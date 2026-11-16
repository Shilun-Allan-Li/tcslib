/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedStepSecurity
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridChain
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joint slice security for the complete actual gate hybrid

The selected-step theorem already supplies one negligible bound uniform over every finite
input option and every actual argument. The chain consumer handles the unchanged missing
positions. This module composes those public contracts on the actual uniform-tape sampler.

## Main definitions

None.

## Main results

* `endpoint_negligible`: joint slice security gives one negligible actual-sample endpoint
  bound, for each fixed distinguisher and uniformly over the finite input family.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (the complete inactive-key gate hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridSecurity

open Complexity Turing BoolCircuit TCSlib.Cryptography

variable {I : ℕ → Type} [∀ n, Fintype (I n)] {inputs : ℕ → ℕ}
  (C : ∀ n, DAGCircuit (inputs n)) (S A B O R : PolyExpr)
  (seed : ∀ n, List Bool →
    GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : ∀ n, I n → ℕ → Bool) (output : ∀ n, Fin (O.eval n) → ℕ)
  (bobWord aliceWord : ∀ n, I n → List Bool)
  (hSize : ∀ n, (C n).size ≤ S.eval n) (hfanin : ∀ n, (C n).IsFaninTwo)
  (hEval : ∀ n z (i : Fin (C n).gates.length),
    gateOut ((C n).gates[i]) (RelabelGarbling.argValues (C n) (v n z) i) =
      v n z (inputs n + i))
  (hsink : ∀ n j g, g ∈ (C n).gates → output n j ∉ g.args)
  (hBob : ∀ n z, (bobWord n z).length ≤ B.eval n)
  (hAlice : ∀ n z, (aliceWord n z).length ≤ R.eval n)
  {L : PolyExpr} {L₂ : ℕ → ℕ}
  (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L.eval n) → Bool))
  (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool))
  (E₁ E₂ : List Bool → List Bool) (hE₂ : PolyTimeComputable E₂)
  (hG : ∀ n (s x : Fin n → Bool),
    List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))
  (hL : ∀ n, 7 * n + 2 ≤ L.eval n) (hSecure : SliceMultiMessageSecure G)

variable
  (hK : ∀ n q (w : Fin (C n).size) (b : Bool) (t : Fin n),
    (seed n q).1 w b t = q.getD ((b.toNat * S.eval n + w.val) * n + t.val) false)
  (hR₀ : ∀ n q (i : Fin (C n).gates.length)
      (a : Fin (C n).gates[i.val].args.length → Bool) (t : Fin n),
    ((seed n q).2.1 i a).1 t = q.getD (2 * S.eval n * n + (4 * i.val +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t.val) false)
  (hR₁ : ∀ n q (i : Fin (C n).gates.length)
      (a : Fin (C n).gates[i.val].args.length → Bool) (t : Fin n),
    ((seed n q).2.1 i a).2 t = q.getD (2 * S.eval n * n + (4 * i.val +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t.val) false)
  (hP : ∀ n q (i : Fin (C n).gates.length)
      (a : Fin (C n).gates[i.val].args.length → Bool)
      (t : Fin (C n).gates[i.val].args.length),
    (seed n q).2.2 i a t = xor (a t)
      (q.getD (10 * S.eval n * n + 2 * i.val + t.val) false))

include hSize hfanin hEval hsink hBob hAlice hE₂ hG hGE₁ hGE₂ hL hSecure
  hK hR₀ hR₁ hP

/-- For the supplied polynomial-size fan-in-two circuit family, addressed seed and
consistent values, joint slice security gives one negligible bound on the actual encoded
sample's advantage from stage zero to stage `2*gatecount`, uniformly over every input
option. The simulator sample is the existing `GateHybridMessage.sample`, including the
prescribed receiver word and outer sender output. [PS10, Theorem 163.7]

**Proof sketch.** Apply the established selected-step theorem to the actual uniform tape.
It returns a nonnegative negligible bound uniform over all inputs, gates and present
arguments. Instantiate the generic chain consumer with the actual encoded sample family.
The published fan-in reader supplies arity at most two. Equality of stage-label families
passes through the public complete-sample congruence, pointwise on the tape. Finally feed
the selected-step bound to the chain consumer, ignoring its redundant first-two-position
premise. The chain theorem already handles absent arguments and polynomial summation;
no reduction, probability law or sampler definition is reproduced. -/
theorem endpoint_negligible (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (z : I n),
      distAdv
        (fun r : SelectedStepChoices.Tape S n =>
          GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn r))
            (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
            (bobWord n z) [] (aliceWord n z) 0)
        (fun r : SelectedStepChoices.Tape S n =>
          GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn r))
            (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
            (bobWord n z) [] (aliceWord n z) (2 * (C n).gates.length))
        (D.distinguisherL n) ≤ ε n := by
  obtain ⟨μ, hμ, hNonneg, hSelected⟩ := SelectedStepSecurity.selected_negligible
    C S A B O R seed v output bobWord aliceWord hSize hfanin hEval hsink hBob hAlice
    G G₁ G₂ E₁ E₂ hE₂ hG hGE₁ hGE₂ hL hSecure hK hR₀ hR₁ hP D
  let H := fun n (z : I n) stage (r : SelectedStepChoices.Tape S n) =>
    GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn r))
      (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
      (bobWord n z) [] (aliceWord n z) stage
  have hA n (i : Fin (C n).gates.length) :=
    ((DAGCircuit.isFaninTwo_iff (C n)).mp (hfanin n)).2 _ (List.getElem_mem i.isLt)
  apply GateHybridChain.endpoint_negligible C S hSize v hA hEval H _ D hμ hNonneg
    (fun n z i p _ => hSelected n z i p)
  intro n z t t' h
  funext r
  exact SelectedFields.sample_eq_of_stageBit_eq (nestedSpecial E₁ E₂ n) (C n)
    (seed n (List.ofFn r)) (A.eval n) (B.eval n) (O.eval n) (output n) (v n z)
    (List.replicate n true) (bobWord n z) [] (aliceWord n z) t t' h

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridSecurity
