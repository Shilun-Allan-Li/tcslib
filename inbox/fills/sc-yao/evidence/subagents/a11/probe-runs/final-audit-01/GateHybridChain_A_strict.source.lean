/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateStepCases
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SliceReduction
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (false && coe && projection)
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
# Summing present-argument bounds along the gate hybrid

The selected-step security result bounds only actual arguments. Missing argument positions
leave the stage labels unchanged. This consumer combines that structural dichotomy with
the existing polynomial-chain theorem, uniformly over the same arbitrary input family.

## Main definitions

None.

## Main results

* `endpoint_negligible`: a uniform negligible selected-step bound gives one negligible
  endpoint bound for a polynomial-size family of two-step-per-gate hybrids.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (the gate hybrid and polynomial summation).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain

open Complexity BoolCircuit TCSlib.Cryptography

/-- Suppose a fan-in-two circuit family has size at most `S(n)`, consistent wire values,
and a sampler `H` whose stage labels determine its value. If every substep at an actual
argument has advantage at most one nonnegative negligible `μ(n)`, uniformly over `z`,
then the advantage from stage zero to stage `2*gatecount` has one negligible bound,
uniformly over that same family. The input family need not be finite or nonempty.
[PS10, Theorem 163.7]

**Proof sketch.** Twice the gate count is bounded by twice the circuit size and hence
by the polynomial twice `S`. Apply the established negligible-chain theorem with this
envelope. For each step, the proved gate-step dichotomy either identifies the stage-label
maps or names an actual argument at the step's gate. In the first case the sampler
congruence identifies both distributions, so its advantage is zero and the nonnegative
bound applies. In the second case the supplied selected-argument bound applies at the
exact clock index. The existing chain theorem performs the summation and negligible
closure; no probability identity or hybrid summation is re-derived. -/
theorem endpoint_negligible {inputs : ℕ → ℕ} {Z σ : ℕ → Type*}
    [∀ n, Fintype (σ n)] (C : ∀ n, DAGCircuit (inputs n)) (S : PolyExpr)
    (hSize : ∀ n, (C n).size ≤ S.eval n) (v : ∀ n, Z n → ℕ → Bool)
    (hA : ∀ n (i : Fin (C n).gates.length), ((C n).gates[i]).args.length ≤ 2)
    (hConsistent : ∀ n z (i : Fin (C n).gates.length),
      gateOut ((C n).gates[i]) (RelabelGarbling.argValues (C n) (v n z) i) =
        v n z (inputs n + i))
    (H : ∀ n, Z n → ℕ → σ n → List Bool)
    (hSameStage : ∀ n z t t', GateHybrids.stageBit (C n) (v n z) t =
      GateHybrids.stageBit (C n) (v n z) t' → H n z t = H n z t')
    (D : NUPPT) {μ : ℕ → ℝ} (hμ : Negligible μ) (hNonneg : ∀ n, 0 ≤ μ n)
    (hSelected : ∀ n z (i : Fin (C n).gates.length)
      (p : Fin ((C n).gates[i]).args.length), p.val < 2 →
      distAdv (H n z (2 * i.val + p.val)) (H n z (2 * i.val + p.val + 1))
        (D.distinguisherL n) ≤ μ n) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n z,
      distAdv (H n z 0) (H n z (2 * (C n).gates.length)) (D.distinguisherL n) ≤ ε n := by
  have hSteps n : 2 * (C n).gates.length ≤ (PolyExpr.mul (.const 2) S).eval n := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_const]
    have hs := hSize n
    rw [DAGCircuit.size_eq] at hs
    omega
  apply SliceReduction.chain_negligible H D (fun n => 2 * (C n).gates.length)
    (.mul (.const 2) S) hSteps hμ
  intro n z t ht
  rcases GateStepCases.step_cases (C n) (v n z) (hA n) (hConsistent n z) t ht with
    hSame | ⟨i, p, hClock, hp⟩
  · rw [hSameStage n z t (t + 1) hSame, distAdv_def, sub_self, abs_zero]
    exact hNonneg n
  · rw [hClock]
    exact hSelected n z i p hp

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridChain
