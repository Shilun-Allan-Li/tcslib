/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RunWithHost
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate
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
# The generic polynomial-time garbled-evaluation host

The retained input determines a unary key-length word, a decoded gate list and
initial keys. Gate records expose their unary argument lists as second components.
A polynomial-time table selector reads the table at the current vertex. The host
then evaluates every gate by the generic nested-special evaluator.

## Main definitions

* `YaoHybridProof.garbledStep`: append one evaluated key to the encoded value list.

## Main results

* `YaoHybridProof.garbledRunWith_poly`: polynomial time for the complete encoded value list.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and §6.2.3.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing BoolCircuit

/-- On the host word `⟨x, ⟨gateRecord, values⟩⟩`, append the key evaluated with
parameter `N x`, argument list `snd gateRecord` and row table `tableWord w`. -/
noncomputable def garbledStep (E₁ E₂ : List Bool → List Bool)
    (N tableWord : List Bool → List Bool) (w : List Bool) : List Bool :=
  evalGateAppendWord E₁ E₂ (pairEncode (N (pairFstD w))
    (pairEncode (pairSndD (pairFstD (pairSndD w)))
      (pairEncode (pairSndD (pairSndD w)) (tableWord w))))

/-- For every `w`, `garbledStep E₁ E₂ N tableWord w` calls `evalGateAppendWord`
on its selected parameter, argument code, encoded values and selected table. -/
theorem garbledStep_eq (E₁ E₂ : List Bool → List Bool)
    (N tableWord : List Bool → List Bool) (w : List Bool) :
    garbledStep E₁ E₂ N tableWord w =
      evalGateAppendWord E₁ E₂ (pairEncode (N (pairFstD w))
        (pairEncode (pairSndD (pairFstD (pairSndD w)))
          (pairEncode (pairSndD (pairSndD w)) (tableWord w)))) := rfl

/-- If the evaluators, parameter selector and table selector are polynomial-time,
then the generic garbled-evaluation step is polynomial-time. -/
theorem garbledStep_poly {E₁ E₂ N tableWord : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hN : PolyTimeComputable N) (hT : PolyTimeComputable tableWord) :
    PolyTimeComputable (garbledStep E₁ E₂ N tableWord) :=
  (evalGateAppendWord_poly hE₁ hE₂).comp
    ((hN.comp polyTimeComputable_pairFstD).pairEncode
      ((polyTimeComputable_pairSndD.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
          ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).pairEncode hT)))

/-- The complete encoded garbled evaluation is polynomial-time when the parameter,
gate records, initial keys and current-row table selector are polynomial-time.
Gate records must expose their unary argument lists, and `tableWord` must select
`T x |vs|` on every host word. The key width may depend on `x`.
[PS10, Protocol 162.6]

**Proof sketch.** Instantiate the generic traversal with the nested-special gate
step. Polynomial-time parameter, gate and initial-key maps give polynomial bounds
on their output lengths. Thus the gate count and initial key count are polynomial.
Each processed gate adds one key of exactly the parameter width, so the encoded
value list has polynomial length throughout the run. The remaining gate records
are a suffix and never grow. These bounds discharge the traversal's state envelope;
the gate-step correctness theorem discharges its leaf contract. -/
theorem garbledRunWith_poly {E₁ E₂ N tableWord : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hN : PolyTimeComputable N) (gateCode : DAGGate → List Bool)
    (gs : List Bool → List DAGGate)
    (init : ∀ x, List (Fin (N x).length → Bool))
    (T : List Bool → ℕ → List (List Bool))
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => BinArith.encWords ((init x).map List.ofFn))
    (hT : PolyTimeComputable tableWord)
    (hargs : ∀ g, pairSndD (gateCode g) =
      BinArith.encWords (g.args.map fun a => List.replicate a true))
    (htable : ∀ x g (vs : List (Fin (N x).length → Bool)),
      tableWord (pairEncode x
        (pairEncode (gateCode g) (BinArith.encWords (vs.map List.ofFn)))) =
          BinArith.encWords (T x vs.length)) :
    PolyTimeComputable fun x => BinArith.encWords
      ((runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ (N x).length) (T x) vs.length g vs)
        (gs x) (init x)).map List.ofFn) := by
  -- Extract envelopes from the three input-construction contracts.
  obtain ⟨Cg, cg, hCg⟩ := hgs.output_length_le
  obtain ⟨Ci, ci, hCi⟩ := hinit.output_length_le
  obtain ⟨Cn, cn, hCn⟩ := hN.output_length_le
  let G := PolyExpr.normal Cg cg
  let I := PolyExpr.normal Ci ci
  let P := PolyExpr.normal Cn cn
  have hg x : (BinArith.encWords ((gs x).map gateCode)).length ≤ G.eval x.length := by
    simpa only [G, PolyExpr.eval_normal] using hCg x
  have hi x : (BinArith.encWords ((init x).map List.ofFn)).length ≤ I.eval x.length := by
    simpa only [I, PolyExpr.eval_normal] using hCi x
  have hn x : (N x).length ≤ P.eval x.length := by
    simpa only [P, PolyExpr.eval_normal] using hCn x
  have hgl x : (gs x).length ≤ G.eval x.length := by
    have h := BinArith.length_decWords_le (BinArith.encWords ((gs x).map gateCode))
    rw [BinArith.decWords_encWords, List.length_map] at h
    exact h.trans (hg x)
  have hil x : (init x).length ≤ I.eval x.length := by
    have h := BinArith.length_decWords_le (BinArith.encWords ((init x).map List.ofFn))
    rw [BinArith.decWords_encWords, List.length_map] at h
    exact h.trans (hi x)
  let B : PolyExpr := .add (.mul (.const 2) G)
    (.add (.const 2) (.mul (.add I G) (.add (.mul (.const 2) P) (.const 2))))
  refine RunWithHost.polyTimeComputable_runWith gateCode
    (fun _ vs => BinArith.encWords (vs.map List.ofFn)) gs init
    (fun x g vs => evalGate (nestedSpecial E₁ E₂ (N x).length) (T x) vs.length g vs)
    hgs hinit (garbledStep_poly hE₁ hE₂ hN hT) ?_ G B hgl ?_
  · intro x g vs
    rw [garbledStep_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hargs, htable]
    exact evalGateAppendWord_encoded E₁ E₂ (N x) (T x) vs.length g vs
  · intro x i _
    -- Remaining gate records form a suffix of the original encoded list.
    have hdrop := BinArith.length_iterate_pairSndD_le
      (BinArith.encWords ((gs x).map gateCode)) i
    rw [BinArith.iterate_pairSndD_encWords, ← List.map_drop] at hdrop
    have hd := hdrop.trans (hg x)
    -- Every vertex value is one fixed-width key; at most one is added per gate.
    have hv := BinArith.length_encWords_le
      ((runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ (N x).length)
        (T x) vs.length g vs) ((gs x).take i) (init x)).map List.ofFn)
      (N x).length (fun w hw => by
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
        exact (List.length_ofFn).le)
    rw [List.length_map, length_runWith, List.length_take] at hv
    have hc : (init x).length + min i (gs x).length ≤ I.eval x.length + G.eval x.length :=
      Nat.add_le_add (hil x) ((Nat.min_le_right _ _).trans (hgl x))
    have hp : 2 * (N x).length + 2 ≤ 2 * P.eval x.length + 2 := by
      have := hn x
      omega
    have hval := hv.trans (Nat.mul_le_mul hc hp)
    rw [length_pairEncode]
    simp only [B, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
