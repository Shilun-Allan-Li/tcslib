/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import TCSlib.Complexity.Randomized.Repetition
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "doc-final_TCSlib_Cryptography_Randomness_Derandomization_RootSchedule_A_coe"
  let includeEval := false
  let projectionCoes := true
  let rec parts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => parts p ++ [("str", s)]
    | .num p n => parts p ++ [("num", toString n)]
  let rec isProjectionBody (e : Lean.Expr) : Bool :=
    match e.consumeMData with
    | .lam _ _ body _ => isProjectionBody body
    | value => match value.getAppFn with
      | .const n _ => env.isProjectionFn n
      | _ => false
  let rec stripLambdas (e : Lean.Expr) : Lean.Expr :=
    match e.consumeMData with
    | .lam _ _ body _ => stripLambdas body
    | value => value
  let mut requested : Array Lean.Name := #[]
  let mut excluded : Nat := 0
  for (name, ci) in env.constants.toList.toArray.qsort (fun a b => Lean.Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let home := env.header.moduleNames[idx.toNat]!
    unless home.getRoot == `TCSlib && ci.isDefinition do continue
    let status := Lean.getReducibilityStatusCore env name
    let matcher := Lean.Meta.isMatcherCore env name
    let instanceFlag := Lean.Meta.isInstanceCore env name
    let coeProjection := match ci with
      | .defnInfo d =>
        let value := stripLambdas d.value
        match value.getAppFn with
        | .const n _ =>
          (n == `CoeFun.mk || n == `Coe.mk) &&
            value.getAppArgs.back?.any isProjectionBody
        | _ => false
      | _ => false
    let eligible := (status != .reducible || matcher) &&
      (includeEval || name != `Complexity.PolyExpr.eval) &&
      !(projectionCoes && instanceFlag && coeProjection)
    let row := Lean.Json.mkObj [
      ("name", Lean.toJson name.toString), ("components", Lean.toJson (parts name)),
      ("home", Lean.toJson home.toString), ("home_components", Lean.toJson (parts home)),
      ("status", Lean.toJson status.toAttrString), ("matcher", Lean.toJson matcher),
      ("instance", Lean.toJson instanceFlag), ("projection_coercion", Lean.toJson coeProjection),
      ("eligible", Lean.toJson eligible)]
    Lean.logInfo m!"DERAND-CATALOG {label} {row.compress}"
    if eligible then requested := requested.push name else excluded := excluded + 1
  let mut active : Nat := 0
  let mut already : Nat := 0
  for name in requested do
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    if before == .irreducible then already := already + 1
    else
      let id := Lean.mkIdent name
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    unless installed == .irreducible do throwError "DERAND seal installation failed: {name}"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do throwError "DERAND seal requires base scope"
  let mut scopedNames : Std.HashSet Lean.Name := {}
  for (_, payloads) in scopes.scopedEntries.map.toList do
    for name in payloads do scopedNames := scopedNames.insert name
  let entryFields (entry : Lean.Meta.InstanceEntry) :=
    (entry.keys, Lean.ExprStructEq.mk entry.val, entry.priority, entry.globalName?,
      entry.synthOrder, entry.attrKind)
  let lookupSnapshot (environment : Lean.Environment) :=
    let state := Lean.Meta.instanceExtension.getState environment
    (state.discrTree.toArray.map (fun (keys, entry) => (keys, entryFields entry)),
      state.instanceNames.toArray.map (fun (name, entry) => (name, entryFields entry)),
      state.erased.toList)
  let beforeLookup := lookupSnapshot env
  for name in requested do
    if scopedNames.contains name then throwError "DERAND scoped instance overlap: {name}"
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      requested.foldl (fun state name => state.erase name) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "DERAND typeclass lookup changed"
  for name in requested do
    if Lean.Meta.isGlobalInstance maskedEnv name then
      throwError "DERAND instance unfolding mask failed: {name}"
  Lean.logInfo m!"DERAND-INSTALL {label} requested={requested.size} active={active} already={already} excluded={excluded} tc_state=preserved"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# An integer-root seed schedule

The schedule in the proof of [PS10, Theorem 180.1] is the least natural `t` with
`n ≤ t ^ d`. It uses the existing natural `nthRoot`; its unary implementation
searches through `0, …, n` with integer length comparisons and fixed powers.

## Main definitions

* `TCSlib.Cryptography.Randomness.Derand.ceilRoot`: a ceiling root, defined over naturals.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff`: its least-root property.
* `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_real`: the real-root upper bound.
* `TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot`: its FP unary word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Complexity Turing

/-- The natural ceiling-root schedule is zero at zero and otherwise one more than
the existing floor root of `n - 1`:
`ceilRoot d n = if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1`.
For `0 < d`, this is `min {t | n ≤ t ^ d}`. [PS10, §8.2, Theorem 180.1] -/
def ceilRoot (d n : ℕ) : ℕ := if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1

/-- The ceiling-root schedule satisfies
`ceilRoot d n = if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1`. -/
theorem ceilRoot_eq (d n : ℕ) :
    ceilRoot d n = if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1 := rfl

/-- For `0 < d`, the root is at most `t` exactly when `n ≤ t ^ d`:
`ceilRoot d n ≤ t ↔ n ≤ t ^ d`. [PS10, §8.2, Theorem 180.1] -/
theorem ceilRoot_le_iff {d : ℕ} (hd : 0 < d) (n t : ℕ) :
    ceilRoot d n ≤ t ↔ n ≤ t ^ d := by
  rw [ceilRoot_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    have h := Nat.nthRoot_lt_iff (n := d) (a := n - 1) (b := t) hd.ne'
    omega

/-- For `0 < d`, the scheduled seed length covers the input:
`n ≤ (ceilRoot d n) ^ d`. [PS10, §8.2, Theorem 180.1] -/
theorem le_ceilRoot_pow {d : ℕ} (hd : 0 < d) (n : ℕ) : n ≤ (ceilRoot d n) ^ d :=
  (ceilRoot_le_iff hd n (ceilRoot d n)).mp le_rfl

/-- The zero input has zero seed length: `ceilRoot d 0 = 0`. -/
theorem ceilRoot_zero (d : ℕ) : ceilRoot d 0 = 0 := by
  rw [ceilRoot_eq, if_pos rfl]


/-- The schedule is bounded by the input length:
`ceilRoot d n ≤ n` when `0 < d`. [PS10, §8.2, Theorem 180.1] -/
theorem ceilRoot_le_nat {d : ℕ} (hd : 0 < d) (n : ℕ) : ceilRoot d n ≤ n := by
  apply (ceilRoot_le_iff hd n n).mpr
  by_cases hn : n = 0
  · subst n
    exact Nat.zero_le _
  · calc
      n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ d := Nat.pow_le_pow_right (by omega) hd

/-- The strict lower-bound form of the least-root property is
`t < ceilRoot d n ↔ t ^ d < n` when `0 < d`. -/
theorem lt_ceilRoot_iff {d : ℕ} (hd : 0 < d) (n t : ℕ) :
    t < ceilRoot d n ↔ t ^ d < n := by
  have h := ceilRoot_le_iff hd n t
  omega

/-- The integer schedule is within one of the real root:
`(ceilRoot d n : ℝ) ≤ (n : ℝ) ^ (1 / d) + 1` for `0 < d`.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Handle zero separately. At a positive input the floor root
of `n-1` has `d`th power at most `n`. Cast this bound to the reals, apply
the monotonic inverse-power comparison, and add one on both sides. -/
theorem ceilRoot_le_real {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (ceilRoot d n : ℝ) ≤ (n : ℝ) ^ (1 / (d : ℝ)) + 1 := by
  by_cases hn : n = 0
  · subst n
    rw [ceilRoot_zero]
    simpa only [Nat.cast_zero] using
      add_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) (1 / (d : ℝ)))
        zero_le_one
  · have hpow : ((Nat.nthRoot d (n - 1) : ℕ) : ℝ) ^ d ≤ (n : ℝ) := by
      exact_mod_cast (Nat.pow_nthRoot_le (n := d) (a := n - 1) (Or.inl hd.ne')).trans
        (Nat.sub_le n 1)
    have hr := (Real.le_rpow_inv_iff_of_pos
      (show 0 ≤ ((Nat.nthRoot d (n - 1) : ℕ) : ℝ) from Nat.cast_nonneg _)
      (show 0 ≤ (n : ℝ) from Nat.cast_nonneg _)
      (show 0 < (d : ℝ) by exact_mod_cast hd)).mpr
        (by simpa only [Real.rpow_natCast] using hpow)
    rw [ceilRoot_eq, if_neg hn, Nat.cast_add, Nat.cast_one]
    simpa only [one_div] using add_le_add_right hr 1

/-- The unary ceiling-root word is polynomial-time computable:
`x ↦ 1 ^ (ceilRoot d |x|)` belongs to `FP` for each fixed positive `d`.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Use `polyTimeComputable_stateFind` with the unary counter as
state. Each round appends one token. The test compares `|x|` with the fixed
power of the counter length, using `StateLoop.unaryPoly_comp` and
`StateLoop.lenLe_comp`. The least-root property makes the test false before
`ceilRoot d |x|` and true there. All states up to that round have length at
most `|x|` by `ceilRoot_le_nat`, so both the iteration and state bounds are
the identity polynomial. The output is the counter itself. -/
theorem polyTimeComputable_ceilRoot {d : ℕ} (hd : 0 < d) :
    PolyTimeComputable fun x => List.replicate (ceilRoot d x.length) true := by
  let start : List Bool → List Bool := fun _ => []
  let step : List Bool → List Bool := fun z => pairSndD z ++ [true]
  let acc : List Bool → Bool := fun z =>
    decide ((pairFstD z).length ≤ (pairSndD z).length ^ d)
  have hstart : PolyTimeComputable start := polyTimeComputable_const []
  have hstep : PolyTimeComputable step :=
    polyTimeComputable_pairSndD.append (polyTimeComputable_const [true])
  have hpower : PolyTimeComputable fun z =>
      List.replicate ((pairSndD z).length ^ d) true := by
    simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using
      StateLoop.unaryPoly_comp (.pow .var d) polyTimeComputable_pairSndD
  have hacc : PolyTimeComputable fun z => [acc z] := by
    simpa only [acc, List.length_replicate] using
      StateLoop.lenLe_comp hpower polyTimeComputable_pairFstD
  have horbit (x : List Bool) (i : ℕ) :
      StateLoop.orbit start step x i = List.replicate i true := by
    induction i with
    | zero => rw [StateLoop.orbit_zero]; rfl
    | succ i ih =>
        rw [StateLoop.orbit_succ, ih]
        simp only [step, pairSndD_pairEncode]
        change List.replicate i true ++ List.replicate 1 true = _
        rw [← List.replicate_add]
  have hN (x : List Bool) : ceilRoot d x.length ≤ PolyExpr.var.eval x.length := by
    simpa only [PolyExpr.eval_var] using ceilRoot_le_nat hd x.length
  have hbound (x : List Bool) (i : ℕ) (hi : i ≤ ceilRoot d x.length) :
      (StateLoop.orbit start step x i).length ≤ PolyExpr.var.eval x.length := by
    rw [horbit, List.length_replicate]
    exact hi.trans (hN x)
  have hfirst (x : List Bool) (i : ℕ) (hi : i < ceilRoot d x.length) :
      acc (pairEncode x (StateLoop.orbit start step x i)) = false := by
    simp only [acc, horbit, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, decide_eq_false_iff_not]
    exact Nat.not_le_of_lt ((lt_ceilRoot_iff hd x.length i).mp hi)
  have hlast (x : List Bool) :
      acc (pairEncode x (StateLoop.orbit start step x (ceilRoot d x.length))) = true := by
    simp only [acc, horbit, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, decide_eq_true_eq]
    exact le_ceilRoot_pow hd x.length
  have h := polyTimeComputable_stateFind hstart hstep hacc polyTimeComputable_pairSndD
    .var .var (fun x => ceilRoot d x.length) hN hbound hfirst hlast
  simpa only [horbit, pairSndD_pairEncode] using h

end TCSlib.Cryptography.Randomness.Derand


run_cmd do
  let label := "doc-final_TCSlib_Cryptography_Randomness_Derandomization_RootSchedule_A_coe"
  Lean.logInfo m!"DERAND-EOF {label}"
