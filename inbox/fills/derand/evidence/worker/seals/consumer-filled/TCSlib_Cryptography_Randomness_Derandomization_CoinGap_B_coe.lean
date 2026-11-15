/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
import TCSlib.Cryptography.Randomness.Derandomization.Expanded
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "consumer-filled_TCSlib_Cryptography_Randomness_Derandomization_CoinGap_B_coe"
  let includeEval := true
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
# Replacing a verifier's coins by generated bits

The expanded generator and the non-uniform advice bound give a single FP
evaluator whose acceptance gap is at most `1/12` on every sufficiently long
input. The probability identification reuses the published counting bridge
and uniform prefix projection, including zero coin lengths.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold`: the
  input-length threshold needed by the piecewise verifier.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Complexity Turing

/-- There are an FP generator evaluator `F` and a threshold `n₀` such that,
for every `|x| ≥ n₀`,
`|randProb (ceilRoot d |x|) (M x (F(u)↾m)) - randProb m (M x)| ≤ 1/12`,
where the rational probabilities are cast to `ℝ` and `m = polyLen a k |x|`.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Expand a secure generator to cover the verifier's entire
coin width. Apply the advice-gap theorem to the prefix-truncated verifier,
which stays efficient by `eff_mapCoins` and `polyTimeComputable_pairTakePoly`.
Advice has bound `s^d` because `|x| ≤ (ceilRoot d |x|)^d`. If the seed threshold
is `S`, input lengths from `S^d+1` on have root greater than `S`. Identify the
generated probability with the first advantage term using the evaluator's
typed contract and `randProb_eq_uprob`; identify the uniform term using
`randProb_take`. No new expectation or probability-reindexing identity is used. -/
theorem exists_coin_gap_threshold (hPRG : ∃ G : PRG, G.Secure)
    {M : List Bool → List Bool → Bool}
    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
    (a k d : ℕ) (hd : 0 < d) :
    ∃ (F : List Bool → List Bool) (n₀ : ℕ), PolyTimeComputable F ∧
      ∀ x : List Bool, n₀ ≤ x.length →
        |(Randomized.randProb (ceilRoot d x.length)
            (fun u => M x ((F u).take (Randomized.polyLen a k x.length)) = true) : ℝ) -
          (Randomized.randProb (Randomized.polyLen a k x.length)
            (fun r => M x r = true) : ℝ)| ≤ (1 : ℝ) / 12 := by
  classical
  obtain ⟨G, F, hG, hF, hFs, hcover⟩ := exists_secure_cover hPRG a k d hd
  let M' : List Bool → List Bool → Bool :=
    fun x r => M x (r.take (Randomized.polyLen a k x.length))
  have hM' : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M') := by
    simpa only [pairFstD_pairEncode, pairSndD_pairEncode, eval_polyLenExpr, M'] using
      eff_mapCoins hM (polyTimeComputable_pairTakePoly (polyLenExpr a k))
  have hsize (n : ℕ) : n ≤ (PolyExpr.pow .var d).eval (ceilRoot d n) := by
    simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using le_ceilRoot_pow hd n
  obtain ⟨S, hS⟩ := exists_verifier_gap_bound hM' (ceilRoot d) (.pow .var d) hsize G hG
  refine ⟨F, S ^ d + 1, hF, fun x hx => ?_⟩
  have hs : S ≤ ceilRoot d x.length :=
    ((lt_ceilRoot_iff hd x.length S).mpr (by omega)).le
  have h := hS x hs
  have hgen :
      (Randomized.randProb (ceilRoot d x.length)
        (fun u => M x ((F u).take (Randomized.polyLen a k x.length)) = true) : ℝ) =
        uprob (fun r : Fin (ceilRoot d x.length) → Bool =>
          M' x (List.ofFn (G.G (ceilRoot d x.length) r)) = true) := by
    rw [randProb_eq_uprob]
    congr 1
    funext r
    rw [hFs]
  have huniform :
      uprob (fun r : Fin (G.stretch.eval (ceilRoot d x.length)) → Bool =>
        M' x (List.ofFn r) = true) =
        (Randomized.randProb (Randomized.polyLen a k x.length)
          (fun r => M x r = true) : ℝ) := by
    rw [← randProb_eq_uprob (G.stretch.eval (ceilRoot d x.length))
      (fun r => M' x r = true)]
    exact congrArg (fun q : ℚ => (q : ℝ))
      (Randomized.randProb_take (hcover x.length) (fun r => M x r = true))
  rw [hgen, ← huniform]
  exact h

end TCSlib.Cryptography.Randomness.Derand


run_cmd do
  let label := "consumer-filled_TCSlib_Cryptography_Randomness_Derandomization_CoinGap_B_coe"
  Lean.logInfo m!"DERAND-EOF {label}"
