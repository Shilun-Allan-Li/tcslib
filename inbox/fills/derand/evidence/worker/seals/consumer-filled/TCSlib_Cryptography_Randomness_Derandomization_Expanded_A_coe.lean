/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Stretch
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "consumer-filled_TCSlib_Cryptography_Randomness_Derandomization_Expanded_A_coe"
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
# Expanding a PRG to cover the verifier's coins

The polynomial stretch `a(s^d+1)^k+s+1` exceeds the seed length even at zero.
At the ceiling-root schedule it covers `a(n+1)^k` true random bits.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.exists_secure_cover`: a secure
  generator with an FP evaluator and the required output-length envelope.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Lemma 80.5 and Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Complexity

/-- A secure PRG can cover every polynomial coin schedule at the integer-root
seed length: there are a secure `G` and an FP evaluator `F` such that
`F(ofFn s) = ofFn(G n s)` and
`polyLen a k n ≤ G.stretch.eval (ceilRoot d n)` for every `n`.
[PS10, Lemma 80.5 and Theorem 180.1]

**Proof sketch.** Truncate the given generator to one-bit stretch and use
`prg_expand` at the syntactic polynomial `a(s^d+1)^k+s+1`. The last two terms
make its expansion clause strict at every seed length. Extract the existing
FP evaluator through `PRG.secure_iff` and `PRG.easy_iff`. Finally
`n ≤ (ceilRoot d n)^d` gives the verifier's length bound by monotonicity of
fixed natural powers and multiplication. -/
theorem exists_secure_cover (hPRG : ∃ G : PRG, G.Secure) (a k d : ℕ) (hd : 0 < d) :
    ∃ (G : PRG) (F : List Bool → List Bool),
      G.Secure ∧ PolyTimeComputable F ∧
      (∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G.G n s)) ∧
      ∀ n, Randomized.polyLen a k n ≤ G.stretch.eval (ceilRoot d n) := by
  obtain ⟨G₀, hG₀⟩ := hPRG
  let p : PolyExpr := .add (.add
    (.mul (.const a) (.pow (.add (.pow .var d) (.const 1)) k)) .var) (.const 1)
  have hp (s : ℕ) : s < p.eval s := by
    simp only [p, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_pow, PolyExpr.eval_var]
    omega
  let G := PRG.expand G₀.truncate p hp
  have hG : G.Secure := prg_expand G₀.truncate p hp hG₀.truncate
  obtain ⟨F, hF, hFs⟩ := (PRG.easy_iff G).mp ((PRG.secure_iff G).mp hG).1
  refine ⟨G, F, hG, hF, hFs, fun n => ?_⟩
  rw [show G.stretch = p from PRG.expand_stretch G₀.truncate p hp]
  simp only [p, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_pow, PolyExpr.eval_var, Randomized.polyLen_eq]
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (le_ceilRoot_pow hd n) 1) k
  have hmul := Nat.mul_le_mul_left a hpow
  omega

end TCSlib.Cryptography.Randomness.Derand


run_cmd do
  let label := "consumer-filled_TCSlib_Cryptography_Randomness_Derandomization_Expanded_A_coe"
  Lean.logInfo m!"DERAND-EOF {label}"
