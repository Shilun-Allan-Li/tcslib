/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Finite
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "host-final_TCSlib_Complexity_Randomized_SeedMajority_Envelope_B_coe"
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
# A timed computation bounds every work head

The coarse head envelope follows from a completed computation: before its
time bound every head is within that many cells of its initial position;
afterward the halted run is constant. This is the native-initial-configuration
version of the clean-module envelope, stated without a clean seam hypothesis.

## Main results

* `Complexity.SeedMajority.envelope_of_computesInTime`: the all-times head bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §1.2, multitape machines.
-/

namespace Complexity.SeedMajority

open Turing

/-- A finite machine computing `y` on `x` by time `t` keeps each work head
within `t` cells at every time `v`:
`|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ)`.
[AB09, §1.2]

**Proof sketch.** The published interval bound puts the head within `u`
cells of its start after `u ≤ t` steps, and `Cfg.init_workTapePos` makes the
start zero. For `v > t`, the computation reader says the configuration at
`t` is halted; split the run there and use `runFrom_of_halt`. -/
theorem envelope_of_computesInTime {M : FinTM Bool} {x y : List Bool} {t : ℕ}
    (h : M.ComputesInTime x y t) (v : ℕ) (j : Fin M.k) :
    |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ) := by
  have bound (u : ℕ) (hu : u ≤ t) :
      |(M.tm.runFrom (M.tm.initCfg x) u).workTapePos j| ≤ (t : ℤ) := by
    have hp := M.tm.workTapePos_runFrom_mem_Icc (M.tm.initCfg x) u j
    rw [Finset.mem_Icc] at hp
    simp only [MultiTapeTM.initCfg_eq, Cfg.init_workTapePos, zero_sub, zero_add] at hp
    have hut : (u : ℤ) ≤ t := by exact_mod_cast hu
    rw [MultiTapeTM.initCfg_eq]
    exact abs_le.mpr ⟨by omega, by omega⟩
  by_cases hv : v ≤ t
  · exact bound v hv
  · have hh := ((FinTM.computesInTime_iff M x y t).mp h).1
    have heq : M.tm.runFrom (M.tm.initCfg x) v = M.tm.runFrom (M.tm.initCfg x) t := by
      rw [show v = t + (v - t) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ hh]
    rw [heq]
    exact bound t le_rfl

end Complexity.SeedMajority


run_cmd do
  let label := "host-final_TCSlib_Complexity_Randomized_SeedMajority_Envelope_B_coe"
  Lean.logInfo m!"DERAND-EOF {label}"
