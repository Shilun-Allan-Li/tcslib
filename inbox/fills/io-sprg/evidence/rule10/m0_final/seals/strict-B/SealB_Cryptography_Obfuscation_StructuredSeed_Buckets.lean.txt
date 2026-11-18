/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic
/- G06-HARNESS INSTALL SealB_Cryptography_Obfuscation_StructuredSeed_Buckets -/ /- io-sprg: success transport=IO.println/MessageData.toString; guards unchanged -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealB_Cryptography_Obfuscation_StructuredSeed_Buckets"
  let payload : String := ""
  let expectedRequests : Nat := 0
  let mut requests : Array (String × String) := #[]
  let payloadLines := if payload.isEmpty then [] else payload.splitOn "\n"
  for line in payloadLines do
    match line.splitOn "\t" with
    | [spelling, home] =>
      unless !spelling.isEmpty && !home.isEmpty do throwError "G06-HARNESS {label}: empty request field"
      requests := requests.push (spelling, home)
    | _ => throwError "G06-HARNESS {label}: malformed serialized request row"
  unless requests.size == expectedRequests do throwError "G06-HARNESS {label}: serialized request count differs: {requests.size} vs {expectedRequests}"
  let rec nameParts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => nameParts p ++ [("str", s)]
    | .num p n => nameParts p ++ [("num", toString n)]
  let nameKey (n : Lean.Name) : String := (Lean.toJson (nameParts n)).compress
  let componentPayload : String := ""
  let mut components : Std.HashMap String (String × String × String × String × String) := {}
  for line in (if componentPayload.isEmpty then [] else componentPayload.splitOn "\n") do
    match line.splitOn "\t" with
    | [n, nk, hk, i, m, a] =>
      if (components[n]?).isSome then throwError "G06-HARNESS {label}: duplicate component request"
      components := components.insert n (nk, hk, i, m, a)
    | _ => throwError "G06-HARNESS {label}: malformed component request"
  unless components.size == requests.size do throwError "G06-HARNESS {label}: component count differs"
  let env ← Lean.getEnv
  let mut resolved : Array Lean.Name := #[]
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut verified : Nat := 0
  let mut active : Nat := 0
  let mut already : Nat := 0
  for (n, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for (spelling, expectedHome) in requests do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "G06-HARNESS {label}: absent/ambiguous imported name {spelling}; candidates={ns.size}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "G06-HARNESS {label}: no home for {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "G06-HARNESS {label}: home differs for {spelling}: {home}"
    let some ci := env.find? n | throwError "G06-HARNESS {label}: no constant for {spelling}"
    unless ci.isDefinition do throwError "G06-HARNESS {label}: requested nondefinition {spelling}"
    let some (nk, hk, ei, em, ea) := components[spelling]?
      | throwError "G06-HARNESS {label}: missing component request"
    unless nameKey n == nk && nameKey home == hk do
      throwError "G06-HARNESS {label}: actual Name components differ"
    let instanceFlag := Lean.Meta.isInstanceCore env n
    let matcherFlag := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    unless toString instanceFlag == ei && toString matcherFlag == em && toString abbrevFlag == ea do
      throwError "G06-HARNESS {label}: definition/instance metadata differs"
    IO.println (← (m!"G06-COMPONENT label={label} phase=install spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}").toString)
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if before == .irreducible then
      already := already + 1
    else
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed for {spelling}"
    resolved := resolved.push n
    verified := verified + 1
    IO.println (← (m!"G06-NAME label={label} spelling={spelling} actual={n.toString} home={home} before={repr before} installed={repr installed}").toString)
  unless active + already == requests.size do throwError "G06-HARNESS {label}: installation count mismatch"
  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do
    throwError "G06-HARNESS {label}: unfolding mask requires base scope"
  let mut scopedNames : Std.HashSet Lean.Name := {}
  for (_, payloads) in scopes.scopedEntries.map.toList do
    for n in payloads do
      scopedNames := scopedNames.insert n
  let mut removed : Nat := 0
  for n in resolved do
    if scopedNames.contains n then
      throwError "G06-HARNESS {label}: scoped unfolding payload intersects request {n}"
    if Lean.Meta.isGlobalInstance maskEnv n then
      removed := removed + 1
  -- InstanceEntry's BEq checks only val, so compare every field explicitly.
  let entryFields (e : Lean.Meta.InstanceEntry) :=
    (e.keys, Lean.ExprStructEq.mk e.val, e.priority, e.globalName?, e.synthOrder, e.attrKind)
  let lookupSnapshot (e : Lean.Environment) :=
    let s := Lean.Meta.instanceExtension.getState e
    (s.discrTree.toArray.map (fun (ks, entry) => (ks, entryFields entry)),
      s.instanceNames.toArray.map (fun (n, entry) => (n, entryFields entry)), s.erased.toList)
  let beforeLookup := lookupSnapshot env
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      resolved.foldl (fun s n => s.erase n) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "G06-HARNESS {label}: typeclass lookup state changed"
  for n in resolved do
    if Lean.Meta.isGlobalInstance maskedEnv n then
      throwError "G06-HARNESS {label}: unfolding membership after mask for {n}"
  IO.println (← (m!"G06-MASK label={label} phase=install requested={requests.size} verified={resolved.size} removed={removed} scope_depth=1 scoped_names={scopedNames.size} tc_state=preserved").toString)
  IO.println (← (m!"G06-SEAL label={label} requested={requests.size} active={active} already_irreducible={already} verified={verified}").toString)


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bucket placement and correction matrices

## Main definitions

* `Buckets.indexMap` assigns distinct grid positions within a non-overfull bucket.
* `Buckets.bucketMatrix` places a correction vector at its assigned grid positions.

## Main results

* Non-overfull buckets have defined, injective grid positions.
* A correction matrix has at most as many nonzero entries as bad outputs in its bucket.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, construction on pp. 15-16.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviation.** The paper chooses arbitrary injective positions and an overfull constant.
We use increasing ranks and an explicit `finProdFinEquiv`. Positions are optional, with
`none` in the overfull case. This preserves the capacity convention when the grid is
empty at security parameter zero; a total point of an empty grid cannot be supplied.
Every good bucket still uses exactly the required grid, without padding its capacity.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets

open scoped BigOperators

variable {R : Type*}

section Positions

variable {m B : ℕ}

/-- A bucket is the finite fiber `bucket φ b = {j | φ j = b}`
[JLS26, construction of IdSamp', p. 15]. Indices start at zero. -/
def bucket (φ : Fin m → Fin B) (b : Fin B) : Finset (Fin m) :=
  Finset.univ.filter (fun j => φ j = b)

/-- A bucket equals the finite fiber of its label. Glue reader. -/
theorem bucket_eq (φ : Fin m → Fin B) (b : Fin B) :
    bucket φ b = Finset.univ.filter (fun j => φ j = b) := rfl

/-- A bucket's load is its cardinality, `load φ b = (bucket φ b).card`
[JLS26, construction of IdSamp', p. 15]. -/
def load (φ : Fin m → Fin B) (b : Fin B) : ℕ := (bucket φ b).card

/-- A bucket's load equals its cardinality. Glue reader. -/
theorem load_eq (φ : Fin m → Fin B) (b : Fin B) : load φ b = (bucket φ b).card := rfl

/-- A placement is overfull if some load exceeds capacity,
`overfull φ cap ↔ ∃ b, cap < load φ b` [JLS26, construction of IdSamp', p. 15]. -/
def overfull (φ : Fin m → Fin B) (cap : ℕ) : Prop := ∃ b, cap < load φ b

/-- A placement is overfull exactly when some bucket exceeds capacity. Glue reader. -/
theorem overfull_iff (φ : Fin m → Fin B) (cap : ℕ) :
    overfull φ cap ↔ ∃ b, cap < load φ b := Iff.rfl

/-- An output's bucket rank counts earlier outputs with the same label,
`rank φ j = #{i | i < j ∧ φ i = φ j}` [JLS26, construction of IdSamp', p. 15].
Increasing ranks make the paper's permitted injection deterministic. -/
def rank (φ : Fin m → Fin B) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun i => i < j ∧ φ i = φ j)).card

/-- The bucket rank counts preceding elements in the same fiber. Glue reader. -/
theorem rank_eq (φ : Fin m → Fin B) (j : Fin m) :
    rank φ j = (Finset.univ.filter (fun i => i < j ∧ φ i = φ j)).card := rfl

/-- Grid positions split increasing bucket ranks using `finProdFinEquiv.symm`
[JLS26, construction of IdSamp', p. 15]. The overfull case returns `none`, including
empty grids, instead of the paper's constant point; no successful case is changed. -/
def indexMap (φ : Fin m → Fin B) (rc : ℕ) (j : Fin m) : Option (Fin rc × Fin rc) :=
  if h : ¬ (∃ b : Fin B, rc * rc < load φ b) ∧ rank φ j < rc * rc then
    some (finProdFinEquiv.symm ⟨rank φ j, h.2⟩)
  else none

/-- Grid positions are optional split ranks, with `none` on overfull placements. Glue reader. -/
theorem indexMap_eq (φ : Fin m → Fin B) (rc : ℕ) (j : Fin m) :
    indexMap φ rc j =
      if h : ¬ (∃ b : Fin B, rc * rc < load φ b) ∧ rank φ j < rc * rc then
        some (finProdFinEquiv.symm ⟨rank φ j, h.2⟩)
      else none := rfl

/-- Each element's rank is strictly below its bucket's load [JLS26, construction, p. 15].
This is mathematical glue for the deterministic placement.

**Proof sketch.** Earlier elements form a strict subset of the fiber because it contains `j`. -/
theorem rank_lt_load (φ : Fin m → Fin B) (j : Fin m) : rank φ j < load φ (φ j) := sorry

/-- Equal ranks in the same bucket identify an output [JLS26, construction, p. 15].
This is mathematical glue for the deterministic placement.

**Proof sketch.** If one index precedes the other, inclusion of the earlier index makes
its rank strictly smaller; rule out both strict inequalities. -/
theorem eq_of_rank_eq (φ : Fin m → Fin B) {i j : Fin m}
    (hφ : φ i = φ j) (hr : rank φ i = rank φ j) : i = j := sorry

/-- Non-overfull placements assign a grid point to every output [JLS26, construction, p. 15].
The optional representation changes no good-case position.

**Proof sketch.** Use `rank_lt_load` and the capacity bound to prove the dependent test. -/
theorem indexMap_some_of_not_overfull (φ : Fin m → Fin B) (rc : ℕ)
    (h : ¬ overfull φ (rc * rc)) (j : Fin m) :
    ∃ c : Fin rc × Fin rc, indexMap φ rc j = some c := sorry

/-- Overfull placements have no grid positions [JLS26, construction, p. 15].
This replaces the paper's unused overfull default by `none` to allow empty grids.

**Proof sketch.** The defining test has a false first conjunct. -/
theorem indexMap_none_of_overfull (φ : Fin m → Fin B) (rc : ℕ)
    (h : overfull φ (rc * rc)) (j : Fin m) : indexMap φ rc j = none := sorry

/-- Non-overfull bucket positions are injective within each bucket
[JLS26, construction of IdSamp', p. 15]. Increasing ranks fix the permitted injection.

**Proof sketch.** Both positions are `some`; apply the explicit product equivalence,
then use `eq_of_rank_eq` in the common bucket. -/
theorem indexMap_injective_on_bucket (φ : Fin m → Fin B) (rc : ℕ)
    (h : ¬ overfull φ (rc * rc)) {i j : Fin m} (hφ : φ i = φ j)
    (hc : indexMap φ rc i = indexMap φ rc j) : i = j := sorry

end Positions

section Matrices

variable {m B : ℕ} [AddCommMonoid R]

/-- A bucket correction matrix sums corrections at matching grid positions,
`M_b(u,v) = ∑ j, [φ j = b ∧ indexMap j = some (u,v)] corr j`
[JLS26, sampling algorithm 1SdSamp, p. 16]. Increasing ranks fix the paper's positions;
`none` contributes nothing, so the empty-grid boundary is total. -/
def bucketMatrix (φ : Fin m → Fin B) (rc : ℕ) (corr : Fin m → R) (b : Fin B) :
    Matrix (Fin rc) (Fin rc) R :=
  fun u v => ∑ j : Fin m,
    if φ j = b ∧ indexMap φ rc j = some (u, v) then corr j else 0

/-- Bucket matrix entries equal the finite sum of corrections assigned to them. Glue reader. -/
theorem bucketMatrix_eq (φ : Fin m → Fin B) (rc : ℕ) (corr : Fin m → R) (b : Fin B) :
    bucketMatrix φ rc corr b = fun u v => ∑ j : Fin m,
      if φ j = b ∧ indexMap φ rc j = some (u, v) then corr j else 0 := rfl

/-- A non-overfull bucket matrix contains each correction at its assigned position
[JLS26, sampling algorithm 1SdSamp, p. 16]. The deterministic positions are injective.

**Proof sketch.** Expand the entry through its reader, retain the summand `j`, and
remove every other summand by injectivity within the bucket. -/
theorem bucketMatrix_apply_indexMap (φ : Fin m → Fin B) (rc : ℕ)
    (corr : Fin m → R) (h : ¬ overfull φ (rc * rc)) (j : Fin m)
    (c : Fin rc × Fin rc) (hc : indexMap φ rc j = some c) :
    bucketMatrix φ rc corr (φ j) c.1 c.2 = corr j := sorry

/-- A correction matrix has at most as many nonzero entries as supported outputs in its bucket
[JLS26, sampling algorithm 1SdSamp, p. 16]. The finite cardinal bound avoids rank theory.

**Proof sketch.** Every nonzero matrix entry receives a nonzero supported correction;
the image of those supported outputs contains the matrix support. -/
theorem bucketMatrix_nonzero_card_le [DecidableEq R] (φ : Fin m → Fin B) (rc : ℕ)
    (corr : Fin m → R) (bad : Finset (Fin m)) (hcorr : ∀ j, j ∉ bad → corr j = 0)
    (b : Fin B) :
    (Finset.univ.filter (fun c : Fin rc × Fin rc =>
      bucketMatrix φ rc corr b c.1 c.2 ≠ 0)).card ≤ (bucket φ b ∩ bad).card := sorry

end Matrices

end TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets
/- G06-HARNESS EOF-VERIFY SealB_Cryptography_Obfuscation_StructuredSeed_Buckets -/ /- io-sprg: success transport=IO.println/MessageData.toString; guards unchanged -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealB_Cryptography_Obfuscation_StructuredSeed_Buckets"
  let payload : String := ""
  let expectedRequests : Nat := 0
  let mut requests : Array (String × String) := #[]
  let payloadLines := if payload.isEmpty then [] else payload.splitOn "\n"
  for line in payloadLines do
    match line.splitOn "\t" with
    | [spelling, home] =>
      unless !spelling.isEmpty && !home.isEmpty do throwError "G06-HARNESS {label}: empty request field"
      requests := requests.push (spelling, home)
    | _ => throwError "G06-HARNESS {label}: malformed serialized request row"
  unless requests.size == expectedRequests do throwError "G06-HARNESS {label}: serialized request count differs: {requests.size} vs {expectedRequests}"
  let rec nameParts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => nameParts p ++ [("str", s)]
    | .num p n => nameParts p ++ [("num", toString n)]
  let nameKey (n : Lean.Name) : String := (Lean.toJson (nameParts n)).compress
  let componentPayload : String := ""
  let mut components : Std.HashMap String (String × String × String × String × String) := {}
  for line in (if componentPayload.isEmpty then [] else componentPayload.splitOn "\n") do
    match line.splitOn "\t" with
    | [n, nk, hk, i, m, a] =>
      if (components[n]?).isSome then throwError "G06-HARNESS {label}: duplicate component request"
      components := components.insert n (nk, hk, i, m, a)
    | _ => throwError "G06-HARNESS {label}: malformed component request"
  unless components.size == requests.size do throwError "G06-HARNESS {label}: component count differs"
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut verified : Nat := 0
  for (n, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for (spelling, expectedHome) in requests do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "G06-HARNESS {label}: absent/ambiguous imported name {spelling}; candidates={ns.size}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "G06-HARNESS {label}: no home for {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "G06-HARNESS {label}: home differs for {spelling}: {home}"
    let some ci := env.find? n | throwError "G06-HARNESS {label}: no constant for {spelling}"
    unless ci.isDefinition do throwError "G06-HARNESS {label}: requested nondefinition {spelling}"
    let some (nk, hk, ei, em, ea) := components[spelling]?
      | throwError "G06-HARNESS {label}: missing component request"
    unless nameKey n == nk && nameKey home == hk do
      throwError "G06-HARNESS {label}: actual Name components differ"
    let instanceFlag := Lean.Meta.isInstanceCore env n
    let matcherFlag := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    unless toString instanceFlag == ei && toString matcherFlag == em && toString abbrevFlag == ea do
      throwError "G06-HARNESS {label}: definition/instance metadata differs"
    IO.println (← (m!"G06-COMPONENT label={label} phase=eof spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}").toString)
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed at EOF for {spelling}"
    if Lean.Meta.isGlobalInstance env n then
      throwError "G06-HARNESS {label}: unfolding membership at EOF for {spelling}"
    verified := verified + 1
  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"
  IO.println (← (m!"G06-MASK label={label} phase=eof requested={requests.size} verified={verified}").toString)
  IO.println (← (m!"G06-SEAL-END label={label} requested={requests.size} verified={verified}").toString)

