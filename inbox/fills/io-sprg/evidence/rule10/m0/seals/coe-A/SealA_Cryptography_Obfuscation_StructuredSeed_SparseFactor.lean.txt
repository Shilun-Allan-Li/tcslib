/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Card
/- G06-HARNESS INSTALL SealA_Cryptography_Obfuscation_StructuredSeed_SparseFactor -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealA_Cryptography_Obfuscation_StructuredSeed_SparseFactor"
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
    Lean.logInfo m!"G06-COMPONENT label={label} phase=install spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}"
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
    Lean.logInfo m!"G06-NAME label={label} spelling={spelling} actual={n.toString} home={home} before={repr before} installed={repr installed}"
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
  Lean.logInfo m!"G06-MASK label={label} phase=install requested={requests.size} verified={resolved.size} removed={removed} scope_depth=1 scoped_names={scopedNames.size} tc_state=preserved"
  Lean.logInfo m!"G06-SEAL label={label} requested={requests.size} active={active} already_irreducible={already} verified={verified}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic sparse matrix factorization

## Main definitions

* `sparseEntries` lists nonzero matrix positions in row-major order.
* `sparseFactor` places one nonzero entry in each factor slot, padding unused slots by zero.

## Main results

* `sparseFactor_mul` reconstructs a matrix with at most `t` nonzero entries.
* `sparseFactor_mul_of_card_le` reads the sparsity hypothesis as a finite cardinal bound.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, sampling algorithm 1SdSamp, p. 16.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviation.** The paper uses the existence of factors for a matrix with at most `t`
nonzero entries. We specify the factors deterministically: list positions in row-major
order, put the entry value in its row in a left column, and put one in its column in the
corresponding right row. This works over any semiring and uses no rank theory or
choice-based enumeration. These are raw deterministic functions; efficiency is a later
core-target obligation, not a theorem of this module.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

variable {rows cols : ℕ} {R : Type*} [Semiring R] [DecidableEq R]

/-- Nonzero positions are listed in row-major order,
`sparseEntries M = [(i,j) in Fin rows × Fin cols | M i j ≠ 0]`
[JLS26, sampling algorithm 1SdSamp, p. 16]. The order fixes the paper's unspecified factors;
`List.finRange` avoids a choice-based finite enumeration. -/
def sparseEntries (M : Matrix (Fin rows) (Fin cols) R) : List (Fin rows × Fin cols) :=
  ((List.finRange rows).flatMap (fun i => (List.finRange cols).map (fun j => (i, j)))).filter
    (fun c => decide (M c.1 c.2 ≠ 0))

/-- Sparse positions are the row-major list filtered by nonzero entries. Glue reader. -/
theorem sparseEntries_eq (M : Matrix (Fin rows) (Fin cols) R) :
    sparseEntries M =
      ((List.finRange rows).flatMap (fun i => (List.finRange cols).map (fun j => (i, j)))).filter
        (fun c => decide (M c.1 c.2 ≠ 0)) := rfl

/-- The left factor puts the `k`th nonzero entry in its row in column `k`,
with zero for missing slots [JLS26, sampling algorithm 1SdSamp, p. 16].
The row-major order makes the paper's factor choice deterministic. -/
def sparseLeft (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    Matrix (Fin rows) (Fin t) R :=
  fun i k => match (sparseEntries M)[k.val]? with
    | none => 0
    | some c => if i = c.1 then M c.1 c.2 else 0

/-- The left factor reads a nonzero position by its slot and writes its entry value. Glue reader. -/
theorem sparseLeft_eq (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    sparseLeft M t = fun i k => match (sparseEntries M)[k.val]? with
      | none => 0
      | some c => if i = c.1 then M c.1 c.2 else 0 := rfl

/-- The right factor puts one at the column of the `k`th nonzero entry in row `k`,
with zero for missing slots [JLS26, sampling algorithm 1SdSamp, p. 16].
The row-major order makes the paper's factor choice deterministic. -/
def sparseRight (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    Matrix (Fin t) (Fin cols) R :=
  fun k j => match (sparseEntries M)[k.val]? with
    | none => 0
    | some c => if j = c.2 then 1 else 0

/-- The right factor reads a nonzero position by its slot and selects its column. Glue reader. -/
theorem sparseRight_eq (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    sparseRight M t = fun k j => match (sparseEntries M)[k.val]? with
      | none => 0
      | some c => if j = c.2 then 1 else 0 := rfl

/-- Sparse factors are the deterministic pair `(sparseLeft M t, sparseRight M t)`
[JLS26, sampling algorithm 1SdSamp, p. 16]. No existence witness or rank decomposition
is selected; the raw functions are defined even when the sparsity bound fails. -/
def sparseFactor (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    Matrix (Fin rows) (Fin t) R × Matrix (Fin t) (Fin cols) R :=
  (sparseLeft M t, sparseRight M t)

/-- The sparse-factor pair consists of its explicit left and right factors. Glue reader. -/
theorem sparseFactor_eq (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    sparseFactor M t = (sparseLeft M t, sparseRight M t) := rfl

/-- The first sparse factor is the explicit left matrix. Glue projection reader. -/
theorem sparseFactor_fst (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    (sparseFactor M t).1 = sparseLeft M t := rfl

/-- The second sparse factor is the explicit right matrix. Glue projection reader. -/
theorem sparseFactor_snd (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    (sparseFactor M t).2 = sparseRight M t := rfl

/-- Nonzero positions occur exactly once in the sparse list
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue for the chosen factors.

**Proof sketch.** The row-major list is a product of duplicate-free finite ranges;
filtering preserves duplicate-freeness. -/
theorem sparseEntries_nodup (M : Matrix (Fin rows) (Fin cols) R) :
    (sparseEntries M).Nodup := sorry

/-- A position belongs to the sparse list exactly when its entry is nonzero
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue.

**Proof sketch.** Every finite row and column occurs in `List.finRange`; use the filter test. -/
theorem mem_sparseEntries_iff (M : Matrix (Fin rows) (Fin cols) R)
    (c : Fin rows × Fin cols) : c ∈ sparseEntries M ↔ M c.1 c.2 ≠ 0 := sorry

/-- The sparse list's length equals the number of nonzero matrix positions
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue.

**Proof sketch.** Use duplicate-freeness and `mem_sparseEntries_iff` to identify the finite set. -/
theorem sparseEntries_length_eq_card (M : Matrix (Fin rows) (Fin cols) R) :
    (sparseEntries M).length =
      (Finset.univ.filter (fun c : Fin rows × Fin cols => M c.1 c.2 ≠ 0)).card := sorry

/-- At most `t` nonzero entries suffice for the explicit factors to multiply to the matrix,
`(sparseFactor M t).1 * (sparseFactor M t).2 = M`
[JLS26, sampling algorithm 1SdSamp, p. 16]. This constructive factorization replaces the
paper's rank-existence justification without changing its factors' dimensions.

**Proof sketch.** Expand matrix multiplication. For each slot, the two factors produce
one entry at its unique row and column. Each nonzero entry has exactly one slot by
`sparseEntries_nodup`, and every slot beyond the list length contributes zero. -/
theorem sparseFactor_mul (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ)
    (h : (sparseEntries M).length ≤ t) :
    (sparseFactor M t).1 * (sparseFactor M t).2 = M := sorry

/-- A finite cardinal bound on nonzero entries implies reconstruction by the sparse factors
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue for bucket matrices.

**Proof sketch.** Translate cardinality to sparse-list length, then use `sparseFactor_mul`. -/
theorem sparseFactor_mul_of_card_le (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ)
    (h : (Finset.univ.filter (fun c : Fin rows × Fin cols => M c.1 c.2 ≠ 0)).card ≤ t) :
    (sparseFactor M t).1 * (sparseFactor M t).2 = M := sorry

end TCSlib.Cryptography.Obfuscation.StructuredSeed
/- G06-HARNESS EOF-VERIFY SealA_Cryptography_Obfuscation_StructuredSeed_SparseFactor -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealA_Cryptography_Obfuscation_StructuredSeed_SparseFactor"
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
    Lean.logInfo m!"G06-COMPONENT label={label} phase=eof spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}"
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed at EOF for {spelling}"
    if Lean.Meta.isGlobalInstance env n then
      throwError "G06-HARNESS {label}: unfolding membership at EOF for {spelling}"
    verified := verified + 1
  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"
  Lean.logInfo m!"G06-MASK label={label} phase=eof requested={requests.size} verified={verified}"
  Lean.logInfo m!"G06-SEAL-END label={label} requested={requests.size} verified={verified}"

