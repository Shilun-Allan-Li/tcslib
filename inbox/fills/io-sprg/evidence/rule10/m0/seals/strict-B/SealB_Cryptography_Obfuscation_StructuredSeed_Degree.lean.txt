/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Degrees
/- G06-HARNESS INSTALL SealB_Cryptography_Obfuscation_StructuredSeed_Degree -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealB_Cryptography_Obfuscation_StructuredSeed_Degree"
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
# Public and private polynomial degrees

## Main definitions

* `pubDegree` counts only public variables in a polynomial on a sum of variable types.
* `privDegree` counts only private variables.

## Main results

* The degrees satisfy sum and product bounds and are preserved by groupwise renaming.
* `Internal` supplies the missing weighted-degree closure lemmas.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, Definition 3.3 and pp. 16-17.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviations.** Dv6 specializes Definition 3.3 to one polynomial with separately bounded
public and private degrees. Dv10 uses public degree `d`, as on p. 17, rather than the
motivating overview's `d + 1` on p. 14. The closure facts are mathematical glue.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open scoped BigOperators

variable {σ τ σ' τ' R ι : Type*} [CommSemiring R]

/-- Public degree weights public variables by one and private variables by zero,
`pubDegree q = q.weightedTotalDegree (Sum.elim 1 0)`
[JLS26, Definition 3.3, p. 10]. Dv6 uses the composite polynomial form. -/
noncomputable def pubDegree (q : MvPolynomial (σ ⊕ τ) R) : ℕ :=
  q.weightedTotalDegree (Sum.elim (fun _ : σ => 1) (fun _ : τ => 0))

/-- Public degree equals weighted degree for the public indicator. Glue reader. -/
theorem pubDegree_eq (q : MvPolynomial (σ ⊕ τ) R) :
    pubDegree q =
      q.weightedTotalDegree (Sum.elim (fun _ : σ => 1) (fun _ : τ => 0)) := rfl

/-- Private degree weights public variables by zero and private variables by one,
`privDegree q = q.weightedTotalDegree (Sum.elim 0 1)`
[JLS26, Definition 3.3, p. 10]. Dv6 uses the composite polynomial form. -/
noncomputable def privDegree (q : MvPolynomial (σ ⊕ τ) R) : ℕ :=
  q.weightedTotalDegree (Sum.elim (fun _ : σ => 0) (fun _ : τ => 1))

/-- Private degree equals weighted degree for the private indicator. Glue reader. -/
theorem privDegree_eq (q : MvPolynomial (σ ⊕ τ) R) :
    privDegree q =
      q.weightedTotalDegree (Sum.elim (fun _ : σ => 0) (fun _ : τ => 1)) := rfl

namespace Internal

/-- Weighted degree of a sum is at most the maximum of the summands' degrees.
Mathematical glue for [JLS26, §4, p. 17].

**Proof sketch.** Bound the support by the union and use `le_weightedTotalDegree`. -/
theorem weightedTotalDegree_add_le (w : σ → ℕ) (q r : MvPolynomial σ R) :
    (q + r).weightedTotalDegree w ≤ max (q.weightedTotalDegree w)
      (r.weightedTotalDegree w) := sorry

/-- Weighted degree of a product is at most the sum of the factors' degrees.
Mathematical glue for [JLS26, §4, p. 17].

**Proof sketch.** Split monomials by `support_mul` and add their `Finsupp.weight`s. -/
theorem weightedTotalDegree_mul_le (w : σ → ℕ) (q r : MvPolynomial σ R) :
    (q * r).weightedTotalDegree w ≤ q.weightedTotalDegree w +
      r.weightedTotalDegree w := sorry

/-- A finite sum of polynomials of weighted degree at most `d` has degree at most `d`.
Mathematical glue for [JLS26, §4, p. 17].

**Proof sketch.** Induct on the finite set using the zero and addition bounds. -/
theorem weightedTotalDegree_finset_sum_le (w : σ → ℕ) (s : Finset ι)
    (q : ι → MvPolynomial σ R) (d : ℕ)
    (h : ∀ i ∈ s, (q i).weightedTotalDegree w ≤ d) :
    (∑ i ∈ s, q i).weightedTotalDegree w ≤ d := sorry

/-- A finite product has weighted degree at most the sum of the factors' degrees.
Mathematical glue for [JLS26, §4, p. 17].

**Proof sketch.** Induct on the finite set using the multiplication bound. -/
theorem weightedTotalDegree_finset_prod_le (w : σ → ℕ) (s : Finset ι)
    (q : ι → MvPolynomial σ R) :
    (∏ i ∈ s, q i).weightedTotalDegree w ≤ ∑ i ∈ s, (q i).weightedTotalDegree w := sorry

/-- Constants have weighted degree zero, `weightedTotalDegree w (C a) = 0`.
Mathematical glue for [JLS26, §4, p. 17].

**Proof sketch.** Only the zero monomial can occur in the support. -/
theorem weightedTotalDegree_C (w : σ → ℕ) (a : R) :
    (MvPolynomial.C a : MvPolynomial σ R).weightedTotalDegree w = 0 := sorry

/-- A variable's weighted degree is at most its weight, also over the zero ring.
Mathematical glue for [JLS26, §4, p. 17].

**Proof sketch.** Bound its singleton support and evaluate the monomial weight. -/
theorem weightedTotalDegree_X_le (w : σ → ℕ) (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ R).weightedTotalDegree w ≤ w i := sorry

end Internal

/-- The zero polynomial has public degree zero, `pubDegree 0 = 0`. Mathematical glue.

**Proof sketch.** Use Mathlib's weighted-degree zero lemma and `pubDegree_eq`. -/
theorem pubDegree_zero : pubDegree (0 : MvPolynomial (σ ⊕ τ) R) = 0 := sorry

/-- The zero polynomial has private degree zero, `privDegree 0 = 0`. Mathematical glue.

**Proof sketch.** Use Mathlib's weighted-degree zero lemma and `privDegree_eq`. -/
theorem privDegree_zero : privDegree (0 : MvPolynomial (σ ⊕ τ) R) = 0 := sorry

/-- Constants have public degree zero, `pubDegree (C a) = 0`. Mathematical glue.

**Proof sketch.** Specialize `Internal.weightedTotalDegree_C`. -/
theorem pubDegree_C (a : R) :
    pubDegree (MvPolynomial.C a : MvPolynomial (σ ⊕ τ) R) = 0 := sorry

/-- Constants have private degree zero, `privDegree (C a) = 0`. Mathematical glue.

**Proof sketch.** Specialize `Internal.weightedTotalDegree_C`. -/
theorem privDegree_C (a : R) :
    privDegree (MvPolynomial.C a : MvPolynomial (σ ⊕ τ) R) = 0 := sorry

/-- Public variables have public degree at most one. Mathematical glue.

**Proof sketch.** Specialize the variable bound at the public indicator. -/
theorem pubDegree_X_inl (i : σ) :
    pubDegree (MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ τ) R) ≤ 1 := sorry

/-- Private variables have public degree zero. Mathematical glue.

**Proof sketch.** The public indicator is zero on private variables. -/
theorem pubDegree_X_inr (i : τ) :
    pubDegree (MvPolynomial.X (Sum.inr i) : MvPolynomial (σ ⊕ τ) R) = 0 := sorry

/-- Public variables have private degree zero. Mathematical glue.

**Proof sketch.** The private indicator is zero on public variables. -/
theorem privDegree_X_inl (i : σ) :
    privDegree (MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ τ) R) = 0 := sorry

/-- Private variables have private degree at most one. Mathematical glue.

**Proof sketch.** Specialize the variable bound at the private indicator. -/
theorem privDegree_X_inr (i : τ) :
    privDegree (MvPolynomial.X (Sum.inr i) : MvPolynomial (σ ⊕ τ) R) ≤ 1 := sorry

/-- Public degree of a sum is at most the maximum of the public degrees. Mathematical glue.

**Proof sketch.** Specialize `Internal.weightedTotalDegree_add_le`. -/
theorem pubDegree_add_le (q r : MvPolynomial (σ ⊕ τ) R) :
    pubDegree (q + r) ≤ max (pubDegree q) (pubDegree r) := sorry

/-- Private degree of a sum is at most the maximum of the private degrees. Mathematical glue.

**Proof sketch.** Specialize `Internal.weightedTotalDegree_add_le`. -/
theorem privDegree_add_le (q r : MvPolynomial (σ ⊕ τ) R) :
    privDegree (q + r) ≤ max (privDegree q) (privDegree r) := sorry

/-- Public degree of a product is at most the sum of the public degrees. Mathematical glue.

**Proof sketch.** Specialize `Internal.weightedTotalDegree_mul_le`. -/
theorem pubDegree_mul_le (q r : MvPolynomial (σ ⊕ τ) R) :
    pubDegree (q * r) ≤ pubDegree q + pubDegree r := sorry

/-- Private degree of a product is at most the sum of the private degrees. Mathematical glue.

**Proof sketch.** Specialize `Internal.weightedTotalDegree_mul_le`. -/
theorem privDegree_mul_le (q r : MvPolynomial (σ ⊕ τ) R) :
    privDegree (q * r) ≤ privDegree q + privDegree r := sorry

/-- Finite sums preserve a uniform public-degree bound. Mathematical glue.

**Proof sketch.** Specialize the weighted finite-sum bound. -/
theorem pubDegree_finset_sum_le (s : Finset ι) (q : ι → MvPolynomial (σ ⊕ τ) R)
    (d : ℕ) (h : ∀ i ∈ s, pubDegree (q i) ≤ d) :
    pubDegree (∑ i ∈ s, q i) ≤ d := sorry

/-- Finite sums preserve a uniform private-degree bound. Mathematical glue.

**Proof sketch.** Specialize the weighted finite-sum bound. -/
theorem privDegree_finset_sum_le (s : Finset ι) (q : ι → MvPolynomial (σ ⊕ τ) R)
    (d : ℕ) (h : ∀ i ∈ s, privDegree (q i) ≤ d) :
    privDegree (∑ i ∈ s, q i) ≤ d := sorry

/-- Finite products have public degree at most the sum of the public degrees. Mathematical glue.

**Proof sketch.** Specialize the weighted finite-product bound. -/
theorem pubDegree_finset_prod_le (s : Finset ι) (q : ι → MvPolynomial (σ ⊕ τ) R) :
    pubDegree (∏ i ∈ s, q i) ≤ ∑ i ∈ s, pubDegree (q i) := sorry

/-- Finite products have private degree at most the sum of the private degrees. Mathematical glue.

**Proof sketch.** Specialize the weighted finite-product bound. -/
theorem privDegree_finset_prod_le (s : Finset ι) (q : ι → MvPolynomial (σ ⊕ τ) R) :
    privDegree (∏ i ∈ s, q i) ≤ ∑ i ∈ s, privDegree (q i) := sorry

/-- Groupwise bijective renaming preserves public degree [JLS26, §4, p. 17].
Dv15 uses explicit equivalences to transport structured seed indices; mathematical glue.

**Proof sketch.** Use `weightedTotalDegree_rename_of_injective` and the indicators. -/
theorem pubDegree_rename (e : σ ≃ σ') (f : τ ≃ τ') (q : MvPolynomial (σ ⊕ τ) R) :
    pubDegree (MvPolynomial.rename (Sum.map e f) q) = pubDegree q := sorry

/-- Groupwise bijective renaming preserves private degree [JLS26, §4, p. 17].
Dv15 uses explicit equivalences to transport structured seed indices; mathematical glue.

**Proof sketch.** Use `weightedTotalDegree_rename_of_injective` and the indicators. -/
theorem privDegree_rename (e : σ ≃ σ') (f : τ ≃ τ') (q : MvPolynomial (σ ⊕ τ) R) :
    privDegree (MvPolynomial.rename (Sum.map e f) q) = privDegree q := sorry

end TCSlib.Cryptography.Obfuscation.StructuredSeed
/- G06-HARNESS EOF-VERIFY SealB_Cryptography_Obfuscation_StructuredSeed_Degree -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealB_Cryptography_Obfuscation_StructuredSeed_Degree"
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

