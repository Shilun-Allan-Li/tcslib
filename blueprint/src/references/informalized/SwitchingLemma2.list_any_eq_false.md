<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: list_any_eq_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A list-wide `any` is false when every element fails the predicate

**Claim.** For a list `l : List α` and `p : α → Bool`, if `p x = false` for all
`x ∈ l`, then `l.any p = false`.

**Proof.** Induction on `l` (`induction l with`).

1. `nil`: `[].any p = false` by `rfl`.
2. `cons hd tl`: `simp only [List.any_cons, ...]` rewrites the goal to
   `p hd || tl.any p = false`; the first disjunct is `false` by `h hd` (with
   membership `by simp`), the second by the induction hypothesis applied to the
   restricted assumption `fun x hx => h x (by simp [hx])`, and `Bool.false_or`
   closes it.

**Remark.** A general `List` fact stated locally rather than pulled from
Mathlib; it is the `Bool`-valued dual of `List.all_eq_true` used in the
neighbouring `fixedTerm_implies_dtDepth_zero`.

**Used in.** `killedAll_implies_dtDepth_zero` (same file), to show that a DNF
all of whose terms are killed evaluates to `false` everywhere; also at
`Switching/CanonicalDTree.lean:279`.
