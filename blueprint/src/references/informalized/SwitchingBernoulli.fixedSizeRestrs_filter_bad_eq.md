<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli.lean :: fixedSizeRestrs_filter_bad_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two spellings of "bad restriction with `k` free variables" agree

**Claim.** For any `f : (Fin n → Bool) → Bool` and any `d k : ℕ`, the number of
restrictions in `fixedSizeRestrs n k` whose restricted function has decision-tree
depth `> d` equals the number of all `ρ : Restriction n` satisfying
`IsRestriction k ρ ∧ IsBadRestriction f d ρ`. No hypotheses are needed.

**Proof.** Purely a change of notation between the Bernoulli-side and
counting-side filters.

1. `congr 1 with ρ` reduces to showing the two filtered `Finset`s are equal
   pointwise.
2. Unfolding `IsRestriction` (which is `ρ.numFree = k`) and `IsBadRestriction`
   (which is `dtDepth (restrictFn f ρ) > d`) via `simp +decide` turns the
   right-hand predicate into the conjunction used on the left.
3. A second `simp +decide [fixedSizeRestrs, Restriction.numFree]` identifies
   membership in `fixedSizeRestrs n k` with `ρ.freeVars.card = k`, which is
   `Restriction.numFree ρ = k` by definition.

**Used in.** `switching_bernoulli` bridge lemma
`switching_fixedSize_bound_small`, where it lets the counting-form conclusion of
`SwitchingLemma2.switching_lemma` be substituted into the numerator of
`fixedSizeRestrProb`.
