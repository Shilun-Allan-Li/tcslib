<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: sum_symmDiff_reindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reindexing a sum over frequencies by `S ↦ S ∆ {i}`

**Claim.** For any `g : Finset (Fin n) → ℝ` and any `i : Fin n`,
`∑_{S : Finset (Fin n)} g (S ∆ {i}) = ∑_{S : Finset (Fin n)} g S`, the sums
being over all of `Finset (Fin n)` as a `Fintype`.

**Proof.** A term-mode one-liner: `Fintype.sum_bijective` applied to the map
`S ↦ S ∆ {i}`, whose bijectivity comes from
`(symmDiff_singleton_invol i).bijective` (an involution is a bijection); the
pointwise compatibility obligation is `fun _ => rfl`.

**Used in.** The two places where the branch recursion's shifted block must be
matched against the unshifted one: the `step2` computation inside
`signEval_eq_sum_coeffs`, and the third `calc` step of `sum_abs_coeffs_le`.
Both are `private`-scope uses within this file.
