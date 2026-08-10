<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: degree_zero_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A degree-zero function is constant

**Claim.** If `f : BooleanFunc n` satisfies `has_degree_at_most f 0`, then
`∀ x, f x = f default` — i.e. `f` agrees everywhere with its value at the
all-`false` point.

**Proof.**

1. Fix `x`. Replace `f` by its Walsh expansion,
   `have h_fourier : f = fun x => ∑ S, fourierCoeff f S * chiS S x`, via
   `funext` and `walsh_expansion`. The rewrite hits both sides, so the goal
   becomes an equality of two sums, over `x` and over `default`.
2. `Finset.sum_congr rfl` reduces it to a per-frequency claim
   `fourierCoeff f S * chiS S x = fourierCoeff f S * chiS S default`.
3. If `fourierCoeff f S = 0` the term vanishes on both sides (`by_cases` +
   `simp`).
4. Otherwise `hf S` gives `S.card ≤ 0`, hence `S = ∅` by
   `Finset.card_eq_zero`; and `chiS ∅` is the constant `1`, so the two terms
   agree (`simp_all`). ∎

**Used in.** `degree_zero_fourth_moment`, which is the `k = 0` base case of the
`bonami_expect` induction.
