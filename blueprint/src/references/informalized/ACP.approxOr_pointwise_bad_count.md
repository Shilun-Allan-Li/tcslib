<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOr_pointwise_bad_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# At most a `2^{-ℓ}` fraction of seeds are bad for OR at a fixed input

**Claim.** For every `polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)`
and every point `y : Fin vars → ZMod p`,

`#{S : Fin ℓ → Finset (Fin width) | (approxOr p polys S).eval y ≠ 1 - ∏ k, (1 - ((polys k).eval y) ^ (p - 1))} * 2 ^ ℓ ≤ 2 ^ (width * ℓ)`.

The right-hand product is the *exact* OR detector at `y`, so the filtered set is
the set of seeds on which the approximator gives the wrong answer at `y`. Since
there are `2 ^ (width * ℓ)` seeds in total, the inequality says the bad fraction
is at most `2 ^ (-ℓ)`. Note the bound is uniform in `y` but the bad *set* depends
on `y` — this is a pointwise, not a worst-case-seed, statement.

**Proof.** A two-step `calc`.

1. The bad count times `2 ^ ℓ` is at most
   `Fintype.card (Fin ℓ → Finset (Fin width))`: this is
   `count_bad_S_or` instantiated at the value vector
   `v := fun i => MvPolynomial.eval y (polys i)`, transported through
   `simpa [approxOr_eval_eq, OR_val]` — `approxOr_eval_eq` turns
   `(approxOr p polys S).eval y` into `approxOr_val` of the evaluated inputs, and
   unfolding `OR_val` matches the exact detector on the right.
2. That cardinality equals `2 ^ (width * ℓ)` by `approxSeed_card width ℓ`.

**Remark.** All the content lives in `count_bad_S_or`, which splits on whether the
evaluated input vector is zero (no bad seeds at all) and otherwise calls
`count_bad_S`. There the factor `2 ^ ℓ` arises by combining `approxOr_failure_iff`
with a per-coordinate tuple count (`Fintype.card_fun`-style equivalence) and the
toggle involution of `subset_sum_zero_bound`: for a nonzero vector, at most half
of all subsets have vanishing subset sum, independently in each of the `ℓ`
coordinates.

**Used in.** `exists_good_approxOr` and `approxAnd_pointwise_bad_count`, which
obtains the AND version by applying this lemma to the complemented inputs
`fun i => 1 - polys i`.
