<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The randomized OR-approximating polynomial

**Definition.** Given `width` polynomials `polys i : MvPolynomial (Fin vars) (ZMod p)`
and a seed `S : Fin ℓ → Finset (Fin width)` of `ℓ` subsets of the input wires,
`approxOr p polys S` is

`1 - ∏ k, (1 - (∑ i ∈ S k, polys i) ^ (p - 1))`.

It is the Razborov–Smolensky randomized approximation to `OR (polys 0, …)` over
`ZMod p`. It is `noncomputable` (multivariate polynomial arithmetic over `ZMod p`).

**Why it approximates OR.** By Fermat's little theorem — packaged here as
`one_sub_pow_card_sub_one` — the quantity `1 - x ^ (p - 1)` is the *indicator of
`x = 0`*: it is `1` when `x = 0` and `0` otherwise. Hence each factor tests
whether the `k`-th subset sum `∑ i ∈ S k, polys i` vanishes, the product is `1`
exactly when **all** `ℓ` subset sums vanish, and `approxOr` is therefore `0` in
that case and `1` otherwise.

If every `polys i` evaluates to `0`, all subset sums vanish and the value is `0`,
matching `OR = 0`. If some `polys i` is nonzero, a uniformly random subset has
nonvanishing sum with probability at least `1/2` (`subset_sum_zero_bound`), so
across `ℓ` independent subsets the value is `1 = OR` for all but a `2^{-ℓ}`
fraction of seeds. The two exact failure and counting statements are
`approxOr_failure_iff` and `count_bad_S`.

**Remark.** The gain is degree: each of the `ℓ` factors costs only `p - 1` in
degree rather than the `width` a literal product would cost, giving the
`(p - 1) · ℓ` multiplier of `approxOr_totalDegree` — independent of the fan-in.

**Used in.** `approxOr_totalDegree`, `approxOr_eval_eq`,
`approxOr_pointwise_bad_count`, `approxOrPolyList` / `exists_good_approxOr`, and —
via De Morgan — `approxAnd` and `approxAnd_pointwise_bad_count`.
