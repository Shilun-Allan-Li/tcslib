<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: OR_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Exact OR over `ZMod p`

**Definition.** For `v : Fin width → ZMod p`,

`OR_val p v = 1 - ∏ k, (1 - (v k) ^ (p - 1))`.

A plain definition; no proof.

**Why this is OR.** By Fermat's little theorem — packaged in this file as
`one_sub_pow_card_sub_one`, `1 - a^(p-1) = if a = 0 then 1 else 0` — each factor is
the indicator of `v k = 0`. So the product is the indicator of `v = 0`, and
`OR_val p v` is `1` exactly when some coordinate is nonzero. This is the *exact*
OR, the target that the randomized `approxOr_val` (which sums over `ℓ` random
subsets instead of testing all `width` coordinates one by one) is trying to match
at low degree.

**Used in.** In-file only: `approxOr_failure_iff` characterises when the
approximator misses it (`approxOr_val p v S ≠ OR_val p v ↔ v ≠ 0 ∧ ∀ k, ∑ i ∈ S k, v i = 0`),
and the bad-seed counts `count_bad_S` / `count_bad_S_or` are stated against it.
The polynomial-level consumers such as `exists_good_approxOr` write
`1 - ∏ k, (1 - ((polys k).eval y)^(p-1))` out by hand and only meet `OR_val`
through a `simpa [approxOr_eval_eq, OR_val]` bridge.
