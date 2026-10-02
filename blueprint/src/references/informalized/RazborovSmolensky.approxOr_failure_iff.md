<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOr_failure_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Exactly when the OR-approximator is wrong

**Claim.** For `v : Fin width → ZMod p` and a seed `S : Fin ℓ → Finset (Fin width)`,

`approxOr_val p v S ≠ OR_val p v ↔ (v ≠ 0 ∧ ∀ k, ∑ i ∈ S k, v i = 0)`.

So the approximator errs precisely when the input is not identically zero — the
true OR is `1` — yet *every one* of the `ℓ` subset sums happens to vanish. This
is the statement that converts "approximation error" into a pure counting
question about seeds.

**Proof.** `by_cases hv : v = 0`.

*Case `v = 0`.* Both sides are false. `simp [approxOr_val, OR_val,
one_sub_pow_card_sub_one]`: every subset sum and every coordinate is `0`, so each
Fermat indicator `1 - x ^ (p - 1)` is `1`, both products are `1`, and both values
are `1 - 1 = 0`; the right-hand conjunct fails on `v ≠ 0`.

*Case `v ≠ 0`.* Two directions.

1. **(→)** Assume failure; we must show every subset sum vanishes. `by_contra hk`
   gives a `k` with `∑ i ∈ S k, v i ≠ 0`. Then that factor is
   `1 - (∑ i ∈ S k, v i) ^ (p - 1) = 0` by `one_sub_pow_card_sub_one`, so
   `Finset.prod_eq_zero (Finset.mem_univ k)` kills the whole product and
   `approxOr_val p v S = 1`. Independently, `Function.ne_iff.mp hv` produces a
   coordinate `k` with `v k ≠ 0`, and the same two steps give `OR_val p v = 1`.
   Both sides equal `1`, contradicting the assumed disagreement.
2. **(←)** Assume `v ≠ 0` and all subset sums vanish. Then every factor is
   `1 - 0 ^ (p - 1) = 1`, so `simp [one_sub_pow_card_sub_one, hsum_zero]` gives
   `approxOr_val p v S = 0`; and `OR_val p v = 1` exactly as above from a nonzero
   coordinate. `norm_num` finishes from `0 ≠ 1` in `ZMod p` (nontrivial, `p` prime).

**Remark.** Both halves reuse the same two-line pattern — *one vanishing factor
forces the product to zero, hence the value to `1`* — applied once to the subset
sums and once to the raw coordinates.

**Used in.** `count_bad_S` (as the rewrite that turns the bad-seed filter into
`∀ k, ∑ i ∈ S k, v i = 0`) and `count_bad_S_or`.
