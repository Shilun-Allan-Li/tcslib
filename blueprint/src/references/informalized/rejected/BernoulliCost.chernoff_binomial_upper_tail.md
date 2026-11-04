<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: chernoff_binomial_upper_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Chernoff upper tail for the binomial at twice the mean

**Claim.** For `nn : ℕ` and `p : ℝ` with `0 < p ≤ 1`,
`∑ k ∈ (Finset.range (nn+1)).filter (fun k => (k : ℝ) > 2 · nn · p),
binomialPMF nn p k ≤ Real.exp (-(nn · p / 3))`. In words: `Pr[Bin(nn,p) > 2 nn p]
≤ e^{−nn p/3}`, the multiplicative Chernoff bound at `δ = 1`.

**Proof.** `by_cases h_cases : p ≤ 0.5`.

*Case `p ≤ 1/2`* — the genuine Chernoff argument, with `t = log 2`.

1. **MGF identity and bound:**
   `∑ k C(nn,k) p^k (1−p)^{nn−k} e^{k log 2} = (p e^{log 2} + (1−p))^{nn}` by
   `add_pow` with `mul_pow` and `Real.exp_nat_mul`; then `Real.rpow_natCast`,
   `Real.rpow_def_of_pos` and `Real.log_le_sub_one_of_pos` bound it by
   `exp (nn · p · (e^{log 2} − 1))` (base positive by `Real.add_one_le_exp`,
   `Real.log_pos one_lt_two`).
2. **Shift by the threshold:** multiply through by `exp (−2 nn p log 2) ≥ 0`
   (`mul_le_mul_of_nonneg_right`, `Real.exp_nonneg`), rearranging summands with
   `Finset.sum_mul` and `Real.exp_add`/`Real.exp_neg`, to get
   `∑ k … e^{(k − 2 nn p) log 2} ≤ exp (nn p (e^{log 2} − 1) − 2 nn p log 2)`.
3. **Exponent arithmetic:** `Real.exp_log` turns `e^{log 2}` into `2`, and
   `Real.log_two_gt_d9` with `nlinarith` (using `nn · p ≥ 0`) gives
   `nn p (2 − 1) − 2 nn p log 2 ≤ −nn p / 3`.
4. **Dropping the exponential on the tail:** for `k > 2 nn p` the factor
   `e^{(k − 2 nn p) log 2} ≥ 1` (`Real.one_le_exp`, `le_mul_of_one_le_right`) and
   all summands are nonnegative, so `gcongr`/`split_ifs` bounds
   `∑ k, if k > 2 nn p then binomialPMF nn p k else 0` by the step-2 sum; a final
   `convert … using 1` with `Finset.sum_ite` matches the filtered sum.

*Case `p > 1/2`* — the tail is empty.

5. `rcases eq_or_ne nn 0`: for `nn = 0`, `simp` and `Finset.sum_filter` finish.
   For `nn > 0`, `2 nn p > nn ≥ k` for every `k ∈ range (nn+1)` (`nlinarith` from
   `k ≤ nn`, `0 < nn`, `0.5 < p`), so the filter is `∅`; `Finset.sum_empty` and
   `Real.exp_nonneg` close the goal.

**Used in.** `bernoulli_restriction_cost`, as the additive `e^{−np/3}` error
term.
