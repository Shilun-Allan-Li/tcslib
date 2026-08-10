<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: bernoulli_restriction_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cost of switching from the fixed-size to the Bernoulli restriction model

**Claim.** Let `0 < n`, `0 < p ≤ 1`, `0 < w`, `0 < s`, and let
`event : Restriction n → Prop` be decidable. If
`fixedSizeRestrProb event k ≤ (5 k w / n) ^ s` for every `k ≤ n`, then
`bernoulliRestrProb p event ≤ (10 p w) ^ s + Real.exp (-(n · p / 3))`. So a
fixed-size bad-event bound of the form `(5kw/n)^s` transfers to the Bernoulli
model at the cost of one additive `e^{−np/3}`.

**Proof.** Split the binomial mixture at `k = 2np`.

1. **`h_split`:** rewrite `bernoulliRestrProb p event` by
   `bernoulli_decompose p hp.le hp1 event` and, using
   `← Finset.sum_add_distrib`, bound it termwise (`gcongr`, `split_ifs`) by
   `(∑ k, if k ≤ 2np then binomialPMF n p k · (10pw)^s else 0) +
    (∑ k, if k > 2np then binomialPMF n p k else 0)`.
   - Low `k`: `mul_le_mul_of_nonneg_left` with `binomialPMF_nonneg`, then
     `h_fixed k` and `pow_le_pow_left₀` — since `k ≤ 2np`, `5kw/n ≤ 10pw`
     (`div_le_iff₀`, `nlinarith`, using `1 ≤ w`).
   - High `k`: drop the probability factor by `mul_le_of_le_one_right` with
     `fixedSizeRestrProb_le_one`.
2. **Low-`k` sum:** it suffices (`suffices h_factor`) that
   `∑ k, if k ≤ 2np then binomialPMF n p k else 0 ≤ 1`, since `(10pw)^s ≥ 0`
   (`positivity`) then factors out by `mul_le_mul_of_nonneg_right` plus
   `Finset.sum_ite`/`Finset.mul_sum` bookkeeping. That bound is
   `Finset.sum_le_sum` against the untruncated sum, which is `1` by
   `binomialPMF_sum_one`; dropped terms are `≥ 0` by `binomialPMF_nonneg`.
3. **High-`k` sum:** `convert chernoff_binomial_upper_tail n p hp hp1 using 1`
   after `Finset.sum_filter` turns the `if`-sum into the filtered sum, giving
   `≤ exp (−(n p / 3))`.
4. `add_le_add` of steps 2 and 3, composed with `h_split` by `le_trans`.

**Remark.** `n_pos` and `hw` enter only through the `5kw/n ≤ 10pw` comparison in
step 1; `_hs` is unused.

**Used in.** `bernoulli_restriction_asymptotic`.
