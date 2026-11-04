<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: prod_if_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Closing the coordinatewise product into `p^|S| (1−p)^|U∖S|`

**Claim.** For `p : ℝ` and finsets `S U : Finset (Fin n)`,

`∏ i : Fin n, (if i ∈ S then p else if i ∈ U then (1 - p) else 1)`
` = p ^ S.card * (1 - p) ^ (U \ S).card`.

Purely arithmetic bookkeeping; note there is **no** hypothesis relating `S` and
`U` — the `U \ S` on the right handles the overlap.

**Proof.**

1. `rw [← Finset.prod_sdiff (Finset.subset_univ S)]` splits the product over
   `univ` into the part over `univ \ S` times the part over `S`.
2. `h1`: on `S` the first test always succeeds (`if_pos`), so `Finset.prod_const`
   gives `p ^ S.card`.
3. `h2`: on `univ \ S` the first test always fails (`if_neg` via
   `Finset.mem_sdiff`), leaving `if i ∈ U then (1 - p) else 1`; then
   `Finset.prod_ite_mem` together with `hset : (univ \ S) ∩ U = U \ S`
   (`ext`/`tauto`) and `Finset.prod_const` give `(1 - p) ^ (U \ S).card`.
4. `rw [h1, h2, mul_comm]`.

**Used in.** `expectation_fourierCoeff_sq_restrictBF`, immediately after
`sum_varWeight_localFactor_mul` has reduced each coordinate to `p`, `1 - p`, or
`1` — this lemma converts that product into the stated exponents.
