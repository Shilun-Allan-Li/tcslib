<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: binom_coeff_ineq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Even binomial coefficients: C(2k, 2j) ≤ C(k, j)·(2k−1)^j

**Claim.** For naturals `k ≥ 1` and `j ≤ k`,
`Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j`. All arithmetic
is over `ℕ`, so the subtractions are truncated (harmless here: `k ≥ 1` and
`j ≤ k`).

**Proof.** Induction on `j` (`induction j with`).

- **`j = 0`:** both sides are `1`; `norm_num`.
- **`j+1`:** three intermediate bounds, then a chain.
  1. `h_ind`: the one-step ratio of even binomials,
     `C(2k, 2j+2) ≤ C(2k, 2j) * ((2k-2j) * (2k-2j-1)) / ((2j+2) * (2j+1))`.
     Via `Nat.le_div_iff_mul_le` this becomes a multiplicative claim, discharged
     from two instances of `Nat.choose_succ_right_eq` (at `2j` and at `2j+1`) by
     `nlinarith`, using `Nat.sub_add_cancel` to unfold the truncated
     subtractions.
  2. `h_ind_step`: multiply the induction hypothesis by the elementary bound
     `(2k-2j) * (2k-2j-1) ≤ (k-j) * (2k-1) * (2j+2)` — proved by `zify`/
     `Nat.cast_sub` to move to `ℤ` and then `nlinarith` — combining the two with
     `Nat.mul_le_mul`.
  3. `h_final`: `C(k,j) * (k-j) ≤ C(k,j+1) * (2j+1)`, from
     `Nat.choose_succ_right_eq` (which gives `C(k,j+1) * (j+1) = C(k,j) * (k-j)`)
     plus `Nat.mul_le_mul_left` and `omega`; then scaled by `(2k-1)*(2j+2)`.
  4. Chain them: `le_trans h_ind`, `Nat.div_le_of_le_mul` to clear the division,
     `le_trans h_ind_step`, and finally `Nat.mul_le_mul_right ((2*k-1)^j) h_final`
     up to `ring`. ∎

**Used in.** `hypercontractivity_2_2k`, where it converts the binomial
coefficients of the `2k`-th moment expansion into the factor `(ρ² (2k−1))^j` that
lets the binomial theorem reassemble the bound.
