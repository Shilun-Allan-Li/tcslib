<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: stirling_comb_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Stirling lower bound for a binomial ratio

**Claim.** Let `a, b, n : ℕ` with `a + b = n`, `0 < (a:ℝ)`, `0 < (b:ℝ)`, and `0 < c`,
and assume the Stirling-type upper bound
`a!·b! ≤ c · (√2·√a·√π·(a/e)^a) · (√2·√b·√π·(b/e)^b)`. Then
`n^n / (a^a·b^b) / (c·√(π/2)·√n) ≤ n! / (a!·b!)`. A `private` helper: the hypothesis
is an upper Stirling estimate for the denominator `a!·b!`, and the conclusion is the
lower bound it yields for the ratio.

**Proof.** Clear both divisions and chain the two Stirling estimates.

1. `0 < (n:ℝ)` from `a + b = n` with `a > 0` (`Nat.add_pos_left`), and
   `(a:ℝ) + b = n` by `exact_mod_cast`.
2. `hsq_ab`: the square-root prefactors merge,
   `√2·√a·√π·(√2·√b·√π) = 2π·√(a·b)`, via `Real.sqrt_mul` and
   `Real.mul_self_sqrt` (for `2` and for `π`, using `Real.pi_pos`). Rewriting the
   hypothesis with it (`linear_combination`) gives
   `h_stir_ab : a!·b! ≤ c·(2π√(ab))·((a/e)^a·(b/e)^b)`.
3. `h_ab_AM_GM`: `√(a·b) ≤ n/2`, from `am_gm_sqrt_le_half_sum` plus `a + b = n`.
4. `h_stir_n`: `√(2πn)·(n/e)^n ≤ n!` — Mathlib's
   `Stirling.le_factorial_stirling`.
5. Exponential bookkeeping: `(x/e)^k = x^k / exp k` (`div_pow`,
   `Real.exp_nat_mul`) for `a`, `b`, `n`, and `exp a · exp b = exp n`
   (`Real.exp_add`), so the three `e`-powers recombine; and
   `√(2πn)·√(π/2)·√n = π·n` (`sqrt_two_pi_mul_sqrt_pi_half`).
6. `suffices` reduces the goal, via `div_div` and `div_le_div_iff₀` (denominators
   positive by `positivity` and `pow_pos`), to the division-free
   `n^n·(a!·b!) ≤ n!·(a^a·b^b)·(c·√(π/2)·√n)`.
7. Final `calc`: apply `h_stir_ab` (`mul_le_mul_of_nonneg_left`), regroup the
   `e`-powers by step 5 into `(n/e)^n·(a^a·b^b)`, replace `2√(ab)` by `n` using
   step 3 (`nlinarith` with `Real.pi_pos`), rewrite `π·n` back as
   `√(2πn)·√(π/2)·√n`, and close with `h_stir_n`. ∎

**Used in.** `binomial_coef_asymptotic_lower_bound'`, with `a = ⌊np⌋` and
`b = n - a`: it is the step that turns Stirling's approximation into the
`n^n/(a^a b^b)` binomial lower bound driving the entropy asymptotics.
