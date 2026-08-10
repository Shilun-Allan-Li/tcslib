<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: alpha_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Squaring the shift parameter

**Claim.** If `0 < n` and `2 * d ≤ n`, then `(alpha n d)^2 = (n - 2*d) / n`,
i.e. squaring cancels the square root in `alpha n d = Real.sqrt ((n - 2*d)/n)`.

**Proof.** The two hypotheses exist only to make the radicand nonnegative.

1. `(0 : ℝ) < n` by `exact_mod_cast hn`.
2. `0 ≤ (n : ℝ) - 2 * d`: cast `hd` to `ℝ` (`exact_mod_cast`) and `linarith`.
3. Hence `0 ≤ ((n : ℝ) - 2*d) / n` by `div_nonneg` with step 1.
4. `Real.sq_sqrt` applied to step 3 gives
   `(Real.sqrt ((n - 2*d)/n))^2 = (n - 2*d)/n`, and `simpa [alpha]` unfolds
   `alpha` to finish.

**Used in.** Rewriting the `α^2 * n` term of the Rankin inequality in
`johnson_arith`, where it turns the square root into the rational expression
that `nlinarith` can handle.
