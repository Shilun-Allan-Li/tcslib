<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.granularityRestrictionTopCoeff_eq_int_mul_two_inv_pow_of_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer scaling of a restriction coefficient

**Claim.** If $J$ is nonempty, the top restriction coefficient of a sign-valued function on $J$ is an integer multiple of $2(1/2)^{|J|}$.

**Proof.** For each assignment $y$ on $J$, the integrand is a sign: multiplying the value of the sign-valued function by the full monomial in the coordinates of $J$ is again a sign. Thus every integrand is either $-1$ or $1$. The assignment space has $2^{|J|}$ elements, and nonemptiness gives $|J|\ge1$. The integer-scaling formula for the expectation of a sign-valued function on a finite space of size $2^m$ now applies, with $m=|J|$, and supplies the required integer multiple.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`, `FABL.expect_sign_values_eq_int_mul_two_inv_pow`.
