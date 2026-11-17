<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.sum_krawtchoukValue_mul_pow_eq_noiseKernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk Identity for the Noise Kernel

**Claim.** For $\rho\in[-1,1]$, the weighted sum of Krawtchouk values equals $2^n$ times the probability that the noise kernel sends the input sign vector to the all-ones vector.

**Proof.** First rewrite the weighted Krawtchouk sum as a sum over all subsets of their monomials times $\rho$ raised to subset size (\texttt{FABL.sum_krawtchoukValue_mul_pow}). For each subset, the expected monomial after applying the noise kernel equals this same weighted monomial, by the noise-kernel monomial expectation formula (\texttt{FABL.pmfExpectation_noiseKernel_monomial}). Interchanging the finite subset sum with expectation, then using the identity that the sum of all monomials is $2^n$ times the all-ones point indicator polynomial (\texttt{FABL.sum_monomial_eq_point_indicator}), turns the expression into $2^n$ times the expectation of that indicator. The point-indicator expectation is exactly the probability assigned by the kernel to the all-ones vector (\texttt{FABL.pmfExpectation_point_indicator}), as required.

**Key facts.** `FABL.sum_krawtchoukValue_mul_pow`, `FABL.pmfExpectation_noiseKernel_monomial`, `FABL.pmfExpectation_finset_sum`, `FABL.sum_monomial_eq_point_indicator`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_point_indicator`.
