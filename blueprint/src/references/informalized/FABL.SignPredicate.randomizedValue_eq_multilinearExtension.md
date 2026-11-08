<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignPredicate.randomizedValue_eq_multilinearExtension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Value as a Multilinear Extension

**Claim.** For coordinate means in $[-1,1]$, the probability that the predicate accepts independent signs with those means equals its multilinear extension at the mean vector.

**Proof.** The Fourier expansion writes the indicator at each sign vector as a sum of Fourier coefficients times the corresponding monomials (\texttt{FABL.fourier_expansion}). Taking expectation under the independent product distribution and interchanging the finite sum with expectation expresses the randomized value as a sum of expected monomials. For each subset, factor out its Fourier coefficient using linearity of expectation (\texttt{FABL.pmfExpectation_const_mul}); the expected monomial is the product of the coordinate means over that subset (\texttt{FABL.pmfExpectation_independentSigns_monomial}). The resulting sum is exactly the defining multilinear extension.

**Key facts.** `FABL.fourier_expansion`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_independentSigns_monomial`.
