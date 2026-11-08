<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.fourierCoeff_eq_zero_of_odd_of_even_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing for Odd Functions

**Claim.** If $f(-x)=-f(x)$ and $S$ has even cardinality, then the Fourier coefficient of $f$ at $S$ is zero.

**Proof.** Negating the input multiplies the monomial on $S$ by $(-1)^{|S|}$ (`monomial_neg_input`). Since $|S|$ is even, the monomial is unchanged, whereas $f$ changes sign. Thus the product $f(x)\chi_S(x)$ is odd under negation. Its sum over the sign cube is zero, and so its uniform average, the Fourier coefficient, is zero.

**Key facts.** `FABL.monomial_neg_input`.
