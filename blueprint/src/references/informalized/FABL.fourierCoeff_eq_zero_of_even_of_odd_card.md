<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.fourierCoeff_eq_zero_of_even_of_odd_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing for Even Functions

**Claim.** If $f(-x)=f(x)$ for every cube input and $S$ has odd cardinality, then the Fourier coefficient of $f$ at $S$ is zero.

**Proof.** The monomial on $S$ changes by the factor $(-1)^{|S|}$ when the input is negated (`monomial_neg_input`). Since $|S|$ is odd, this factor is $-1$, while $f$ is unchanged. Therefore the product $f(x)\chi_S(x)$ is odd under negation. An odd function on the sign cube has sum zero, so its uniform average—and thus the Fourier coefficient—is zero.

**Key facts.** `FABL.monomial_neg_input`.
