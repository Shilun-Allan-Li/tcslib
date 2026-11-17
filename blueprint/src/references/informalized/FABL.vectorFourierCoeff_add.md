<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorFourierCoeff_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Vector Fourier Coefficients

**Claim.** For real-valued functions $f,g$ on $\mathbb F_2^n$, the vector Fourier coefficient of $f+g$ at any frequency is the sum of their coefficients at that frequency.

**Proof.** Express each vector Fourier coefficient as the uniform expectation of the function multiplied by the corresponding Walsh character (`vectorFourierCoeff_eq_expect`). At every point, $(f+g)$ times that character expands as the sum of $f$ times the character and $g$ times the character. Linearity of expectation then gives the sum of the two Fourier coefficients.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`.
