<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.binaryLowPolynomial_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the coefficient polynomial map

**Claim.** For every natural number $\ell$, the map sending a length-$\ell$ coefficient vector to its low polynomial is injective.

**Proof.** Suppose two vectors have the same low polynomial. For each coordinate $i$, take the coefficient in degree $i$ on both sides. Since $i<\ell$, the low-polynomial coefficient formula (`coeff_binaryLowPolynomial`) identifies these coefficients with the respective entries of the two vectors. The entries therefore agree at every coordinate, so the vectors are equal.

**Key facts.** `FABL.coeff_binaryLowPolynomial`.
