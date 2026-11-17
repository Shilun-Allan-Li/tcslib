<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinialExtremizer_isPolynomialThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Threshold Representation

**Claim.** The Gotsman–Linial extremizer is a polynomial threshold function of degree at most $k$.

**Proof.** Choose the cube polynomial itself as the representing function. By the definition of the extremizer, its value at each input is the threshold sign of this polynomial, so the representation condition holds. The product formula identifies the cube polynomial with the product on the cube having $k$ factors. The Fourier-degree bound for that product ($\texttt{fourierDegree_gotsmanLinialProductOnCube_le}$) therefore gives degree at most $k$.

**Key facts.** `FABL.gotsmanLinialCubePolynomial_eq_product`, `FABL.fourierDegree_gotsmanLinialProductOnCube_le`.
