<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ReasonableProductPolynomials.lean :: FABL.productMultilinearRandomVariable_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Coordinate Decomposition

**Claim.** For a vector with first coordinate $z$ and remaining coordinates $\omega$, the product multilinear random variable decomposes into the first-coordinate value times the polynomial with odd coefficients, plus the polynomial with even coefficients, both evaluated on the remaining coordinates.

**Proof.** Write the input vector as $(z,\omega)$. By definition, the random variable evaluates the product multilinear polynomial at the coordinatewise values of the functions $X$. In positive dimension, that polynomial splits into its first-coordinate contribution and its remainder. Substituting the coordinatewise values gives the stated decomposition: the first-coordinate value $X_0(z)$ multiplies the polynomial formed from the odd coefficients, and the even-coefficient polynomial supplies the remaining term.
