<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryProperFactorWitness_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Proper Factor Witness Characterization

**Claim.** The binary proper factor witness equals true exactly when the two low polynomials are both different from $1$ and their product is the specified monic polynomial.

**Proof.** Unfold the witness: it is the conjunction of the Boolean test that neither coefficient vector is the vector for $1$ and the Boolean test that the convolution coefficients match those of the monic polynomial. The coefficient-vector characterization of the constant polynomial $1$ (`FABL.binaryLowPolynomial_eq_one_iff`) turns the first test into the two inequalities between low polynomials and $1$. The product characterization of the coefficient test (`FABL.binaryProductEqMonic_eq_true_iff`) turns the second test into equality of the product with the monic polynomial. Reordering the resulting conjunction gives the stated equivalence.

**Key facts.** `FABL.binaryLowPolynomial_eq_one_iff`, `FABL.binaryProductEqMonic_eq_true_iff`.
