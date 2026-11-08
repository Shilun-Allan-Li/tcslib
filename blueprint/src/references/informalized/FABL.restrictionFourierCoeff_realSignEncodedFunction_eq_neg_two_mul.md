<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/BentDegree.lean :: FABL.restrictionFourierCoeff_realSignEncodedFunction_eq_neg_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign encoding coefficient identity

**Claim.** For a nonempty frequency set $A$ among the free coordinates, the restricted Fourier coefficient of the real sign encoding is $-2$ times the corresponding coefficient of the indicator that the Boolean function equals $1$.

**Proof.** Write the real sign encoding pointwise as $1-2\,1_{\{f=1\}}$ (realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding), and evaluate both restricted coefficients as expectations over the free signs, using the pointwise interpretation of restriction (signRestriction_apply). Multiplying by the $A$-monomial and distributing gives the expectation of that monomial minus twice the indicator-function coefficient. The first expectation vanishes: since $A$ is nonempty, its monomial has zero mean, by character orthogonality (expect_indexedMonomial_mul), applied against the empty monomial. Only the second term remains, yielding the stated identity.

**Key facts.** `FABL.signRestriction_apply`, `FABL.realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding`, `FABL.expect_indexedMonomial_mul`.
