<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productMean_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the Product Mean

**Claim.** The product mean of $c f$ is $c$ times the product mean of $f$.

**Proof.** The product mean is the expectation under the product distribution. Pulling the constant factor $c$ out of this expectation gives $c$ times the expectation of $f$ (`pmfExpectation_const_mul`).

**Key facts.** `FABL.pmfExpectation_const_mul`.
