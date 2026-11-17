<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.expect_sq_discreteDerivative_product -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Decomposition of Derivative Influence

**Claim.** The iterated uniform mean of the squared discrete derivative over free and fixed sign assignments equals the influence of the function at the chosen coordinate.

**Proof.** The product expectation formula identifies the iterated mean over free and fixed assignments with the uniform mean over pairs of assignments. The coordinate-splitting bijection then identifies this pair mean with the uniform mean over the full sign cube of the squared discrete derivative. By definition, that full-cube mean is the influence at the chosen coordinate.
