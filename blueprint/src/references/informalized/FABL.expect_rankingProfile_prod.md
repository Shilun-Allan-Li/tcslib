<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.expect_rankingProfile_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Product over Profiles

**Claim.** For functions assigned to the voters, the uniform expectation over ranking profiles of the product of their values equals the product of their individual uniform expectations over rankings.

**Proof.** Write the expectation over all profiles as a sum divided by the number of profiles. A profile is a choice of one ranking for each voter, so its product sum factors into the product, over voters, of the sums of the corresponding functions over the six rankings. The number of profiles is likewise the product of the number of rankings available to each voter. Dividing the factored numerator by this factored denominator gives the product of the individual uniform expectations.
