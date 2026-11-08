<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.bind_replace_independentProductPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replacement in an independent product law

**Claim.** Replacing the law at a fixed coordinate by a point mass at a value sampled from its original law, and then mixing over that sampled value, recovers the original independent product law.

**Proof.** It is enough to compare the two probability mass functions at an arbitrary assignment. In the bind defining the mixture, sum over the sampled label. By `independentProductPMF_apply`, the probability of the assignment under each conditional product law is the product of the coordinate probabilities. Every label other than the assignment's value at the chosen coordinate contributes zero, because the point mass there assigns zero probability to that assignment. The one surviving summand is the original probability of the assignment at the chosen coordinate, multiplied by the product of the original probabilities at all other coordinates. This is exactly the product formula for the original independent product law, so the two mass functions agree at every assignment.

**Key facts.** `FABL.independentProductPMF_apply`.
