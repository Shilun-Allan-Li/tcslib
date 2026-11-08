<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.one_div_checkCount_le_innerProduct_failedCheckProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on Check Failure Probability

**Claim.** If at least one of the $2m+2$ endpoint or transition checks fails, then a uniformly chosen seed fails with probability at least $1/(2m+2)$.

**Proof.** There are two endpoint seeds and, for each of the $m$ positions, two transition seeds, for a total of $2m+2$. The specified failing seed shows that the failure predicate holds somewhere in this finite sample space. A predicate holding at a specified sample has uniform probability at least the reciprocal of the sample space's cardinality (`FABL.one_div_card_le_uniformProbability_of_mem`). Applying this result yields the stated lower bound.

**Key facts.** `FABL.one_div_card_le_uniformProbability_of_mem`.
