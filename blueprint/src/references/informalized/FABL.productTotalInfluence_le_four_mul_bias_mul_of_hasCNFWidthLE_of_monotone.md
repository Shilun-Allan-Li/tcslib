<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productTotalInfluence_le_four_mul_bias_mul_of_hasCNFWidthLE_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound from CNF width

**Claim.** If a monotone sign-valued function has a CNF representation of width at most $w$, then its total influence under the product law with bias parameter $p\in(0,1)$ is at most $4pw$.

**Proof.** The CNF width hypothesis implies that at every input, at most $w$ coordinates are pivotal when the output is $+1$ (\texttt{outputPivotalCount\_one\_le\_of\_hasCNFWidthLE}). Apply the bound that a monotone function whose positive-output pivotal count is everywhere at most $w$ has total influence at most $4pw$ (\texttt{productTotalInfluence\_le\_four\_mul\_bias\_mul\_of\_onePivotalCount\_le}). This gives the claimed estimate.

**Key facts.** `FABL.outputPivotalCount_one_le_of_hasCNFWidthLE`, `FABL.productTotalInfluence_le_four_mul_bias_mul_of_onePivotalCount_le`.
