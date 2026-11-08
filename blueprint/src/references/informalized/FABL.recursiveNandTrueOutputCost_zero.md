<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandTrueOutputCost_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial True-Output Cost

**Claim.** At depth zero, the cost for output $-1$ is $1$.

**Proof.** Expand the output-conditional cost as the supremum over inputs, using the input cost when the input produces $-1$ and zero otherwise. Every such term is at most $1$, since the level-zero input cost is $1` (`recursiveNandRandomizedTree_inputCost_zero`); hence the supremum is at most $1$. For the reverse inequality, take the unique one-coordinate input equal to $-1$. The level-zero function outputs $-1$ there, and its input cost is $1$ by the same base-cost fact. This term is included in the supremum, so the supremum is at least $1$.

**Key facts.** `FABL.recursiveNandRandomizedTree_inputCost_zero`.
