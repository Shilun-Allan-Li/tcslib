<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeRandomizedTree_averageCost_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base-level average query cost

**Claim.** At level $0$, the randomized recursive three-way majority tree has average query cost $1$ under uniform sign inputs.

**Proof.** Replace the average cost by the expected input cost on the uniform sign cube using `recursiveMajorityThreeRandomizedTree_averageCost_eq_expect`. At depth zero, the input cost is constantly $1` (`recursiveMajorityThreeRandomizedTree_inputCost_zero`). The expectation of a constant function is that constant, so the average cost is $1$.

**Key facts.** `FABL.recursiveMajorityThreeRandomizedTree_averageCost_eq_expect`, `FABL.recursiveMajorityThreeRandomizedTree_inputCost_zero`.
