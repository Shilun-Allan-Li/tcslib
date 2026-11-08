<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandRandomizedTree_worstCaseCost_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Worst-Case Cost

**Claim.** The worst-case expected query cost of the level-one randomized tree is $2$.

**Proof.** The upper bound follows from the theorem that worst-case cost is at most the larger of the two output-conditional costs (`recursiveNandRandomizedTree_worstCaseCost_le_maxOutputCost`). At level one these costs are $2$ for output $1$ and $3/2$ for output $-1$ (`recursiveNandFalseOutputCost_one` and `recursiveNandTrueOutputCost_one`), so their maximum is $2$. For the reverse inequality, take the input whose two signs are both $-1$. The level-one input-cost recurrence (`recursiveNandRandomizedTree_inputCost_succ`), together with the base input cost $1$ (`recursiveNandRandomizedTree_inputCost_zero`), gives expected cost $2$ on this input: whichever block is queried first, its level-zero tree costs one query, and since its output is $-1$, the other block is queried too and costs one more. Every input cost is bounded by the worst-case cost (`RandomizedDecisionTree.inputCost_le_worstCaseCost`), so the worst-case cost is at least $2$.

**Key facts.** `FABL.recursiveNandRandomizedTree_worstCaseCost_le_maxOutputCost`, `FABL.recursiveNandFalseOutputCost_one`, `FABL.recursiveNandTrueOutputCost_one`, `FABL.recursiveNandRandomizedTree_inputCost_succ`, `FABL.recursiveNandRandomizedTree_inputCost_zero`, `FABL.RandomizedDecisionTree.inputCost_le_worstCaseCost`.
