<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandTrueOutputCost_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-One True-Output Cost

**Claim.** At depth one, the cost for output $-1$ is $3/2$.

**Proof.** For the upper bound, the true-output cost is at most the corresponding recursive true-cost bound (`recursiveNandOutputCosts_le_recurrence`). At depth one, that recursive cost is $3/2$ (`recursiveNand_costs_one`). For the matching lower bound, use the input with first coordinate $1$ and second coordinate $-1$. Its recursive NAND output is $-1$. By the input-cost recurrence (`recursiveNandRandomizedTree_inputCost_succ`) and the level-zero input cost of $1$ (`recursiveNandRandomizedTree_inputCost_zero`), its expected query cost is $3/2$: the first queried block costs one query, and with probability one half the other block must also be queried. The input cost on an input producing $-1$ is at most the output-conditional cost for $-1$ (`RandomizedDecisionTree.inputCost_le_outputConditionalCost`), yielding the lower bound.

**Key facts.** `FABL.recursiveNandOutputCosts_le_recurrence`, `FABL.recursiveNand_costs_one`, `FABL.recursiveNandRandomizedTree_inputCost_succ`, `FABL.recursiveNandRandomizedTree_inputCost_zero`, `FABL.RandomizedDecisionTree.inputCost_le_outputConditionalCost`.
