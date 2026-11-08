<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandFalseOutputCost_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False-Output Cost at Level One

**Claim.** For the recursively defined randomized decision tree on two sign inputs, the maximum expected number of queries over inputs whose output is $+1$ is $2$.

**Proof.** For the upper bound, the general recurrence comparison bounds the randomized tree's false-output cost at level one by the recursive false-output cost, which the level-one cost computation identifies as $2$ (using `recursiveNandOutputCosts_le_recurrence` and `recursiveNand_costs_one`). For the reverse bound, take the input whose two coordinates are both $-1$. Its recursive NAND output is $+1$. The successor formula for expected query cost, together with the level-zero cost of $1$ on each one-coordinate block, gives expected cost $2$ on this input. The input-cost bound for inputs with the specified output then shows that the maximum conditional cost is at least $2$ (`RandomizedDecisionTree.inputCost_le_outputConditionalCost`). Combining the two bounds proves equality.

**Key facts.** `FABL.recursiveNandOutputCosts_le_recurrence`, `FABL.recursiveNand_costs_one`, `FABL.recursiveNandRandomizedTree_inputCost_succ`, `FABL.recursiveNandRandomizedTree_inputCost_zero`, `FABL.RandomizedDecisionTree.inputCost_le_outputConditionalCost`.
