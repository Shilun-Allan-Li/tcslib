<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandFalseOutputCost_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Bound for False-Output Cost

**Claim.** For every natural number $d$, the maximum expected query cost on inputs with output $+1$ for the recursive randomized decision tree at level $d+1$ is at most twice the corresponding maximum for output $-1$ at level $d$.

**Proof.** Bound the maximum defining the level-$d+1$ false-output cost by considering each input separately. If the recursive NAND output is not $+1$, that input contributes zero to the conditional maximum, so its contribution is at most twice the nonnegative level-$d$ true-output cost. If the output is $+1$, the NAND rule forces both depth-$d$ block outputs to be $-1$. The successor formula for expected query cost then reduces to the average of the two block input costs: each block cost appears twice in the sum, with no continuation penalty because both block outputs are $-1$. Each block input cost is bounded by the level-$d$ maximum conditional cost for output $-1$ (`RandomizedDecisionTree.inputCost_le_outputConditionalCost`). Their average is therefore at most twice that maximum, proving the desired bound.

**Key facts.** `FABL.recursiveNandRandomizedTree_inputCost_succ`, `FABL.RandomizedDecisionTree.inputCost_le_outputConditionalCost`, `FABL.RandomizedDecisionTree.outputConditionalCost_nonneg`.
