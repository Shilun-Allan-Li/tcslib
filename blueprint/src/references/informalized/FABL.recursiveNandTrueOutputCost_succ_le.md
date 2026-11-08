<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandTrueOutputCost_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True-Output Cost Bound

**Claim.** For every natural number $d$, the recursively defined randomized NAND decision tree has cost for output $-1$ at depth $d+1$ at most its cost for output $1$ at depth $d$ plus half its cost for output $-1$ at depth $d$.

**Proof.** Bound the supremum defining the level-$d+1$ cost pointwise over inputs. If an input produces $-1$, the input-cost recurrence (`recursiveNandRandomizedTree_inputCost_succ`) expresses its expected cost as the average of the two possible query orders. The two block outputs cannot both be $1$, since then their NAND would be $1$. If both block outputs are $-1$, each block's cost is bounded by the level-$d$ output-$1$ conditional cost; this gives the required bound using nonnegativity of the output-$-1$ cost. If exactly one block output is $1$, its input cost is bounded by the output-$1$ conditional cost and the other block's by the output-$-1$ conditional cost (`RandomizedDecisionTree.inputCost_le_outputConditionalCost`); averaging the two orders gives the same bound. If the input instead produces $1$, its contribution to the conditional-cost supremum for output $-1$ is zero, which is at most the claimed right-hand side because both conditional costs are nonnegative (`RandomizedDecisionTree.outputConditionalCost_nonneg`). These pointwise bounds establish the supremum inequality.

**Key facts.** `FABL.recursiveNandRandomizedTree_inputCost_succ`, `FABL.RandomizedDecisionTree.inputCost_le_outputConditionalCost`, `FABL.RandomizedDecisionTree.outputConditionalCost_nonneg`.
