<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.FiniteDecisionTree.majorityThree_hard_averageCost_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hard Distribution Cost for Majority

**Claim.** Any finite decision tree computing majority on three signs has expected query cost at least $8/3$ under the specified hard distribution.

**Proof.** The structural lower bound for majority supplies a first queried coordinate $i$ and, for each sign $a$, a second coordinate $j(a)\ne i$. On every input $x$, the query count is at least $2$ plus an extra $1$ whenever $x_i$ agrees with $x_{j(x_i)}$; this is the fact that the tree must distinguish the relevant majority inputs (`exists_majorityThree_first_second`). The hard distribution is the image of a uniform seed consisting of a sign and a coordinate, so its expected cost equals the seed average of the cost on the corresponding hard input (`deterministicAverageCostUnder_majorityThreeHardPMF`). For these inputs, the probability that the two indicated signs disagree is $2/3$ (`expect_majorityThreeHardInput_skeleton_disagreement`), hence the expected lower bound from the structural estimate is $2+1/3\cdot 2=8/3$—equivalently, the disagreement indicator contributes $0$ on agreement and $1$ on disagreement, with expectation $2/3$. Averaging the pointwise query-count bound therefore gives the claimed lower bound.

**Key facts.** `FABL.FiniteDecisionTree.exists_majorityThree_first_second`, `FABL.deterministicAverageCostUnder_majorityThreeHardPMF`, `FABL.expect_majorityThreeHardInput_skeleton_disagreement`.
