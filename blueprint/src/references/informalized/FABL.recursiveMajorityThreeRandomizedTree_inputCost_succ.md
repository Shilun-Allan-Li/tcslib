<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeRandomizedTree_inputCost_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive input cost recurrence

**Claim.** At depth $d+1$, the expected query cost on an input with three blocks is the average of the three order-dependent costs: each order queries two blocks and queries the remaining block exactly when the first two recursive majority values differ.

**Proof.** Express the input cost as the expectation over the random seed of the deterministic tree’s query count. At depth $d+1$, the seed consists of a uniformly chosen order and three independent depth-$d$ seeds. Iterated expectation over these choices uses the expectation-of-bind identity (`pmfExpectation_bind`); averaging over the three orders is the finite uniform average. For each fixed order and fixed recursive seeds, `queryCount_recursiveMajorityThreeTree_succ` gives the tree’s query count: it is the sum of the two queried block counts, together with the third block’s count if and only if the first two recursive majority outputs differ. Averaging over each block seed turns its query count into that block’s input cost; the expectation-of-map identity (`pmfExpectation_map`) justifies passing from a seed to its selected tree data. Linearity of expectation (`pmfExpectation_add`) separates the sums, while the expectation of a constant (`pmfExpectation_const`) handles the zero contribution when the outputs agree. Evaluating the three possible orders yields the stated formula.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.pmfExpectation_map`, `FABL.queryCount_recursiveMajorityThreeTree_succ`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`.
