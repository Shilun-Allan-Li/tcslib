<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeRandomizedTree_averageCost_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive-level average cost recurrence

**Claim.** For every depth $d$, the average query cost at level $d+1$ is $5/2$ times the average query cost at level $d$, with uniform sign inputs at both levels.

**Proof.** First replace each average cost by the expected input cost on its uniform sign cube using `recursiveMajorityThreeRandomizedTree_averageCost_eq_expect`. Reorganize an input at depth $d+1$ as three blocks of depth $d$; the block decomposition is a bijection, and its coordinates are the recursive input blocks (`recursiveMajorityThreeBlocksEquiv_apply`). The pointwise cost recurrence (`recursiveMajorityThreeRandomizedTree_inputCost_succ`) expresses the cost for each of the three possible query orders as the two initial block costs plus the third block’s cost precisely when the first two recursive majority values differ. Averaging over the blocks, linearity of expectation separates the three order-dependent terms, and division by three commutes with expectation (`expect_div_const`). For each order, the expected pair cost is $5/2$ times the expected depth-$d$ cost by `expect_recursiveMajorityThree_pairCost`. Thus the three terms each contribute the same quantity; their average is that quantity, proving the recurrence.

**Key facts.** `FABL.recursiveMajorityThreeRandomizedTree_averageCost_eq_expect`, `FABL.recursiveMajorityThreeRandomizedTree_inputCost_succ`, `FABL.recursiveMajorityThreeBlocksEquiv_apply`, `FABL.expect_div_const`, `FABL.expect_recursiveMajorityThree_pairCost`.
