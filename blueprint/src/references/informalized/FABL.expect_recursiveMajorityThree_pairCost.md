<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.expect_recursiveMajorityThree_pairCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Cost of the Recursive Tree

**Claim.** For three distinct blocks, the expected cost of querying the first two blocks and querying the third only when their recursive-majority values disagree is five halves times the expected cost on one uniform input.

**Proof.** Since $i,j,k$ are distinct elements of a three-element set, they enumerate its coordinates. Reindex the expectation over block assignments as an expectation over three independent uniform inputs $(X,Y,Z)$. Each of the first two cost terms has expectation equal to the average cost, because the other coordinates do not affect that term; this follows by factoring expectations over independent coordinates. For the third term, rewrite it as the product of the indicator that the first two outputs differ and the cost on the third input. The pair of first inputs is independent of the third, so the product expectation factors. The disagreement probability is $1/2$, hence this term contributes half the average cost. Adding the contributions gives $(1+1+1/2)$ times the average cost, namely $5/2$ times that cost.

**Key facts.** `FABL.expect_triple_mul_separate`, `FABL.expect_pair_mul_separate`, `FABL.expect_recursiveMajorityThree_disagreement`.
