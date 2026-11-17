<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.majorityThreeRandomizedTree_worstCaseCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Worst-case query cost bound

**Claim.** The maximum, over all three-coordinate sign inputs, of the randomized decision tree’s expected number of queries is at most $8/3$.

**Proof.** Fix any input $x$. The inputwise estimate ( `majorityThreeRandomizedTree_inputCost_le`) gives an expected query cost of at most $8/3$ on $x$. Thus every value in the finite supremum defining the worst-case cost is bounded by $8/3$, so their supremum is bounded by the same number.

**Key facts.** `FABL.majorityThreeRandomizedTree_inputCost_le`.
