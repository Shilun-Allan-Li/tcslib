<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedRandomizedTree_inputCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Tree Input Cost Bound

**Claim.** For every nine-coordinate sign vector, the randomized decision tree's expected input cost is at most $571/81$.

**Proof.** By the expected-cost formula (`depthTwoInterleavedRandomizedTree_inputCost`), the expected input cost is the total model-cost sum divided by $81$. The total sum is at most $571$ (`depthTwoInterleavedModelCostSum_le`); dividing this inequality by the positive number $81$ preserves its direction and gives the bound $571/81$.

**Key facts.** `FABL.depthTwoInterleavedRandomizedTree_inputCost`, `FABL.depthTwoInterleavedModelCostSum_le`.
