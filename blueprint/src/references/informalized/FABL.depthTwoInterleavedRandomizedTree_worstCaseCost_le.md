<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedRandomizedTree_worstCaseCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Worst-case cost bound

**Claim.** The depth-two interleaved randomized decision tree has worst-case expected query cost at most $571/81$.

**Proof.** By definition, its worst-case cost is the supremum of its input costs over all inputs. The input-cost bound gives, for each input, a cost at most $571/81$; therefore the supremum is at most this same bound.

**Key facts.** `FABL.depthTwoInterleavedRandomizedTree_inputCost_le`.
