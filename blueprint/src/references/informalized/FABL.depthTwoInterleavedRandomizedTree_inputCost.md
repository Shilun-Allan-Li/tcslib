<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedRandomizedTree_inputCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Input Cost Formula

**Claim.** For every nine-coordinate sign vector, the randomized decision tree's expected input cost equals the sum of the interleaved model costs over all depth-two seeds, divided by $81$.

**Proof.** The seed is drawn uniformly from the finite set of depth-two seeds. Its expected query count is therefore the arithmetic mean of the query counts over that set (`pmfExpectation_uniformPMF_eq_expect`). For each seed, the query count equals the corresponding interleaved model cost (`queryCount_depthTwoInterleavedTreeBySeed`), so the mean is the sum of those costs divided by the number of seeds. Since there are $81$ seeds (`card_depthTwoInterleavedSeed`), the expected cost is the stated sum divided by $81$.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.queryCount_depthTwoInterleavedTreeBySeed`, `FABL.card_depthTwoInterleavedSeed`.
