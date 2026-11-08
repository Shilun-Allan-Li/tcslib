<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeRandomizedTree_inputCost_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base-depth input cost

**Claim.** For every sign input of length $3^0=1$, the randomized decision tree at depth zero has expected query cost $1$.

**Proof.** At depth zero the seed law is concentrated on the unique base seed and the selected tree is the identity tree, which queries its sole coordinate once. The expectation under a point-mass law is the payoff at its supporting point (`pmfExpectation_pure`), so the expected query cost is $1$.

**Key facts.** `FABL.pmfExpectation_pure`.
