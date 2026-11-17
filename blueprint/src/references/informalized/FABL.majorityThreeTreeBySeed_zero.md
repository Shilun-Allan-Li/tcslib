<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.majorityThreeTreeBySeed_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed zero selects the first tree

**Claim.** When the seed is $0$, the seeded three-sign decision tree is exactly the tree that queries coordinates $0$ and $1$ first and coordinate $2$ if their signs differ.

**Proof.** Substitute seed $0$ into the definition of the seeded tree. The first seed test succeeds, so the selected tree is the first tree, which queries coordinates $0$ and $1$ first and queries coordinate $2$ when their signs differ.
