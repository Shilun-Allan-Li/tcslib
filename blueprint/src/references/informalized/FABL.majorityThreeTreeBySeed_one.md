<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.majorityThreeTreeBySeed_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed one selects the second tree

**Claim.** When the seed is $1$, the seeded three-sign decision tree is exactly the tree that queries coordinates $0$ and $2$ first and coordinate $1$ if their signs differ.

**Proof.** Substitute seed $1$ into the definition of the seeded tree. The test for seed $0$ fails, and the test for seed $1$ succeeds, so the selected tree is the second tree, which queries coordinates $0$ and $2$ first and queries coordinate $1$ when their signs differ.
