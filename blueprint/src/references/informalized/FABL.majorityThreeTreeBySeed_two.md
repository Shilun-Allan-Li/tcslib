<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.majorityThreeTreeBySeed_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed two selects the third tree

**Claim.** When the seed is $2$, the seeded three-sign decision tree is exactly the tree that queries coordinates $1$ and $2$ first and coordinate $0$ if their signs differ.

**Proof.** Substitute seed $2$ into the definition of the seeded tree. The tests for seeds $0$ and $1$ both fail, leaving the third tree, which queries coordinates $1$ and $2$ first and queries coordinate $0$ if those signs differ.
