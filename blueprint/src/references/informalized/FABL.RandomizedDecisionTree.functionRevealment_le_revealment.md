<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.functionRevealment_le_revealment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Function Revealment Is Bounded by Tree Revealment

**Claim.** For a finite input alphabet, the infimum of revealment over randomized decision trees computing a function is at most the revealment of any particular such tree under the product input distribution.

**Proof.** The function revealment is the infimum of the revealments of all randomized trees computing the function. This family is nonempty because the complete deterministic tree computes the function (`completeTree_computes`), and it can be regarded as a randomized tree. Its revealment values are bounded below by zero, since every such tree has nonnegative revealment (`revealment_nonneg`). The infimum is therefore defined, and it is no greater than any member of the family; applying this to the given tree proves the claim.

**Key facts.** `FABL.RandomizedDecisionTree.revealment_nonneg`.
