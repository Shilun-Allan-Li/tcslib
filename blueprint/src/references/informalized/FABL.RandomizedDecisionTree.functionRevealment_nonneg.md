<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.functionRevealment_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Function Revealment

**Claim.** For a finite input alphabet, the infimum of revealment over randomized decision trees computing any given function is nonnegative.

**Proof.** The probability mass function has nonempty support, so the input alphabet has an element and is nonempty. Consequently a complete deterministic tree computing the function exists (`completeTree_computes`); viewing it as randomized shows that the family of revealments in the infimum is nonempty. Every member of this family is nonnegative by `revealment_nonneg`. Thus zero is a lower bound for the family, and its infimum is nonnegative.

**Key facts.** `FABL.FiniteDecisionTree.completeTree_computes`, `FABL.RandomizedDecisionTree.revealment_nonneg`.
