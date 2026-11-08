<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.auxiliaryAverageCost_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Average Cost Definitions

**Claim.** The auxiliary average cost of $T$ under the product distribution equals its deterministic average cost under that distribution.

**Proof.** Unfolding the two average-cost definitions shows that both sides are the same product mean of the query count: each is the expectation of $x\mapsto \mathrm{queryCount}(T,x)$ under the product probability mass function. Thus the equality holds by the definitions.
