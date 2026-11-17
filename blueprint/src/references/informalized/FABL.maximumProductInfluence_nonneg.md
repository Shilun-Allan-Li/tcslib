<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.maximumProductInfluence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative maximum product influence

**Claim.** For every finite alphabet, probability mass function, dimension, and real-valued function on the product space, the maximum product influence is nonnegative.

**Proof.** If the coordinate set is nonempty, its maximum is the supremum over coordinates. Each coordinate influence is nonnegative, so it is bounded above by that supremum, which is therefore nonnegative. If the coordinate set is empty, the definition assigns the maximum product influence the value zero. Both cases give the claim.

**Key facts.** `FABL.productInfluence_nonneg`.
