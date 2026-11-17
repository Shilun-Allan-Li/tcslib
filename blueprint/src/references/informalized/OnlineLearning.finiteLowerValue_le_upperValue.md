<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.finiteLowerValue_le_upperValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak duality for finite games

**Claim.** In a finite zero-sum game, the lower value is at most the upper value.

**Proof.** Fix any mixed row strategy $p$ and mixed column strategy $q$. Weak duality says that $p$'s least payoff against a pure column is at most the largest payoff a pure row receives against $q$ (weak_duality). Since this holds for every pair $(p,q)$, take the supremum over $p$ and then the infimum over $q$. The result is that the finite lower value is at most the finite upper value.

**Key facts.** `weak_duality`.
