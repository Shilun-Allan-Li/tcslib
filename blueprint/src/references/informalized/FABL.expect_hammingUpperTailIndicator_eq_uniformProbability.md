<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.expect_hammingUpperTailIndicator_eq_uniformProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail Probability as an Expectation

**Claim.** For every $t\in\mathbb R$ and $n\in\mathbb N$, the uniform expectation of the indicator that the normalized Rademacher sum exceeds $t$ equals the uniform probability of that event.

**Proof.** Unfolding the indicator and the definition of uniform probability gives the same function of each cube point: it is $1$ when the normalized sum exceeds $t$ and $0$ otherwise. The two expectations are therefore definitionally equal.
