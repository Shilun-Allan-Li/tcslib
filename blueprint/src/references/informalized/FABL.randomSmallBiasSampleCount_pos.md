<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.randomSmallBiasSampleCount_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Sample Count

**Claim.** For positive natural number $n$ and positive real number $\varepsilon$, the least natural number greater than or equal to $8n/\varepsilon^2$ is positive.

**Proof.** By the defining property of the ceiling, it suffices to show that $8n/\varepsilon^2>0$. The constant $8$ and the real cast of $n$ are positive, and $\varepsilon^2>0$ because $\varepsilon>0$. Thus their quotient is positive, so its natural ceiling is positive.
