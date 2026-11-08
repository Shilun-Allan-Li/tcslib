<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.isPivotal_dictator_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator pivotality

**Claim.** The dictator reading coordinate $i$ is pivotal at $x$ in coordinate $j$ exactly when $j=i$.

**Proof.** Split into the cases $j=i$ and $j\ne i$. If $j=i$, flipping coordinate $j$ replaces the dictator's value $x_i$ by $-x_i$. Since $x_i$ is either $1$ or $-1$, these values differ, so the dictator is pivotal. If $j\ne i$, changing coordinate $j$ leaves coordinate $i$ unchanged; hence the dictator has the same value before and after the flip and is not pivotal.
