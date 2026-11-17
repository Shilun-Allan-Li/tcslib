<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.mem_influentialCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influential coordinate membership

**Claim.** A coordinate belongs to the set of coordinates whose influence under $f$ is at least $\tau$ exactly when $\tau$ is at most its influence under $f$.

**Proof.** The influential coordinates are defined by filtering all coordinates according to whether their influence is at least $\tau$. This membership condition is exactly $\tau\leq \operatorname{influence}_f(i)$.
