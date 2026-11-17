<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_toReal_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Mean

**Claim.** If two sign-valued functions satisfy $f(x)\le g(x)$ at every input, then the mean of their real-valued sign representations satisfies $\mathbb E[f]\le\mathbb E[g]$.

**Proof.** The real-valued sign map is monotone (`FABL.monotone_signValue`), so the pointwise hypothesis implies that the real-valued representation of $f$ is at most that of $g$ at every point. The mean on the finite cube is the sum of these values divided by the same positive cardinality. Summing the pointwise inequalities and dividing by that cardinality proves the desired inequality.

**Key facts.** `FABL.monotone_signValue`.
