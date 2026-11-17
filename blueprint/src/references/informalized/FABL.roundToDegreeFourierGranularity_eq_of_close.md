<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.roundToDegreeFourierGranularity_eq_of_close -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rounding within half a granule

**Claim.** If a rational number $q$ lies within half a Fourier granularity $g_k$ of the integer multiple $zg_k$, rounding $q$ to the nearest multiple of $g_k$ gives $zg_k$.

**Proof.** The granularity $g_k$ is positive (`degreeFourierGranularity_pos`). Dividing the strict distance bound by $g_k$ therefore places $q/g_k$ strictly between $z-1/2$ and $z+1/2$. The nearest-integer rounding characterization says that every point in this interval rounds to $z$. Casting this equality between real and rational rounding, then multiplying by $g_k$, gives the claimed rational identity.

**Key facts.** `FABL.degreeFourierGranularity_pos`.
