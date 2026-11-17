<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.lmnLayerCutoff_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the layer cutoff

**Claim.** If $s>0$ and $0<\varepsilon\leq1$, then the layer cutoff, the least natural number at least $\log_2(2s/\varepsilon)$, is positive.

**Proof.** Suppose instead that the cutoff were zero. The bound `mul_half_pow_lmnLayerCutoff_le` gives $s(1/2)^{\mathrm{cutoff}}\leq\varepsilon/2$. With cutoff zero this becomes $s\leq\varepsilon/2$. Since $s$ is a positive integer, $s\geq1$, whereas $\varepsilon\leq1$ gives $\varepsilon/2\leq1/2$. These inequalities contradict one another, so the cutoff is positive.

**Key facts.** `FABL.mul_half_pow_lmnLayerCutoff_le`.
