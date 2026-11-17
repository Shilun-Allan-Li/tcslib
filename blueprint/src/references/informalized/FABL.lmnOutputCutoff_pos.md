<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.lmnOutputCutoff_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the output cutoff

**Claim.** If $0<\varepsilon\leq1$, then the output cutoff, the least natural number at least $\log_2(2/\varepsilon)$, is positive.

**Proof.** If the cutoff were zero, `half_pow_lmnOutputCutoff_le` would imply $(1/2)^0\leq\varepsilon/2$, hence $1\leq\varepsilon/2$. But $\varepsilon\leq1$ implies $\varepsilon/2\leq1/2$, a contradiction. Thus the cutoff is positive.

**Key facts.** `FABL.half_pow_lmnOutputCutoff_le`.
