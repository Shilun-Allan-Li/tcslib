<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.lmnWidthCutoff_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the width cutoff

**Claim.** If $s>1$ and $0<\varepsilon\leq1/2$, then the width cutoff, the least natural number at least $\log_2(16s/\varepsilon)$, is positive.

**Proof.** Assume the cutoff is zero. The estimate `mul_inv_two_pow_dnfWidthTruncationCutoff_le`, applied with parameter $\varepsilon/16$, gives $s\,2^{-\mathrm{cutoff}}\leq\varepsilon/16$. At cutoff zero this says $s\leq\varepsilon/16$. But $s>1$ implies $s\geq2$, while $\varepsilon\leq1/2$ implies $\varepsilon/16\leq1/32$. This is impossible, so the cutoff is positive.

**Key facts.** `FABL.mul_inv_two_pow_dnfWidthTruncationCutoff_le`.
