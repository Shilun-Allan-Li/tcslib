<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.half_pow_lmnOutputCutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output-Cutoff Power Bound

**Claim.** For every real number $\varepsilon>0$, if $d$ is the output cutoff, then $(1/2)^d\le\varepsilon/2$.

**Proof.** Apply the cutoff estimate (`mul_inv_two_pow_dnfWidthTruncationCutoff_le`) with width parameter $1$ and tolerance $\varepsilon/2$, which is positive. It gives $1\cdot(2^d)^{-1}\le\varepsilon/2$ for the resulting cutoff $d$. The output cutoff is exactly this choice of $d$, and $(2^d)^{-1}=(1/2)^d$, giving the claimed inequality.

**Key facts.** `FABL.mul_inv_two_pow_dnfWidthTruncationCutoff_le`.
