<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.totalInfluence_composedMajority_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for composed majority influence

**Claim.** For every natural number $m$, the total influence of the composed majority function is at least $\frac18\sqrt{2m+3}$.

**Proof.** Write $T=2m+1$ and let $E_m$ be the error term in the exact formula for total influence. That formula gives $I_m=1+\frac12\sqrt{2/\pi}\sqrt{T}+E_m$. The error belongs to $[0,1/(2\sqrt T)]$, so in particular it is nonnegative. Also $\sqrt{2/\pi}\ge 1/2$, whence $I_m\ge \frac14\sqrt T$. The dimension comparison $\sqrt{2m+3}\le 2\sqrt T$ then yields $I_m\ge \frac18\sqrt{2m+3}$: indeed, $\frac18\sqrt{2m+3}\le\frac14\sqrt T$.

**Key facts.** `FABL.composedMajorityInfluenceError_mem_Icc`, `FABL.totalInfluence_composedMajority_eq_main_add_error`, `FABL.one_half_le_sqrt_two_div_pi`, `FABL.sqrt_composedMajority_dimension_le`.
