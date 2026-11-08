<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.integrableOn_two_mul_add_one_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Negative Power Tail

**Claim.** If $s<-1$ and $a\ge0$, then $x\mapsto(2x+1)^s$ is integrable on $(a,\infty)$.

**Proof.** The standard power-tail criterion gives integrability of $x\mapsto(x+1/2)^s$ on $(a,\infty)$: its shift is positive on this interval, and the exponent is less than $-1$. Since $2x+1=2(x+1/2)$ there, and both factors are nonnegative, the real-power product rule gives $(2x+1)^s=2^s(x+1/2)^s$. Thus the desired function is a constant multiple of an integrable one.
