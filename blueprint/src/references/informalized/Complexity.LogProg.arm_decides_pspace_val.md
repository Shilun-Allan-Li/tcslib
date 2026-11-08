<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.LogProg.arm_decides_pspace_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential register values use polynomial space

**Claim.** If each register value along the correct halting computation is at most $2^{C_0(|x|+1)^{c_0}}$ and the oracle languages are in polynomial space, then $L$ is decidable in polynomial space.

**Proof.** Apply the polynomial-space register theorem (`arm_decides_pspace`) with register-word exponent coefficient $C_0+2$. To verify its register-length hypothesis, put $N=C_0(|x|+1)^{c_0}$. Each register value $a$ satisfies $a\le2^N$, so $a+1<2^{N+2}$. The binary length bound for numbers below a power of two (`length_bits_le`) gives $|\mathrm{bits}(a+1)|\le N+2$. Since $(|x|+1)^{c_0}\ge1$, this is at most $(C_0+2)(|x|+1)^{c_0}$. The assumed side conditions and halting correctness are unchanged, so `arm_decides_pspace` yields the conclusion.

**Key facts.** `Complexity.LogProg.arm_decides_pspace`, `Complexity.LogProg.length_bits_le`.
