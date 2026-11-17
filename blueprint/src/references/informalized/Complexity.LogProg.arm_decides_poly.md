<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean :: Complexity.LogProg.arm_decides_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial bounds yield logarithmic space

**Claim.** If the register values along the correct halting computation are polynomially bounded and the oracle languages are decidable in logarithmic space, then $L$ is decidable in logarithmic space.

**Proof.** Choose $K$ so that $\log_2(C_0(n+1)^{c_0}+1)+1\le K(\log_2 n+1)$ for every $n$; such a constant exists by the logarithmic bound on a polynomial (`log_poly_bound`). At any pre-halting configuration, each register value $a$ satisfies $a\le C_0(|x|+1)^{c_0}$. The length of its binary representation is at most $\log_2(a+1)+1$ (`length_bits_le_log`), and monotonicity of the logarithm bounds this by $\log_2(C_0(|x|+1)^{c_0}+1)+1$. Hence every register word has length at most $K\logSpace(|x|)$. The side conditions are already part of the assumed computation. The logarithmic-space register-program simulation theorem (`arm_decides`) now applies and yields $L\in\mathrm{LOGSPACE}$.

**Key facts.** `Complexity.LogProg.log_poly_bound`, `Complexity.LogProg.length_bits_le_log`, `Complexity.LogProg.arm_decides`.
