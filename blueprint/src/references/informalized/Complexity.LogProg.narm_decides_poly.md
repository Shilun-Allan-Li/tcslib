<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean :: Complexity.LogProg.narm_decides_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Registers and Nondeterministic Logspace

**Claim.** If a nondeterministic register program has polynomially bounded register values, satisfies its validity conditions on every run before a common halting length, and accepts exactly when some choice string answers yes, then its language belongs to $	ext{NL}$.

**Proof.** Choose a constant $K$ from the logarithmic bound on polynomial quantities (`log_poly_bound`), so that the logarithm of $C_0(|x|+1)^{c_0}+1$ is at most $K\,\mathrm{logSpace}(|x|)$. Apply the register-program simulation theorem (`narm_decides`), which gives an NL machine provided each register value in every pre-final configuration has a binary representation of length at most $K\,\mathrm{logSpace}(|x|)$. For such a configuration, let $v$ be any register value. The binary-length estimate $(\mathrm{Nat.bits}\,n).\mathrm{length}\leq \mathrm{Nat.log}\,2\,n+1$ (`length_bits_le_log`) bounds the length of $v$ by $\mathrm{Nat.log}\,2\,(v+1)+1$. Since $v\leq C_0(|x|+1)^{c_0}$ and the logarithm is monotone, this is at most $\mathrm{Nat.log}\,2\,(C_0(|x|+1)^{c_0}+1)+1$, hence at most the chosen logarithmic-space bound. The original validity condition is preserved, and the halting and acceptance equivalence are unchanged. Thus all hypotheses of the simulation theorem hold, yielding $L\in\text{NL}$.

**Key facts.** `Complexity.LogProg.log_poly_bound`, `Complexity.LogProg.narm_decides`, `Complexity.LogProg.NHalts.mono`, `Complexity.LogProg.length_bits_le_log`.
