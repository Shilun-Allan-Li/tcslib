<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/P.lean :: Complexity.mem_P_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time with Conventional Bounds

**Claim.** A language belongs to $\mathsf{P}$ exactly when some finite Turing machine decides it within $C(n+1)^d$ steps for natural numbers $C,d$.

**Proof.** If $L\in\mathsf{P}$, its definition provides a machine and a bound $a(n^c+1)$ for some natural numbers $a,c$. Since $n^c\le(n+1)^c$ and $1\le(n+1)^c$, this is at most $2a(n+1)^c$. The machine therefore meets a conventional polynomial bound. Conversely, suppose a machine decides $L$ within $C(n+1)^d$ steps. The estimate $(n+1)^d\le2^d(n^d+1)$ (`Complexity.succ_pow_le`) bounds this by $C2^d(n^d+1)$. Hence the machine witnesses membership in the defining union for $\mathsf{P}$. In both directions, a computation within a smaller time bound remains valid at any larger bound by time monotonicity (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.ComputesInTime.mono`, `Complexity.succ_pow_le`.
