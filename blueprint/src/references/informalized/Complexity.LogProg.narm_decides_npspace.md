<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean :: Complexity.LogProg.narm_decides_npspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Space from Register Computations

**Claim.** If the oracle languages are decidable in polynomial space and the register machine satisfies the stated polynomial register-size, halting, and correctness assumptions, then its language belongs to nondeterministic polynomial space.

**Proof.** For each oracle language, choose an exponent $e_j$, a constant $c_j$, and a deterministic decider using at most $c_j(v^{e_j}+1)$ space on inputs of length $v$. Put $A_0=2+2mC_0+2m$ and choose a common exponent $E=(c_0+1)(\sum_j e_j+1)$. Also set $C_*=C_0+\sum_j c_j(A_0^{e_j}+1)$. The polynomial-space simulation theorem `narm_decides_space` applies with target scale $S(n)=(n+1)^E$ and register-word bound $W(n)=C_0(n+1)^{c_0}$. This word bound is at most $C_0S(n)$. For an oracle query of length $v$, the input and register bounds give $v\le A_0(n+1)^{c_0+1}$. Hence $v^{e_j}\le A_0^{e_j}(n+1)^{(c_0+1)e_j}\le A_0^{e_j}S(n)$ by the choice of $E$. It follows that the $j$th oracle decider uses at most $c_j(A_0^{e_j}+1)S(n)$ space. Summing the oracle costs and the register simulation cost gives at most $C_*S(n)$. The simulation theorem therefore places the language in nondeterministic space bounded by a constant multiple of $(n+1)^E$. Finally, the elementary estimate $(n+1)^E\le 2^E(n^E+1)$ and closure under constant-factor space bounds (`NSPACE.mono_const`) put the language in the union defining nondeterministic polynomial space.

**Key facts.** `Complexity.LogProg.narm_decides_space`, `Complexity.NSPACE.mono_const`, `Complexity.succ_pow_le`.
