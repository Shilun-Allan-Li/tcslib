<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean :: Complexity.LogProg.narm_decides_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound for Oracle Register Programs

**Claim.** Under the stated space bounds for the oracle deciders and the register representations, the language decided by the nondeterministic register program belongs to $\mathrm{NSPACE}(S)$.

**Proof.** Fix an input $x$ of length $n$. Choose, for each oracle language, a deterministic decider witnessing its assumed space bound, and combine these machines into the banked deterministic oracle simulator. Write $B=C S(n)+1$ and let $k_D$ be the number of work tapes in this simulator. The register bound and the validity conditions imply that each pre-final configuration satisfies the guard required by the register-program simulation: the registers have at most $W(n)$ bits, and the oracle simulator has enough space for every virtual query of length at most $2n+2+m(2W(n)+2)$. The latter follows from the hypothesis on $s_j$ and the choice of $B$. Formally, `npre_of_npreS` transfers the original validity conditions and binary-length bounds to the banked oracle-machine conditions; monotonicity of the halting condition (`NHalts.mono`) therefore supplies the hypotheses of `narm_space`. That simulation produces a finite-state nondeterministic machine which halts on all choice strings at a common time, preserves the yes-answer relation, and uses at most $m(W(n)+2)+k_D(2B+1)$ space. Finally, $W(n)\leq C S(n)$, $B=C S(n)+1$, and $1\leq S(n)$ give
\[
m(W(n)+2)+k_D(2B+1)\leq (mC+2m+k_D(2C+3))S(n).
\]
The constant on the right is independent of the input. The constructed machine thus witnesses $L\in\mathrm{NSPACE}(S)$.

**Key facts.** `Complexity.LogProg.NHalts.mono`, `Complexity.LogProg.npre_of_npreS`, `Complexity.LogProg.narm_space`.
