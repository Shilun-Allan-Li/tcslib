<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.LogProg.arm_decides_pspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-space register simulation

**Claim.** If the register program has a correct halting run, its side conditions hold, its register words have polynomially bounded length, and its oracle languages are in polynomial space, then $L$ is decidable in polynomial space.

**Proof.** For each oracle language $A_j$, membership in polynomial space supplies an exponent $e_j$, a coefficient $c_j$, and a decider using at most $c_j(v^{e_j}+1)$ space on inputs of length $v$. Let $e_* = \sum_j e_j$, so $e_j\le e_*$, and choose a common polynomial exponent $E=(c_0+1)(e_*+1)$. Set $A_0=2+2m+2mC_0$ and choose a coefficient $C$ large enough to cover both the program's registers and every oracle's coefficient $c_j(A_0^{e_j}+1)$.

For input length $n$, write $P=(n+1)^{c_0+1}$. The hypothesis on register-word lengths, together with the bound on the length of the input, implies that any virtual input to an oracle call has length $v\le A_0P$. Also $n+1\ge1$, so increasing an exponent can only increase its power. Since $(c_0+1)e_j\le E$, we obtain
\[
v^{e_j}+1\le (A_0^{e_j}+1)(n+1)^E.
\]
Consequently oracle $j$ uses at most $c_j(A_0^{e_j}+1)(n+1)^E\le C(n+1)^E$ space on such a call. The register simulation theorem (`arm_decides_space`), with space scale $(n+1)^E$ and the polynomial register-word bound, now gives $L\in\mathrm{SPACE}(n\mapsto(n+1)^E)$. Finally, this polynomial space class is contained in polynomial space as defined in the statement (`SPACE_succ_pow_subset_PSPACE`), proving $L\in\mathrm{PSPACE}$.

**Key facts.** `Complexity.LogProg.arm_decides_space`, `Complexity.SPACE_succ_pow_subset_PSPACE`.
