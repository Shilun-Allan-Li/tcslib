<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.pow_sub_one_eq_one_of_mem_eulerLiarSubgroup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponentiation of an Euler-Liar Unit

**Claim.** For odd $N>1$, if a unit $u$ modulo $N$ satisfies the Euler–Jacobi relation, then $u^{N-1}=1$ in $\mathbb Z/N\mathbb Z$.

**Proof.** Membership in the Euler-liar subgroup says that the Jacobi symbol, viewed in $\mathbb Z/N\mathbb Z$, equals $u^{(N-1)/2}$ (`Randomized.mem_eulerLiarSubgroup`). Since $N$ is odd, $N-1=2((N-1)/2)$, so $u^{N-1}$ is the square of this Jacobi-symbol value. The Jacobi symbol is one of $-1,0,1$ (the trichotomy for the Jacobi symbol). The zero case is impossible: the membership equation would make a power of the unit $u$ equal zero, contradicting that a unit has nonzero value in $\mathbb Z/N\mathbb Z$. In either remaining case, the square of the symbol is $1$. Hence $u^{N-1}=1$.

**Key facts.** `Randomized.mem_eulerLiarSubgroup`.
