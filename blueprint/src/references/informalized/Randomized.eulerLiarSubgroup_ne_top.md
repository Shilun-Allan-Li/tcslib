<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.eulerLiarSubgroup_ne_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Euler-liar subgroup is proper

**Claim.** For nonzero odd composite $N>1$, the subgroup of units modulo $N$ whose Jacobi symbol equals their $(N-1)/2$-th power is a proper subgroup.

**Proof.** Separate the two possibilities for the prime factorization of $N$. If some prime square divides $N$, the square-divisor witness theorem supplies a unit outside the Euler-liar subgroup (`exists_not_mem_of_sq_dvd`). If no prime square divides $N$, then every prime $p$ satisfies $p^2\nmid N$; since $N$ is odd and composite, the square-free witness theorem again supplies a unit outside the subgroup (`exists_not_mem_of_not_sq_dvd`). In either case choose such a unit $u$. If the subgroup were the whole unit group, then $u$ would belong to it, contradicting its choice. Therefore the subgroup is proper.

**Key facts.** `Randomized.exists_not_mem_of_sq_dvd`, `Randomized.exists_not_mem_of_not_sq_dvd`.
