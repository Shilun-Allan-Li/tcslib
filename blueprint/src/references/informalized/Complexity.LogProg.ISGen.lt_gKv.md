<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.LogProg.ISGen.lt_gKv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Lower Bound

**Claim.** For natural numbers $E,L,s$ with $1\le E$, one has $s<2^{2EL+2Es}$.

**Proof.** First, the exponent $2EL+2Es$ is at least $s$: since $E\ge1$, its second summand $2Es$ alone is at least $s$. Also, every natural number $n$ is strictly smaller than $2^n$. Applying this to $n=2EL+2Es$ and combining the inequalities gives $s<2^{2EL+2Es}$.
