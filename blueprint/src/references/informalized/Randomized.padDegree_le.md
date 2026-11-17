<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkPad.lean :: Randomized.padDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Degree Bound

**Claim.** For every positive natural number $n$, the power of $2$ whose exponent is the binary length of $n$ is at most $2n$.

**Proof.** By positivity of $n$, its binary length $\operatorname{Nat.size}(n)$ is positive. The defining bound for binary size gives $2^{\operatorname{Nat.size}(n)-1}\le n$: otherwise the size would be at most $\operatorname{Nat.size}(n)-1$, contradicting its value. Since the size is positive, $2^{\operatorname{Nat.size}(n)}=2\cdot2^{\operatorname{Nat.size}(n)-1}$. Multiplying the preceding inequality by $2$ yields the desired bound.
