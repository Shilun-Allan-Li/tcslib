<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.take_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a List Prefix

**Claim.** Let $\sigma$ be a finite Boolean list and let $N,s$ be natural numbers with $N\le s$. Then the prefix of $\sigma$ of length $s$ is the concatenation of its prefix of length $N$ and the prefix of length $s-N$ of the list obtained by removing its first $N$ entries.

**Proof.** Write $s=N+k$, where $k=s-N$; this decomposition follows from $N\le s$. Taking a prefix of length $N+k$ is the same as first taking a prefix of length $N$ and then taking a prefix of length $k$ from the remaining list. Substituting $k=s-N$ gives the stated identity.
