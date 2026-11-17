<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arSpaceBlock_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intersection of neighboring block intervals

**Claim.** For every natural number $N$ and integers $p,q$ with $|p-q|\le 1$, the two block intervals indexed by $p$ and $q$ intersect.

**Proof.** The absolute value bound gives both $p-q\le 1$ and $q-p\le 1$. Since $N+1$ is nonnegative, multiplication by it preserves these inequalities. If $p\le q$, use the left endpoint of the block indexed by $q$, namely $(N+1)q$. It is at least the left endpoint $(N+1)p$ of the other block, and $q\le p+1$ ensures it is no greater than $(N+1)p+N+1$. It is also the left endpoint of its own block. If $q<p$, the same argument with the roles reversed shows that $(N+1)p$ belongs to both intervals. Hence their intersection is nonempty.
