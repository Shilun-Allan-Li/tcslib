<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.rowMajor_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row-Major Index Bound

**Claim.** If $u<n$ and $v<n$, then $un+v<n^2$.

**Proof.** From $u<n$, multiplication by the nonnegative number $n$ gives $(u+1)n\le n^2$. Expanding the left side yields $un+n\le n^2$. Since $v<n$, we have $un+v<un+n$, and therefore $un+v<n^2$.
