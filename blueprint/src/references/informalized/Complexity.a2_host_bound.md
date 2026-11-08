<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_host_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Host ledger bound

**Claim.** For natural numbers $Q,B,r,A,d,n,T$ with $T\le B(n+Q+1)^r$, the displayed sum is at most $(B+A+5)(n+Q+1)^{r+d+1}$.

**Proof.** Set $m=n+Q+1$, which is positive. Since $r+d+1$ is at least both $r$ and $d$, monotonicity of powers for base $m\ge1$ gives $T\le Bm^{r+d+1}$ and $Am^d\le Am^{r+d+1}$. Also $m\le m^{r+d+1}$, while direct arithmetic gives $3n+Q+5\le5m$. Thus $3n+Q+5\le5m^{r+d+1}$. The left side of the claimed inequality rearranges to $T+Am^d+3n+Q+5$, so adding these three bounds proves it.
