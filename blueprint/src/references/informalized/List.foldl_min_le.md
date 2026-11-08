<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.foldl_min_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for a Finite Running Minimum

**Claim.** For a linearly ordered type, the running minimum of $f(0),f(1),\ldots,f(m)$ is at most $f(k)$ for every $k\le m$.

**Proof.** Induct on $m$. If $m=0$, the condition $k\le0$ forces $k=0$, and the running minimum equals $f(0)$. For the successor step, the new running minimum is the minimum of the previous running minimum and $f(m+1)$. If $k\le m$, this new minimum is at most the previous one, which by induction is at most $f(k)$. In the remaining case, $k=m+1$, and the new minimum is at most $f(m+1)=f(k)$.
