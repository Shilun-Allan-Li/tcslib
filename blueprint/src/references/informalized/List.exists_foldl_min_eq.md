<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.exists_foldl_min_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Finite Minimum Is Attained

**Claim.** For a linearly ordered type, the running minimum of $f(0),f(1),\ldots,f(m)$ equals $f(k)$ for some $k\le m$.

**Proof.** Proceed by induction on $m$. When $m=0$, the running minimum is $f(0)$, so choose $k=0$. For the successor step, the induction hypothesis gives an index $k\le m$ whose value is the running minimum through $f(m)$. Appending the next term makes the new running minimum the minimum of $f(k)$ and $f(m+1)$. By totality of the order, either $f(k)\le f(m+1)$, in which case the minimum is $f(k)$ and the same index works, or $f(m+1)\le f(k)$, in which case the minimum is $f(m+1)$ and choose the new index $m+1$. In either case the chosen index is at most $m+1$.
