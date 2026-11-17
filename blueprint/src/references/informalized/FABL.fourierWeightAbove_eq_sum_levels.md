<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.fourierWeightAbove_eq_sum_levels -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight by levels

**Claim.** For every $n,k$ and every function $f$, the Fourier weight on subsets of size greater than $k$ equals the sum of the level weights for $k+1\le j<n+1$.

**Proof.** Let $s$ be the family of subsets of $[n]$ whose sizes exceed $k$, and let $t=\{k+1,\ldots,n\}$. Every member of $s$ has size at most $n$, so its size lies in $t$. Group the sum over $s$ according to the value $j=|S|$; the finite-sum fiber decomposition says this is the sum over $j\in t$ of the sums over subsets in $s$ of size $j$. For each such $j$, one has $k<j$, so the subsets of size $j$ are all in $s$. Thus the inner sum is exactly the level-$j$ Fourier weight, giving the claimed identity.
