<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.prefixFrequency_eq_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Long prefix retains every frequency

**Claim.** If $n\le k$, filtering a set of coordinates in $\{0,\ldots,n-1\}$ to retain indices less than $k$ leaves that set unchanged.

**Proof.** Every coordinate in the given set has index less than $n$, which together with $n\le k$ implies its index is less than $k$. Thus the filter retains every element, and the filtered set equals the original set.
