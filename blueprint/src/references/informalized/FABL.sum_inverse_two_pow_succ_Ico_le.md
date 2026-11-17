<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.sum_inverse_two_pow_succ_Ico_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Geometric Sum Bound

**Claim.** For nonnegative integers $m,n$, the sum of $2^{-(k+1)}$ over $m\le k<n$ is at most $2^{-m}$, with an empty sum when $n\le m$.

**Proof.** Reindex the interval by writing $k=m+r$, where $0\le r<n-m$. Then each summand is $2^{-m}(1/2)(1/2)^r$, so the sum equals $2^{-m}(1/2)\sum_{r<n-m}(1/2)^r$. The finite geometric sum is at most $2$, hence the expression is at most $2^{-m}$. This also covers the empty interval, whose sum is zero.
