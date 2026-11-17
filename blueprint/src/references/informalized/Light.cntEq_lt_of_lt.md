<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntEq_lt_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Increase in a Prefix Count

**Claim.** If $j<N$, then the number of indices below $N$ at which $kf$ equals $kf(j)$ is strictly greater than the number of such indices below $j$.

**Proof.** Count the indices satisfying $kf(i)=kf(j)$. Extending the prefix from indices below $j$ to indices below $N$ strictly increases the count whenever $j<N$: the larger prefix includes the additional index $j$, which satisfies the counted property. This is the strict monotonicity of the natural-number count over prefixes.
