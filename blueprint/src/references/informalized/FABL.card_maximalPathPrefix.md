<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.card_maximalPathPrefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of a permutation path prefix

**Claim.** For a permutation $\pi$ of $[n]$ and $k\in\{0,\ldots,n\}$, the set of indices $i$ for which $\pi(i)<k$ has cardinality $k$.

**Proof.** Map each index in the set to its value under $\pi$, regarded as an element of $[k]$. This map is injective because $\pi$ is a permutation. It is also surjective: for any value in $[k]$, its preimage under $\pi$ belongs to the set, since that value is less than $k$. Thus the set is in bijection with $[k]$ and has cardinality $k$.
