<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.maximalPathPrefix_mul_transport_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation transport of prefixes

**Claim.** For equal-cardinality subsets $A,B\subseteq\{0,\ldots,n-1\}$, the prefix set determined by $\pi$ composed with the inverse of the transport permutation equals $B$ exactly when the prefix set determined by $\pi$ equals $A$.

**Proof.** Let $\tau$ be the permutation transporting $A$ to $B$. For the forward implication, fix an index $j$ and test membership of $\tau(j)$ in the assumed prefix-set equality. This says that $(\pi\circ\tau^{-1})(\tau(j))<k$ exactly when $\tau(j)\in B$. Since the two permutations cancel at $j$, and the transport property says $\tau(j)\in B$ exactly when $j\in A$, this is equivalent to $\pi(j)<k$ exactly when $j\in A$. Hence the prefix set for $\pi$ is $A$. Conversely, test the assumed equality of the prefix set for $\pi$ with the index $\tau^{-1}(i)$. It gives $\pi(\tau^{-1}(i))<k$ exactly when $\tau^{-1}(i)\in A$. The transport property, applied to $\tau^{-1}(i)$, makes the latter equivalent to $i\in B$. Meanwhile $(\pi\circ\tau^{-1})(i)=\pi(\tau^{-1}(i))$, so this is precisely membership of $i$ in the transported prefix set, proving that it equals $B$.

**Key facts.** `FABL.mem_finsetTransportPerm_iff`.
