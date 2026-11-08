<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.normalizedRestrictedWalshVector_orthonormal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthonormality of Restricted Walsh Vectors

**Claim.** If a finite nonempty sample space carries a $k$-wise independent multiset of sign vectors, then the normalized restricted Walsh vectors indexed by a family whose pairwise unions have size at most $k$ are orthonormal.

**Proof.** Fix two members $S,T$ of the indexing family. By the moment identity for $k$-wise independence (`FABL.IsKWiseIndependentMultiset.expect_monomial_mul`), the expected product of their monomials is $1$ when $S=T$ and $0$ otherwise, since the union of the two sets has size at most $k$. Converting this expectation over the finite nonempty sample space into a sum shows that the sum of the monomial products is the cardinality of the sample space times this same indicator. The inner product of the two normalized vectors is the sum of those products multiplied by $(\sqrt{|\Omega|})^{-2}$: this follows by expanding the Euclidean inner product and factoring out the common normalization. If $S=T$, the identity $(\sqrt{|\Omega|})^2=|\Omega|$ makes the inner product $1$; if $S\ne T$, the monomial-product sum is zero, so the inner product is zero. These are precisely the orthonormality relations.

**Key facts.** `FABL.IsKWiseIndependentMultiset.expect_monomial_mul`.
