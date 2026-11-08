<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.card_firstCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the initial coordinate set

**Claim.** If $k\leq n$, then the set of the first $k$ coordinates among $n$ coordinates has cardinality $k$.

**Proof.** The set consists of indices in $\mathrm{Fin}\,n$ whose values are less than $k$. The number of such indices is $\min(n,k)$; since $k\leq n$, this minimum equals $k$.
