<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.deltaRandomIntersectionTail_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Intersection Tail

**Claim.** For $0\le\delta\le1$, the weighted sum of indicators that a random subset intersects $U$ in at least $k$ elements is nonnegative.

**Proof.** Expand the intersection tail as a finite sum over all subsets $J$. Each summand is the product of the random subset weight and an indicator, which is either $0$ or $1$. The weight is nonnegative by the nonnegativity of the random subset weight (\texttt{deltaRandomSubsetWeight\_nonneg}); hence each summand is nonnegative. A finite sum of nonnegative terms is nonnegative.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`.
