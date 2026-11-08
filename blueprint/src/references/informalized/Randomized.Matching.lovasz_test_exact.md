<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.lovasz_test_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Length Determinant Test

**Claim.** Under the stated size and injectivity assumptions, a uniformly chosen bit string of length exactly $n^2k$ produces a masked sample matrix with nonzero determinant with probability at least $1/2$.

**Proof.** Let $q$ be the determinant of the Edmonds matrix for $A$, with its variables renamed to be indexed by the $n^2$ matrix positions. A perfect matching makes this determinant polynomial nonzero: the determinant criterion for the Edmonds matrix says its determinant is nonzero exactly when the graph has a perfect matching (`det_edmondsMatrix_ne_zero_iff`). Its total degree is at most $n$ (`totalDegree_det_edmondsMatrix_le`), and renaming does not increase total degree. Evaluate this polynomial on a tuple of values indexed by matrix positions. The determinant evaluation identity (`eval_det_edmondsMatrix`) identifies the result with the determinant of the masked sample matrix.

Set $S$ to be the image in $R$ of the integers from $0$ through $2^k-1$. Injectivity makes $S$ have exactly $2^k$ elements. The assumed inequality gives $2\deg(q)\le |S|$, and $S$ is nonempty. The polynomial zero-count bound (`two_mul_card_eval_eq_zero_le`) therefore says that at most half of the tuples in $S^{n^2}$ make $q$ vanish.

It remains to connect this tuple count to the bit-string experiment. The block-counting identity (`randProb_blocks_piFinset`) expresses the probability as the fraction of tuples of block values for which the masked determinant is nonzero. Each block value ranges over $0,\ldots,2^k-1$; casting its entries into $R$ gives a bijection between these tuples and $S^{n^2}$, by the assumed injectivity. Under this bijection, the determinant condition is precisely that the evaluation of $q$ is nonzero. Thus at least half the tuples, and hence at least half the bit strings, are accepted.

**Key facts.** `Randomized.Matching.det_edmondsMatrix_ne_zero_iff`, `Randomized.Matching.totalDegree_det_edmondsMatrix_le`, `Randomized.Matching.eval_det_edmondsMatrix`, `Randomized.two_mul_card_eval_eq_zero_le`, `Randomized.randProb_blocks_piFinset`.
