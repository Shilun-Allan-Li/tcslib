<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/PairwiseIndependence.lean :: FABL.exists_pairwiseIndependentSubspace_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small Subspace with Fourier Regularity

**Claim.** For every positive $n$, there is a subspace whose associated density has vanishing nonempty Fourier coefficients of degree at most two, and whose cardinality is at most $4n$.

**Proof.** Choose the row count $\ell$ prescribed by the pairwise-independent construction. Its defining bound ensures $n\le 2^\ell-1$ (`n_le_two_pow_pairwiseIndependentRowCount_sub_one`), so form the corresponding matrix $H$ and let $A$ be its row span. The matrix has no nonzero column sum from any nonempty set of at most two columns (`pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo`). The characterization of $k$-wise independence for a row-span density translates this property into vanishing Fourier coefficients on all such sets (`matrixRowSpanDensity_isKWiseIndependent_iff`), giving the required regularity for the density associated with $A$. To bound its size, the rank of the row span is at most the number $\ell$ of rows, since it is the range of the matrix's row-span map into an $\ell$-dimensional space. A subspace over $\mathbb F_2$ has cardinality $2^{\operatorname{rank}(A)}$ (`card_submodule_eq_two_pow_finrank`), hence $|A|\le 2^\ell$. The chosen row-count bound gives $2^\ell\le 4n$ (`two_pow_pairwiseIndependentRowCount_le_four_mul`), completing the claim.

**Key facts.** `FABL.n_le_two_pow_pairwiseIndependentRowCount_sub_one`, `FABL.pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo`, `FABL.matrixRowSpanDensity_isKWiseIndependent_iff`, `FABL.card_submodule_eq_two_pow_finrank`, `FABL.two_pow_pairwiseIndependentRowCount_le_four_mul`.
