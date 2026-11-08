<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/PairwiseIndependence.lean :: FABL.pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Column Sums for Sets of Size at Most Two

**Claim.** For the matrix whose columns enumerate nonzero vectors in $\mathbb F_2^\ell$, every nonempty set of at most two columns has nonzero sum.

**Proof.** Take a nonempty set of columns with cardinality at most two. Its cardinality is either one or two. If it is one, the column-sum identity (FABL.matrixColumnSum_pairwiseIndependentMatrix) identifies the sum with its sole column, which is nonzero by the nonvanishing of every enumerated vector (FABL.pairwiseIndependentColumn_ne_zero). If it is two, write the set as distinct indices $i,j$. The same column-sum identity makes its sum the sum of the two corresponding vectors. If that sum were zero, then adding the vector at $j$ to both sides and using $v+v=0$ in characteristic two would give equality of the vectors at $i$ and $j$. Injectivity of the enumeration (FABL.pairwiseIndependentColumn_injective) would then force $i=j$, contradicting their distinctness. Hence the two-column sum is nonzero as well.

**Key facts.** `FABL.matrixColumnSum_pairwiseIndependentMatrix`, `FABL.pairwiseIndependentColumn_ne_zero`, `FABL.pairwiseIndependentColumn_injective`.

**Caveat.** The supplied informal statement describes a different proposition; this account follows the formal theorem and its proof source.
