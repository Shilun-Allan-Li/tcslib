<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ReducedVandermonde.lean :: FABL.reducedVandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Sums in the Reduced Binary Vandermonde Matrix

**Claim.** For an injective choice of points in the degree-$\ell$ extension field of $\mathbb F_2$, every nonempty sum of at most $k$ columns of the reduced binary Vandermonde matrix is nonzero.

**Proof.** Suppose, toward a contradiction, that the sum of the columns indexed by a nonempty set $S$ of size at most $k$ is zero. The constant row then says that $|S|$ copies of $1$ sum to zero in $\mathbb F_2$. Mapping this equation into the extension field gives $\sum_{j\in S}1=0$. For each row indexed by an odd power $2q+1<k$, the basis-coordinate rows say that every coordinate of $\sum_{j\in S}\alpha_j^{2q+1}$ is zero. Because the basis encoding is a linear isomorphism, this implies that the field-valued sum itself is zero. Thus the constant sum and all odd-power sums vanish. The odd-moment implication (extensionField_moments_eq_zero_of_oddMoments_eq_zero) now shows that $\sum_{j\in S}\alpha_j^p=0$ for every $p<k$. These are precisely the vanishing row sums for the ordinary binary Vandermonde matrix: its constant row vanishes by the equation over $\mathbb F_2$, and each positive-power row vanishes by encoding the corresponding field moment and taking its basis coordinates. But the ordinary Vandermonde nonzero-sum theorem says that every nonempty sum of at most $k$ of its columns is nonzero (vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo), a contradiction. Therefore the reduced matrix has the required nonzero column sums.

**Key facts.** `FABL.matrixColumnSum_apply_eq_sum`, `FABL.reducedVandermondeBinaryMatrixOfPoints_oddPowerRow`, `FABL.extensionField_moments_eq_zero_of_oddMoments_eq_zero`, `FABL.vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo`.
