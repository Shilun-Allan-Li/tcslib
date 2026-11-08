<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ReducedVandermonde.lean :: FABL.exists_kWiseIndependentSubspace_card_le_two_mul_two_n_pow_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A small subspace with Fourier regularity

**Claim.** For integers $1\le k\le n$, there is a subspace of $\mathbb{F}_2^n$ whose associated uniform density has zero Fourier coefficients on every nonempty set of at most $k$ coordinates, and whose cardinality is at most $2(2n)^{\lfloor k/2\rfloor}$.

**Proof.** Choose $\ell=\max(1,\lceil\log_2 n\rceil)$, so $n\le2^\ell\le2n$, and inject the $n$ coordinate labels into the binary extension field of degree $\ell$. Use these field elements as points in the reduced Vandermonde construction, with row count $r=(\lfloor k/2\rfloor)\ell+1$. The construction's column-sum theorem (`reducedVandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo`) ensures that every nonempty sum of at most $k$ columns is nonzero. Let $A$ be the row span of the resulting matrix. The matrix row-span criterion (`matrixRowSpanDensity_isKWiseIndependent_iff`) translates that nonzero-sum property into the stated vanishing Fourier coefficients for the uniform density on $A$. The row span has dimension at most $r$, since it is the image of a linear map from an $r$-dimensional row space. A subspace of dimension $d$ over $\mathbb{F}_2$ has cardinality $2^d$ (`card_submodule_eq_two_pow_finrank`), hence $|A|\le2^r=2(2^\ell)^{\lfloor k/2\rfloor}\le2(2n)^{\lfloor k/2\rfloor}$.

**Key facts.** `FABL.reducedVandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo`, `FABL.matrixRowSpanDensity_isKWiseIndependent_iff`, `FABL.card_submodule_eq_two_pow_finrank`.
