<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/FiniteFields.lean :: FABL.eq_zero_of_vandermonde_mulVec_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Kernel of a Vandermonde matrix

**Claim.** For pairwise distinct elements of a field, the Vandermonde matrix has trivial kernel: if it sends a vector to zero, that vector is zero.

**Proof.** Injectivity of $\alpha$ says its entries are pairwise distinct. The Vandermonde determinant is nonzero for pairwise distinct entries (`det_vandermonde_ne_zero_of_injective`), so the matrix is invertible. An invertible matrix has trivial kernel; applying this fact to the assumed matrix-vector equation yields $v=0$.

**Key facts.** `FABL.det_vandermonde_ne_zero_of_injective`.
