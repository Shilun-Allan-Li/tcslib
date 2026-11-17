<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.finrank_perpendicularSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension of the perpendicular subspace

**Claim.** For a subspace $A$ of $\mathbb F_2^n$, its perpendicular subspace has dimension $n-\dim A$.

**Proof.** The dot-product bilinear form on $\mathbb F_2^n$ is nondegenerate (`FABL.f₂DotProductBilin_nondegenerate`). For a nondegenerate bilinear form on a finite-dimensional space, the orthogonal complement of a subspace has dimension equal to the ambient dimension minus the subspace dimension. Applying this fact to $A$ gives $\dim A^\perp=n-\dim A$; the ambient space $\mathbb F_2^n$ has dimension $n$.

**Key facts.** `FABL.f₂DotProductBilin_nondegenerate`.
