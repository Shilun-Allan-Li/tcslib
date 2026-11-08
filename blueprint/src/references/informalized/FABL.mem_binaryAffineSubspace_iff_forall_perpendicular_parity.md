<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.mem_binaryAffineSubspace_iff_forall_perpendicular_parity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Characterization of an Affine Subspace

**Claim.** A vector x belongs to the affine translate of H by a exactly when every vector γ perpendicular to H has the same dot product with x as with a.

**Proof.** For the forward direction, affine membership gives x+a ∈ H by the affine membership criterion (FABL.mem_binaryAffineSubspace_iff_add_mem). If γ is perpendicular to H, its dot product with x+a is zero (FABL.mem_perpendicularSubspace_iff). Bilinearity expands this as γ·x+γ·a=0; over 𝔽₂, additive inverses equal the original elements, so γ·x=γ·a.

Conversely, suppose γ·x=γ·a for every γ perpendicular to H. To show x+a ∈ H, use the double-perpendicular characterization: it suffices to show x+a is perpendicular to every vector γ in H⊥, since (H⊥)⊥=H (FABL.perpendicularSubspace_perpendicularSubspace). For such γ, symmetry of the dot product and bilinearity give (x+a)·γ=γ·x+γ·a=0, using the assumed equality and characteristic two. Thus x+a ∈ H, and the affine membership criterion (FABL.mem_binaryAffineSubspace_iff_add_mem) yields x in the affine translate.

**Key facts.** `FABL.mem_binaryAffineSubspace_iff_add_mem`, `FABL.mem_perpendicularSubspace_iff`, `FABL.perpendicularSubspace_perpendicularSubspace`.
