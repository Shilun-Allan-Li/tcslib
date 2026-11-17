<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.mem_binaryAffineSubspace_iff_add_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Subspace Membership Criterion

**Claim.** For a linear subspace H of 𝔽₂^n and vectors a,x, x belongs to the affine translate of H by a exactly when x+a belongs to H.

**Proof.** Membership in the affine translate of H by a is equivalent to x−a ∈ H. In characteristic two, every vector is its own negative, so −a=a and x−a=x+a. Substitution gives the stated equivalence.
