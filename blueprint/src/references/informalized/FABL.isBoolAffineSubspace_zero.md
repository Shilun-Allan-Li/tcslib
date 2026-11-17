<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.isBoolAffineSubspace_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Membership in Dimension Zero

**Claim.** In the zero-dimensional binary vector space, every Boolean assignment belongs, after conversion to a binary vector, to the affine subspace obtained by translating any linear subspace by any vector.

**Proof.** By the characterization of membership in a translated subspace, it suffices to show that the converted assignment plus the translating vector lies in the linear subspace ( `mem_binaryAffineSubspace_iff_add_mem`). The zero-dimensional vector space has only one element, so this sum is the zero vector. Every submodule contains zero, proving the claim.

**Key facts.** `FABL.mem_binaryAffineSubspace_iff_add_mem`.
