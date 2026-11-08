<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.binaryAffineSubspace_direction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Direction of a Translated Subspace

**Claim.** For a linear subspace $H$ and vector $a$, the direction subspace of the affine translate $a+H$ is $H$.

**Proof.** The affine translate is defined as the affine subspace obtained by translating $H$ by $a$. By the direction formula for a translated affine subspace (`AffineSubspace.direction_mk'`), its direction is exactly $H$.
