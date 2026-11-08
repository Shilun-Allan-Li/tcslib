<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.subsetDensity_submodule_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subspace density Fourier expansion

**Claim.** As functions on the Boolean cube, the probability density of a subspace equals the sum of the characters indexed by its perpendicular subspace.

**Proof.** Two functions are equal once they agree at every point. For an arbitrary point, the pointwise density identity identifies the subspace density with the perpendicular-subspace character sum (\(`FABL.subsetDensity_submodule_apply`\)). Since the point was arbitrary, the functions agree everywhere.

**Key facts.** `FABL.subsetDensity_submodule_apply`.
