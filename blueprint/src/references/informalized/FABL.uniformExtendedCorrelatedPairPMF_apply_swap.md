<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.uniformExtendedCorrelatedPairPMF_apply_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the joint law

**Claim.** The joint law assigns the same probability to $(x,y)$ and $(y,x)$.

**Proof.** Apply the point mass formula for the joint law to each ordered pair. The resulting expressions are the uniform mass of the first coordinate times its conditional noise mass at the second coordinate. The uniform masses at $x$ and $y$ are equal, since the distribution is uniform, and the conditional noise masses in the two directions agree by symmetry of the coordinate noise law ( `uniformExtendedCoordinateNoisePMF_apply_comm`). Hence the two joint point masses are equal.

**Key facts.** `FABL.uniformExtendedCorrelatedPairPMF_apply`, `FABL.uniformExtendedCoordinateNoisePMF_apply_comm`.
