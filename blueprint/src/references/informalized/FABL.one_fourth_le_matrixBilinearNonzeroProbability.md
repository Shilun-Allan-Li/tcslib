<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.one_fourth_le_matrixBilinearNonzeroProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero bilinear form probability

**Claim.** For a nonzero matrix over $\mathbb F_2$, independent uniform vectors satisfy $\mathbb P(x^{\mathsf T}Dy\ne0)\ge1/4$.

**Proof.** First condition on the vector $y$. The bilinear form is nonzero precisely when $x$ has nonzero dot product with $Dy$. Averaging over uniform $x$ gives probability $1/2$ whenever $Dy\ne0$, and zero otherwise; thus the overall probability is half the probability that $Dy\ne0$ (`matrixBilinearNonzeroProbability_eq`). Since $D$ is nonzero, its image on a uniform vector is nonzero with probability at least $1/2$ (`one_half_le_uniformProbability_mulVec_ne_zero`). Multiplying these bounds gives the claimed $1/4$.

**Key facts.** `FABL.matrixBilinearNonzeroProbability_eq`, `FABL.one_half_le_uniformProbability_mulVec_ne_zero`.
