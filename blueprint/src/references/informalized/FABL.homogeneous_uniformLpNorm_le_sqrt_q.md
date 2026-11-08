<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.homogeneous_uniformLpNorm_le_sqrt_q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneous norm bound from degree control

**Claim.** A Fourier-homogeneous function of degree $k$ satisfies the stated bound $\|f\|_{2r}\le \sqrt{2r}^{\,k}\|f\|_2$.

**Proof.** Homogeneity implies that the Fourier degree of $f$ is at most $k$ (FABL.isFourierHomogeneous_fourierDegree_le). Apply the low-degree norm estimate (FABL.homogeneous_uniformLpNorm_le_sqrt_two_mul) with this degree bound and the given positive integer $r`; it gives exactly the asserted inequality.

**Key facts.** `FABL.isFourierHomogeneous_fourierDegree_le`, `FABL.homogeneous_uniformLpNorm_le_sqrt_two_mul`.
