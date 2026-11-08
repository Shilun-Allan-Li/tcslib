<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgut_coordinateJunta_close -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate junta approximation

**Claim.** If the Fourier weight above degree $k$ is at most $\epsilon$, the coordinate junta approximation formed from coordinates with pivotal probability at least the threshold differs from $f$ on at most an $\epsilon$ fraction of inputs.

**Proof.** Let $J$ be the threshold-influential coordinates. The small-family concentration result (`improvedFriedgut_small_spectrum_concentrated`) says that the Fourier weight outside the family of sets contained in $J$ and of size at most $k$ is at most $2\epsilon$. In particular, the family of all sets contained in $J$ contains that small family, so the weight outside the larger family is no greater: Fourier weight outside a family decreases when the family grows (`fourierWeightOutside_antitone`). On the other hand, the coordinate junta approximation bound (`two_mul_relativeHammingDist_coordinateJuntaApproximation_le`) says that twice its relative Hamming distance from $f$ is at most the Fourier weight outside the sets contained in $J$. Combining these inequalities gives twice the distance at most $2\epsilon$, hence the distance is at most $\epsilon$.

**Key facts.** `FABL.improvedFriedgut_small_spectrum_concentrated`, `FABL.fourierWeightOutside_antitone`, `FABL.two_mul_relativeHammingDist_coordinateJuntaApproximation_le`.
