<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.theorem9_28_close_to_coordinateJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Junta Approximation

**Claim.** Under the stated positive-influence and spectral-concentration hypotheses, the function is within relative Hamming distance ε of the coordinate junta obtained by thresholding its projection onto the influential coordinates.

**Proof.** Let $J$ be the set of coordinates whose influence is at least the specified threshold. The small-spectrum concentration result ( `theorem9_28_small_spectrum_concentrated`) says that the Fourier weight outside the small family of sets is at most $2\varepsilon$. Every set in that family is contained in $J$, so the family is included in the sets supported inside $J$. Since Fourier weight outside a family decreases when the family is enlarged ( `fourierWeightOutside_antitone`), the Fourier weight outside the sets supported inside $J$ is also at most $2\varepsilon$. The coordinate-junta rounding bound ( `two_mul_relativeHammingDist_coordinateJuntaApproximation_le`) says that twice the relative Hamming distance to the thresholded coordinate projection on $J$ is at most this outside Fourier weight. Combining the two bounds gives relative Hamming distance at most $\varepsilon$.

**Key facts.** `FABL.theorem9_28_small_spectrum_concentrated`, `FABL.fourierWeightOutside_antitone`, `FABL.two_mul_relativeHammingDist_coordinateJuntaApproximation_le`.
