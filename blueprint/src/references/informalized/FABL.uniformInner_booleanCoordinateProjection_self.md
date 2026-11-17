<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.uniformInner_booleanCoordinateProjection_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection norm and Fourier weight

**Claim.** For a Boolean function $f$ and coordinate set $J$, the squared uniform norm of its projection onto $J$ is one minus the sum of squared Fourier coefficients indexed by sets not contained in $J$.

**Proof.** Let the inside indices be those subsets $S$ with $S\subseteq J$, and let the outside indices be the remaining subsets. By Plancherel, the squared norm of the projection is the sum of the squares of its Fourier coefficients. The projection's Fourier coefficients equal those of $f$ on inside indices and vanish on outside indices (`fourierCoeff_booleanCoordinateProjection`); hence its squared norm is the sum over inside indices. The total sum of squared Fourier coefficients of the Boolean function is $1$ (`sum_sq_fourierCoeff_eq_one`). Partitioning that total into inside and outside sums shows that the inside sum is $1$ minus the outside sum, which is precisely the claimed Fourier weight outside $J$.

**Key facts.** `FABL.plancherel`, `FABL.fourierCoeff_booleanCoordinateProjection`, `FABL.sum_sq_fourierCoeff_eq_one`.
