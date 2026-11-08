<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.exists_fknOptimalityApproximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximation to Gaussian boundary data

**Claim.** For every natural number $q$, some dimension parameter $r$ makes both the mean of the specified upper-tail indicator and its level-one Fourier weight close to their corresponding Gaussian quantities, within the stated half-mass and half-squared-density tolerances.

**Proof.** Fix $q$ and apply Proposition 5.25 at the threshold determined by $q$. Its first convergence statement says that the means of the cube indicators converge to the Gaussian upper tail at this threshold; by the defining quantile identity, this limit is the prescribed mass $1/(q+2)$. Its second convergence statement says that the level-one Fourier weights converge to the square of the Gaussian density there; the Gaussian-boundary identity identifies that density with the stated boundary quantity. Convergence to each limit implies eventual membership in any open interval around it. Choose radii equal to half the prescribed mass and half the squared boundary quantity, respectively; these radii are positive, with positivity of the boundary quantity ensuring the latter. Both inequalities therefore hold for all sufficiently large $r$. The intersection of these two eventual sets is eventual, hence nonempty, so one such $r$ satisfies both bounds.

**Key facts.** `FABL.proposition5_25`, `FABL.standardGaussianUpperTail_fknOptimalityThreshold`, `FABL.fknOptimalityGaussianBoundary_eq_density`, `FABL.fknOptimalityGaussianBoundary_pos`.
