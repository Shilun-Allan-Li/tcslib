<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierEstimator.lean :: FABL.smallBiasFourierEstimate_eq_uniformPushforward_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Fourier estimate as an expectation

**Claim.** The empirical average of $f$ times the sign monomial indexed by $U$ over the encoded sample equals the expectation of that same function under the density obtained by pushing forward the uniform distribution on the sample points.

**Proof.** Apply the expectation formula for a pushforward density: its expectation of a function on the binary cube is the uniform expectation of that function evaluated at the sample point (the fact that expectation under `uniformPushforward` equals the sample expectation, `FABL.ProbabilityDensity.expectation_uniformPushforward`). The uniform expectation over the finite type `Fin m` is its sum divided by $m$. Substituting the function $x\mapsto f(\mathrm{binaryCubeSignEquiv}(n,x))\,\mathrm{monomial}(U,\mathrm{binaryCubeSignEquiv}(n,x))$ gives exactly the defining sum for the empirical estimate, with the same divisor $m$.

**Key facts.** `FABL.ProbabilityDensity.expectation_uniformPushforward`.
