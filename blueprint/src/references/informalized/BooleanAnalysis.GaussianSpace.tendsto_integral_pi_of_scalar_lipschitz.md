<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedBlocks.lean :: BooleanAnalysis.GaussianSpace.tendsto_integral_pi_of_scalar_lipschitz -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product convergence from scalar tests

**Claim.** If integrals of every Lipschitz real test function converge from probability measures $\mu_m$ to $\nu$, then integrals of every bounded continuous function on $\mathbb R^n$ converge from the product measures $\mu_m^{\otimes n}$ to $\nu^{\otimes n}$.

**Proof.** The assumed convergence for all nonnegative Lipschitz constants implies convergence for every Lipschitz test function, since each such function has some finite Lipschitz constant. The characterization of weak convergence of probability measures by convergence of Lipschitz-test integrals therefore gives $\mu_m\to\nu$ weakly. Coordinatewise application of this convergence, together with continuity of the product-measure map on probability measures (ProbabilityMeasure.continuous_pi), yields weak convergence of the $n$-fold product measures. Finally, weak convergence gives convergence of integrals against every bounded continuous function, as required.
