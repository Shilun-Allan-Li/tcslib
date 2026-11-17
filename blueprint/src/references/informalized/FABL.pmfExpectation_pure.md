<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_pure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Point Mass

**Claim.** For a finite set $\Omega$, the expectation of $\mathrm{payoff}$ under the probability mass function concentrated at $\mathrm{point}$ is $\mathrm{payoff}(\mathrm{point})$.

**Proof.** In the finite sum defining expectation, the point mass assigns probability one to $\mathrm{point}$ and zero to every other element. Thus every term except the one at $\mathrm{point}$ vanishes, and the remaining term is $\mathrm{payoff}(\mathrm{point})$.
