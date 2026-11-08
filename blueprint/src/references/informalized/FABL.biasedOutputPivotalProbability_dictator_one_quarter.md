<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedOutputPivotalProbability_dictator_one_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Pivotal Probability

**Claim.** For the one-dimensional dictator and the bias parameter $p=1/4$, the probability that its output is $-1$ and its sole coordinate is pivotal is $1/4$.

**Proof.** First identify the homogeneous product-distribution pivotal probability with its heterogeneous-coordinate version (\texttt{FABL.heterogeneousOutputPivotalProbability_const}). For a monotone function, the latter equals the biased sign mass of the specified output multiplied by the mean of the discrete derivative (\texttt{FABL.heterogeneousOutputPivotalProbability_eq_mass_mul_derivativeMean_of_monotone}); the dictator is monotone (\texttt{FABL.dictator_monotone}). At $p=1/4$, the mass of output $-1$ is $1/4$. The dictator's discrete derivative in its only coordinate is identically $1$: its values at coordinate $1$ and $-1$ are respectively $1$ and $-1$, so their difference divided by two is $1$ (\texttt{FABL.discreteDerivative_apply}). The mean of this constant derivative is $1$ (\texttt{FABL.pmfExpectation_const}). Multiplying gives $1/4$.

**Key facts.** `FABL.heterogeneousOutputPivotalProbability_const`, `FABL.heterogeneousOutputPivotalProbability_eq_mass_mul_derivativeMean_of_monotone`, `FABL.dictator_monotone`, `FABL.discreteDerivative_apply`, `FABL.pmfExpectation_const`.
