<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_coordinateNoisePMF_signValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Sign After Coordinate Noise

**Claim.** For a sign $x$ and $ho\in[-1,1]$, the expected value of the sign obtained by retaining $x$ with probability $(1+\rho)/2$ and otherwise flipping it is $\rho x$.

**Proof.** Write $p=(1+\rho)/2$. Since the noisy sign is obtained by mapping a two-point choice (keep or flip) to either $x$ or $-x$, the expectation under the mapped distribution is the expectation of the corresponding function of that choice (`FABL.pmfExpectation_map`). The two cases contribute $p x$ and $(1-p)(-x)$, so the mean is $(2p-1)x=\rho x$. In the final equality, a sign is either $1$ or $-1$, and the identity follows in either case.

**Key facts.** `FABL.correlationKeepProbability_le_one`, `FABL.pmfExpectation_map`.
