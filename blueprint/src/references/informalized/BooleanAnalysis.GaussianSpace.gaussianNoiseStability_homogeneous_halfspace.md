<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Halfspace.lean :: BooleanAnalysis.GaussianSpace.gaussianNoiseStability_homogeneous_halfspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability of a homogeneous Gaussian halfspace

**Claim.** If $a\in\mathbb R^n$ has squared coordinates summing to one, then for every $\rho\in[-1,1]$ the Gaussian noise stability of $x\mapsto\sigma(\sum_i a_i x_i)$ is $1-2\arccos(\rho)/\pi$.

**Proof.** Let $L(x)=\sum_i a_i x_i$, let $f(x)=\sigma(L(x))$, and use the correlated Gaussian measure to represent the pair of noisy vectors. The normalized projection theorem says that $L$ sends a standard Gaussian vector to a standard real Gaussian (\texttt{measurePreserving\_gaussianProjection}). Applying this to the two coordinate projections of the correlated pair shows that both $L(z_1)$ and $L(z_2)$ have standard Gaussian law; the second marginal fact used here is \texttt{correlatedGaussianMeasure\_snd}, while the first is \texttt{correlatedGaussianMeasure\_fst}. The correlated-integral identity then represents the noise stability as the expectation of $f(z_1)f(z_2)$ under this joint law (\texttt{integral\_correlatedGaussianMeasure}). For standard Gaussian marginals, the sign-product integral is four times the probability that both projections are nonpositive, minus one (\texttt{integral\_thresholdSign\_mul}). The projection formula for the correlated Gaussian measure identifies this quadrant probability with the real Gaussian quadrant probability at correlation $\rho$ (\texttt{correlatedGaussianMeasure\_projection}). Finally, Sheppard's formula gives that probability as $1/2-\arccos(\rho)/(2\pi)$ (\texttt{sheppard\_formula}); substituting and simplifying yields $1-2\arccos(\rho)/\pi$.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianProjection`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_fst`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_snd`, `BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure`, `BooleanAnalysis.GaussianSpace.integral_thresholdSign_mul`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_projection`, `BooleanAnalysis.ThresholdFunctions.sheppard_formula`.
