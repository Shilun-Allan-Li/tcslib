<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.lintegral_gaussianGradient_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian gradient bound from rotation

**Claim.** A uniform bound on the extended Gaussian integrals of the scaled rotational differences of a differentiable function implies the same bound on the Gaussian integral of the Euclidean norm of its gradient.

**Proof.** Put $c=\sqrt{\pi/2}$, which is nonnegative, and replace $f$ by $cf$. Its derivative at $x$ is $cL(x)$. The assumed rotational-difference bound is precisely the unscaled bound needed for the derivative estimate, because $|c a|=c|a|$; applying that estimate yields an upper bound $C$ for the extended integral of $|cL(z_1)(z_2)|$ (\texttt{BooleanAnalysis.GaussianSpace.lintegral_gaussianRotation_derivative_le}). Pulling out the nonnegative factor $c$ and applying the Gaussian linear-functional family identity expresses this integral as the desired gradient-norm integral times $c\,2\varphi(0)$. Gaussian surface normalization gives $c\,2\varphi(0)=1$ (\texttt{BooleanAnalysis.GaussianSpace.gaussian_surface_normalization}), so the desired integral is at most $C$.

**Key facts.** `BooleanAnalysis.GaussianSpace.lintegral_gaussianRotation_derivative_le`, `BooleanAnalysis.GaussianSpace.lintegral_gaussianLinearMap_family`, `BooleanAnalysis.GaussianSpace.gaussian_surface_normalization`.
