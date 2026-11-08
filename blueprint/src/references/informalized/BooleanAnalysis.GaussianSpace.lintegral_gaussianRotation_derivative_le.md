<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.lintegral_gaussianRotation_derivative_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative bound from Gaussian rotations

**Claim.** Under the stated differentiability and rotation-variation bound, the product Gaussian integral of $|L(X)Y|$ is at most $C$.

**Proof.** Set $t_k=1/(k+1)$ and let $q_k(X,Y)$ be the nonnegative extended-real value obtained by applying the rotation difference quotient at angle $t_k$. Since $t_k$ tends to zero through positive values, differentiability gives pointwise convergence of the quotient to $|L(X)Y|$ (the Gaussian rotation difference-quotient limit, `gaussianRotation_difference_quotient_tendsto`). Continuity of the map taking a nonnegative real to its extended-real value gives convergence of $q_k$ to $|L(X)Y|$ in this same sense. Thus the desired integral equals the integral of the pointwise limit inferior. Fatou's lemma bounds it by the limit inferior of the integrals of $q_k$. Each of those integrals is at most $C$ by the assumed rotation bound, so their limit inferior is at most $C$ as well.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianRotation_difference_quotient_tendsto`.
