<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.concaveOn_profile_sq_difference -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concavity of a squared profile difference

**Claim.** If $b\ge0$, $a-b>0$, $a+b<1$, and $a\le\tfrac12$, then $x\mapsto U(a+x)^2-U(a-x)^2$ is concave on $[0,b]$, where $U$ is the Gaussian isoperimetric profile.

**Proof.** For every $x\in[0,b]$, the bounds on $a$ and $b$ ensure that both shifted probabilities $a+x$ and $a-x$ lie strictly between $0$ and $1$ (shifted_probabilities_mem). Apply the second-derivative criterion for concavity on the interval. The first derivative of the squared-profile pair is given by the profile-quantile formula (hasDerivAt_profile_sq_pair), with coefficient $k=-1$; differentiating this formula gives the second derivative $2\bigl(q_{a+x}^2-q_{a-x}^2igr)$ (hasDerivAt_profile_sq_pair_derivative). For an interior point $x$, one has $a-x\le a+x$ and $(a-x)+(a+x)=2a\le1$. Both probabilities are in $(0,1)$, so the quantile-square comparison gives $q_{a+x}^2\le q_{a-x}^2$ (standardGaussianQuantile_sq_le). Hence the second derivative is nonpositive. The first-derivative formula also supplies the required differentiability on the interior, and the profile is continuous there; the derivative criterion yields concavity on the whole closed interval.

**Key facts.** `BooleanAnalysis.GaussianSpace.shifted_probabilities_mem`, `BooleanAnalysis.GaussianSpace.hasDerivAt_profile_sq_pair`, `BooleanAnalysis.GaussianSpace.hasDerivAt_profile_sq_pair_derivative`, `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_sq_le`.
