<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.profile_sq_difference_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Squared-profile difference bound

**Claim.** If $b\ge0$, $a-b>0$, $a+b<1$, and $a\le1/2$, then the squared difference of the Gaussian profiles at $a+b$ and $a-b$ satisfies the stated bound.

**Proof.** If $b=0$, the two profile values coincide and both sides of the inequality are zero. Suppose henceforth that $b>0$. On $[0,b]$, the function $g(x)=I(a+x)^2-I(a-x)^2$ is concave (`concaveOn_profile_sq_difference`). Its derivative at zero is $-4I(a)Q(a)$: this follows by applying the derivative formula for a pair of shifted squared profiles (`hasDerivAt_profile_sq_pair`) with the second coefficient $-1$. Concavity bounds the secant slope from $0$ to $b$ by this derivative at zero. Since $b>0$, this gives $g(b)\le -4I(a)Q(a)b$.

The Gaussian profile is nonnegative, so the squared-profile difference $g(b)$ is nonnegative; the endpoint assumptions also ensure the shifted probabilities stay in $(0,1)$ (`shifted_probabilities_mem`). Moreover, $I(a+b)\le I(a-b)$: the profile is monotone on the relevant lower half of the probability range, as supplied by `gaussianIsoperimetric_le_of_le_of_add_le_one`, and $a\le1/2$ ensures the required ordering and sum condition. These facts, together with the secant bound, yield the claimed squared inequality by algebra. Positivity of the Gaussian density (`standardGaussianPDF_pos`) supplies the nonnegativity used in this final comparison.

**Key facts.** `BooleanAnalysis.GaussianSpace.concaveOn_profile_sq_difference`, `BooleanAnalysis.GaussianSpace.hasDerivAt_profile_sq_pair`, `BooleanAnalysis.GaussianSpace.shifted_probabilities_mem`, `BooleanAnalysis.ThresholdFunctions.gaussianIsoperimetric_le_of_le_of_add_le_one`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.

**Caveat.** The final nonlinear-algebra step combines the secant estimate, profile ordering, and positivity to obtain the constant 16 bound; the proof source closes this with polynomial inequalities rather than displaying the intermediate rearrangement.
