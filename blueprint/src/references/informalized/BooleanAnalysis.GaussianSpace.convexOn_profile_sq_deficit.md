<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.convexOn_profile_sq_deficit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of the Corrected Profile Sum

**Claim.** For $a,b\in\mathbb R$ with $a-b>0$ and $a+b<1$, the function $x\mapsto U(a+x)^2+U(a-x)^2+2(1-Q(a)^2)x^2$ is convex on $[-b,b]$.

**Proof.** On the interval $[-b,b]$, the hypotheses imply $0<a+x<1$ and $0<a-x<1$. The proof first differentiates the displayed function: the derivative of the two profile-square terms is given by the paired profile derivative formula ($\texttt{hasDerivAt\_profile\_sq\_pair}$), and the quadratic correction contributes its ordinary derivative. It then differentiates this first derivative. The resulting second derivative is $2\bigl(Q(a+x)^2+Q(a-x)^2-2Q(a)^2\bigr)$. By convexity of the squared Gaussian quantile on $(0,1)$ ($\texttt{convexOn\_standardGaussianQuantile\_sq}$), its value at the midpoint of $a+x$ and $a-x$ is at most the average of its values at those two points. Since their midpoint is $a$, the displayed second derivative is nonnegative. The second-derivative criterion for convexity on an interval now gives the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_profile_sq_pair`, `BooleanAnalysis.GaussianSpace.hasDerivAt_profile_sq_pair_derivative`, `BooleanAnalysis.ThresholdFunctions.convexOn_standardGaussianQuantile_sq`.
