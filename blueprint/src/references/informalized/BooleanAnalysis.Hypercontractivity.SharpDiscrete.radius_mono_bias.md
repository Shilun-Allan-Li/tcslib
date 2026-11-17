<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_mono_bias -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in atom mass

**Claim.** For $q>2$ and $0<\lambda\le\gamma<1/2$, the sharp radius at $\lambda$ is no larger than the sharp radius at $\gamma$.

**Proof.** Let $a=1/(q-1)$ and write $t(x)=\log((1-x)/x)/(q/(q-1))$. Then $0<a<1$. The logarithm decreases as $x$ increases on this interval, so $t(\gamma)\le t(\lambda)$; both quantities are positive because $x<1/2$. The hyperbolic sine ratio $u\mapsto\sinh(au)/\sinh u$ is nonincreasing for positive $u$ (`sinh_ratio_antitoneOn`). Applying this with $u=t(\gamma)$ and $v=t(\lambda)$ gives the corresponding ratio at $t(\lambda)$ no larger than that at $t(\gamma)$. The identity $a\,t(x)=\log((1-x)/x)/q$ identifies these ratios with the expressions under the square roots defining the two radii. Taking square roots preserves the inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.sinh_ratio_antitoneOn`.
