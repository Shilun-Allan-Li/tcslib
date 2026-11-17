<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/GeneratingFunction.lean :: BooleanAnalysis.GaussianSpace.normalizedHermite_generating_summand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Hermite series term

**Claim.** For every nonnegative integer $j$ and real numbers $x,t$, the normalized Hermite summand $H_j(x)t^j/\sqrt{j!}$ equals the unnormalized Hermite summand $\operatorname{He}_j(x)t^j/j!$.

**Proof.** Evaluating the normalized polynomial at $x$ evaluates its constant factor and the mapped Hermite polynomial separately. The integer coefficients map to their usual real values, so the resulting expression is $\operatorname{He}_j(x)t^j$ multiplied by $(\sqrt{j!})^{-1}$ and then divided by $\sqrt{j!}$. Since $j!$ is nonnegative and $\sqrt{j!}^{\,2}=j!$, the two factors of the square-root denominator combine to give $j!$ in the denominator, proving the identity.
