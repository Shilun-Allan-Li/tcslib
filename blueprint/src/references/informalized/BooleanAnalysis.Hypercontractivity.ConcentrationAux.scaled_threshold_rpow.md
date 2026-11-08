<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Concentration.lean :: BooleanAnalysis.Hypercontractivity.ConcentrationAux.scaled_threshold_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a Concentration Power

**Claim.** For $k>0$ and $\lambda,t>0$, $(t(\sqrt\lambda)^k)^{2/k}=\lambda t^{2/k}$.

**Proof.** Both factors inside the power are nonnegative, so the real-power product rule gives $(t(\sqrt\lambda)^k)^{2/k}=t^{2/k}((\sqrt\lambda)^k)^{2/k}$. Express the integer power as a real power and combine exponents: $((\sqrt\lambda)^k)^{2/k}=(\sqrt\lambda)^2=\lambda$, using $k>0$ to cancel the exponents and $\lambda>0$ for the square-root identity. This yields the formula.
