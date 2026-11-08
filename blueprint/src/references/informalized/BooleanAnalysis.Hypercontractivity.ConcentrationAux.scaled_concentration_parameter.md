<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Concentration.lean :: BooleanAnalysis.Hypercontractivity.ConcentrationAux.scaled_concentration_parameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaled Concentration Threshold

**Claim.** If $k>0$, $\lambda>0$, and $(\sqrt{2e/\lambda})^k\leq t$, then $t>0$ and $\lambda t^{2/k}/e\geq2$.

**Proof.** The threshold $(\sqrt{2e/\lambda})^k$ is positive, so the hypothesis first gives $t>0$. Multiply the threshold inequality by the nonnegative factor $(\sqrt\lambda)^k$. The square-root and power laws show that the resulting lower bound is $(\sqrt{2e})^k\leq t(\sqrt\lambda)^k$. Apply the concentration parameter threshold ( `concentration_parameter`) to this scaled quantity, obtaining $2\leq (t(\sqrt\lambda)^k)^{2/k}/e$. The scaling identity ( `scaled_threshold_rpow`) rewrites its numerator as $\lambda t^{2/k}$, which proves the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ConcentrationAux.concentration_parameter`, `BooleanAnalysis.Hypercontractivity.ConcentrationAux.scaled_threshold_rpow`.
