<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Concentration.lean :: BooleanAnalysis.Hypercontractivity.ConcentrationAux.concentration_parameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration Parameter Threshold

**Claim.** If $k$ is a positive integer and $(\sqrt{2e})^k\leq t$, then $t>0$ and $t^{2/k}/e\geq2$.

**Proof.** Since $\sqrt{2e}>0$, its $k$th power is positive, so the assumed lower bound implies $t>0$. The map $x\mapsto x^{2/k}$ is increasing on nonnegative reals. Applying this to $(\sqrt{2e})^k\leq t$ gives $((\sqrt{2e})^k)^{2/k}\leq t^{2/k}$. The left side simplifies to $2e$, because $k>0$. Dividing by $e>0$ proves $t^{2/k}/e\geq2$.
