<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.noiseBlockCount_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on the Block Count

**Claim.** If $0<\delta\le1/2$ and $m=\lfloor\delta^{-1}\rfloor$, then $2\le m$, $m\le\delta^{-1}$, and $\delta^{-1}/2\le m$.

**Proof.** The assumptions imply $2\le\delta^{-1}$, so the floor of $\delta^{-1}$ is at least $2$. By the defining floor inequalities, $m\le\delta^{-1}<m+1$. The first inequality gives the stated upper bound, and the strict second inequality gives $\delta^{-1}/2<(m+1)/2\le m$ since $m\ge1$. Hence the required lower bound follows as well.
