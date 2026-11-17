<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.sqrt_div_noiseBlockCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal Block Count Bound

**Claim.** For $0<\delta\le \tfrac12$, if $m=\lfloor\delta^{-1}\rfloor$, then $\sqrt m/m\le\sqrt2\,\sqrt\delta$.

**Proof.** Write $M=m$ as a real number. The floor bounds give $M\ge2$ and $\delta^{-1}/2\le M$. In particular $M>0$, and multiplying the latter inequality by $2\delta>0$ gives $1\le2\delta M$. Taking square roots yields $1\le\sqrt2\sqrt\delta\sqrt M$. Since $M>0$, the desired inequality is equivalent to $\sqrt M\le\sqrt2\sqrt\delta\,M$. Multiplying the square-root inequality by $\sqrt M$ gives precisely this conclusion.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.noiseBlockCount_spec`.
