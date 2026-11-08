<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.contDiff_intervalSmooth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Regularity gained by interval smoothing

**Claim.** If $\psi$ is $m$-times continuously differentiable and $\eta>0$, then its interval smoothing is $(m+1)$-times continuously differentiable.

**Proof.** The derivative formula identifies the derivative of the smoothing with $x\mapsto(\psi(x+\eta)-\psi(x))/\eta$. Since $\psi$ is $m$-times continuously differentiable, composing it with the identity shifted by $\eta$ and subtracting $\psi$ gives an $m$-times continuously differentiable function; division by the constant $\eta$ preserves that regularity. The derivative is therefore $m$-times continuously differentiable, and the smoothing itself is differentiable everywhere. These are exactly the conditions for the smoothing to be $(m+1)$-times continuously differentiable.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_hasDerivAt`.
