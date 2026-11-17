<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.iteratedDeriv_intervalSmooth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Higher Derivatives of an Interval Average

**Claim.** For positive $\eta$, nonnegative integer $m$, and an $m$-times continuously differentiable function $\psi$, the $(m+1)$st derivative of its interval average is the difference of the $m$th derivatives at the interval endpoints divided by $\eta$.

**Proof.** The derivative of the interval average at a point $y$ is $(\psi(y+\eta)-\psi(y))/\eta$, by the endpoint formula for differentiating an interval average (`intervalSmooth_hasDerivAt`). The shifted function $y\mapsto\psi(y+\eta)$ and $\psi$ are both $m$-times continuously differentiable. Differentiate the displayed derivative $m$ more times. Linearity of iterated derivatives gives the difference of their $m$th derivatives, with the constant factor $1/\eta$ unchanged. Translation commutes with differentiation, so the shifted term becomes $\psi^{(m)}(x+\eta)$ and the other becomes $\psi^{(m)}(x)$. This yields the asserted quotient.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_hasDerivAt`.
