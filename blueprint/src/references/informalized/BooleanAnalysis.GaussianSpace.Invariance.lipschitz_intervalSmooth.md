<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_intervalSmooth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Interval Averaging

**Claim.** For $\eta>0$, interval averaging of a $c$-Lipschitz function produces another $c$-Lipschitz function.

**Proof.** The interval average is differentiable, with derivative $(\psi(x+\eta)-\psi(x))/\eta$ (\texttt{intervalSmooth_hasDerivAt}). Since $\psi$ is $c$-Lipschitz, the absolute value of this difference quotient is at most $c$, using $\eta>0$. Hence the derivative of the averaged function has absolute value at most $c$ everywhere (\texttt{abs_deriv_intervalSmooth_le}). The derivative criterion for Lipschitz continuity now shows that the interval average is $c$-Lipschitz.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_hasDerivAt`, `BooleanAnalysis.GaussianSpace.Invariance.abs_deriv_intervalSmooth_le`.
