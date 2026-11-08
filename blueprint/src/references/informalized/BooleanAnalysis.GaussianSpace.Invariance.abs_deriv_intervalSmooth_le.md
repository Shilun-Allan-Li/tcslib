<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.abs_deriv_intervalSmooth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative bound for interval smoothing

**Claim.** For $eta>0$, a $c$-Lipschitz function has interval smoothing whose derivative has absolute value at most $c$ at every point.

**Proof.** The derivative formula for interval smoothing gives $(S_\eta\psi)'(x)=(\psi(x+\eta)-\psi(x))/\eta$. The Lipschitz condition bounds the numerator in absolute value by $c\,|(x+\eta)-x|=c\eta$. Since $\eta>0$, division by $\eta$ yields the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_hasDerivAt`.
