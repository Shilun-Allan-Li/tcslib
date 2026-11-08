<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.abs_intervalSmooth_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximation by interval smoothing

**Claim.** For a $c$-Lipschitz function and $\eta>0$, its interval smoothing differs from the original function at $x$ by at most $c\eta$.

**Proof.** The interval-average mean-value property supplies some $t$ strictly between $0$ and $\eta$ for which the interval average of $s\mapsto\psi(x+s)$ equals $\psi(x+t)$. Hence the difference in question is $|\psi(x+t)-\psi(x)|$. The Lipschitz condition bounds this by $ct$, and $0<t<\eta$ together with $c\ge0$ gives $ct\le c\eta$.
