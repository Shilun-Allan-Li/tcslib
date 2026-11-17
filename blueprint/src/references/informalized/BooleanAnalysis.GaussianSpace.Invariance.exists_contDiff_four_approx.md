<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.exists_contDiff_four_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-order smooth approximation

**Claim.** For $\eta>0$, a nonnegative Lipschitz constant $c$, and a $c$-Lipschitz function $\psi$, there is a $C^4$ function within $4c\eta$ of $\psi$ everywhere whose fourth derivative is bounded in absolute value by $8c/\eta^3$.

**Proof.** Smooth $\psi$ by applying the interval-smoothing operation four times. The iterate is $C^4$, and the smoothing estimate bounds its pointwise error by $(m+1)c\eta$ and its $(m+1)$st derivative by $c(2/\eta)^m$ when the operation is iterated $m+1$ times (intervalSmooth_iterate_bounds). Taking $m=3$ gives error at most $4c\eta$ and fourth derivative at most $c(2/\eta)^3=8c/\eta^3$.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_iterate_bounds`.
