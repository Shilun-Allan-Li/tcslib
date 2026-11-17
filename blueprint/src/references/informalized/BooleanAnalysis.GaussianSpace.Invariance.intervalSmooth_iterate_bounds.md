<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_iterate_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for Repeated Interval Averaging

**Claim.** After $m+1$ repeated interval averages, the result is $m+1$ times continuously differentiable, remains $c$-Lipschitz, differs from the original function by at most $(m+1)c\eta$, and has its $(m+1)$st derivative bounded by $c(2/\eta)^m$.

**Proof.** Proceed by induction on $m$. For $m=0$, the one-step estimates give continuous differentiability and preservation of the Lipschitz constant; the averaging error is at most $c\eta$, and the first derivative is bounded by $c$. These are the asserted bounds at the base case. For the successor step, write the new iterate as one interval average of the preceding iterate. The regularity theorem for interval averaging raises the differentiability order by one, and averaging preserves the Lipschitz constant (`contDiff_intervalSmooth`, `lipschitz_intervalSmooth`). For the approximation estimate, use the triangle inequality to split the difference from the original function into the new averaging error, at most $c\eta$ (`abs_intervalSmooth_sub_le`), and the preceding iterate's error; together these yield $(m+2)c\eta$. For the derivative estimate, the formula for derivatives of an interval average expresses the new derivative of order $m+2$ as the difference of the preceding order-$m+1$ derivatives at $x+\eta$ and $x$, divided by $\eta$ (`iteratedDeriv_intervalSmooth`). Each term has absolute value at most $c(2/\eta)^m$ by induction, so the difference is at most twice that bound. Division by positive $\eta$ gives $c(2/\eta)^{m+1}$.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.abs_deriv_intervalSmooth_le`, `BooleanAnalysis.GaussianSpace.Invariance.abs_intervalSmooth_sub_le`, `BooleanAnalysis.GaussianSpace.Invariance.contDiff_intervalSmooth`, `BooleanAnalysis.GaussianSpace.Invariance.iteratedDeriv_intervalSmooth`, `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_intervalSmooth`.
