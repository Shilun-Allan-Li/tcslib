<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_log_parameters -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on logarithmic parameters

**Claim.** If $0<\lambda\le 1/2$, then $\frac12\le\log(1/\lambda)\le\log(9/\lambda)\le5\log(1/\lambda)$.

**Proof.** The assumption $\lambda\le1/2$ implies $2\le1/\lambda$. Also, $\log 2\ge1/2$, by the standard lower bound $1-1/x\le\log x$ for positive $x$, applied at $x=2$. Since logarithm is increasing, these facts give $1/2\le\log 2\le\log(1/\lambda)$. Next, $9/\lambda\ge1/\lambda$, so monotonicity gives $\log(1/\lambda)\le\log(9/\lambda)$. Finally, $9\le2^4$ implies $\log 9\le4\log 2$. The identity $\log(9/\lambda)=\log 9+\log(1/\lambda)$ and $\log 2\le\log(1/\lambda)$ then give $\log(9/\lambda)\le5\log(1/\lambda)$.
