<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.sharp_radius_comparison_limit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Limit of the sharp radius comparison

**Claim.** For $0<\lambda<1/2$, as $q$ tends to $2$ from above, $\exp\!\left(-\frac{q\log\rho(q,\lambda)}{q-2}\right)$ tends to $C(\lambda)$.

**Proof.** Set $u=\log((1-\lambda)/\lambda)>0$ and define $L(q)=\frac12[\log(\sinh(u/q))-\log(\sinh(u-u/q))]$. For $q>2$, the definition of the sharp radius and the identity $u/(q/(q-1))=u-u/q$ show that $\log\rho(q,\lambda)=L(q)$; the logarithms are legitimate since both hyperbolic sines are positive. Also $L(2)=0$. By the derivative formula ($\texttt{log\_sinh\_difference\_hasDerivAt\_two}$), the difference quotient $L(q)/(q-2)$ tends to $-u\cosh(u/2)/(4\sinh(u/2))$. Meanwhile $q\to2$, so $-qL(q)/(q-2)$ tends to $u\cosh(u/2)/(2\sinh(u/2))$. The log-odds hyperbolic ratio identity ($\texttt{log\_odds\_coth}$) identifies this limit as $u/(2(1-2\lambda))$. Continuity of the exponential then gives the limit $\exp(u/(2(1-2\lambda)))$. Since $u=\log((1-\lambda)/\lambda)$, this is exactly the nonexceptional branch defining $C(\lambda)$; the hypothesis $\lambda<1/2$ excludes its exceptional case.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.log_sinh_difference_hasDerivAt_two`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.log_odds_coth`.
