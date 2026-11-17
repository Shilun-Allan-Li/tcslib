<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.integral_pow_mul_one_sub_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral of Powers on the Unit Interval

**Claim.** For natural numbers $k,m$, the integral of $x^k(1-x)^m$ from $0$ to $1$ equals $k!m!/(k+m+1)!$.

**Proof.** Evaluate the corresponding complex beta integral with parameters $k+1$ and $m+1$. Its natural-parameter formula gives the integral as $m!$ divided by the product $(k+1)(k+2)\cdots(k+m+1)$. Because the integrand is real-valued, the real integral is the real part of this complex evaluation, so the same formula holds over $\mathbb R$. The product is the rising factorial $(k+1)^{\overline{m+1}}$, and the factorial identity $k!(k+1)^{\overline{m+1}}=(k+m+1)!$ converts the quotient to $k!m!/(k+m+1)!$.
