<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.invariance_c3_quarter_power_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-Root Power Inequality

**Claim.** For every natural number $k$ and real numbers $r,\varepsilon$ with $6/5\le r$ and $\varepsilon\ge0$, the stated fourth-root expression is at most $r^{2k}\varepsilon^{1/8}$.

**Proof.** The hypothesis gives $r\ge1$ and $r^4\ge2$. Since $k\le2^k$, it follows that $k\le r^{4k}$. Hence $k r^{3k}/3\le r^{8k}$: first use $1/3\le1$, then combine the powers, and use $7k\le8k$ with $r\ge1$. Multiplying this inequality by the nonnegative quantity $\sqrt{\varepsilon}$ preserves its direction. Taking fourth roots, which is increasing on nonnegative reals, bounds the left side by $(r^{8k}\varepsilon^{1/2})^{1/4}$. Rewrite $r^{8k}=(r^{2k})^4$; extracting the fourth root gives $r^{2k}$, while $(\varepsilon^{1/2})^{1/4}=\varepsilon^{1/8}$, including the case $\varepsilon=0$.
