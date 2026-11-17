<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.integral_taylor_cubic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Taylor Polynomial and Moments

**Claim.** Under the stated moment hypotheses, the expectation of the cubic Taylor polynomial in $bX$ equals $\psi(a)+\frac{\psi^{(2)}(a)}{2}b^2$.

**Proof.** Apply the integration formula for a Taylor polynomial (`integral_taylor_polynomial`) with degree cutoff four. It rewrites the expectation as the sum, for $j=0,1,2,3$, of the Taylor coefficient $\psi^{(j)}(a)/j!$ times $b^j$ times the $j$th moment of $X$. The zeroth moment is one because the measure is a probability measure; the first and third moments vanish, and the second moment is one by hypothesis. Only the terms for $j=0$ and $j=2$ remain. Since $2!=2$, their sum is exactly $\psi(a)+\frac{\psi^{(2)}(a)}{2}b^2$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_taylor_polynomial`.
