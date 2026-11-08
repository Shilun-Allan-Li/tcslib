<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/GeneratingFunction.lean :: BooleanAnalysis.GaussianSpace.hermite_generating_function -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite generating function

**Claim.** For real $x,t$, the Hermite polynomials satisfy $\sum_{j=0}^{\infty} H_j(x)t^j/j!=\exp(tx-t^2/2)$.

**Proof.** Consider the entire complex function $z\mapsto \exp(xz-z^2/2)$. Its Taylor series at zero converges to its value at every complex $t$. The $j$th iterated derivative at a general point $z$ is $H_j(x-z)\exp(xz-z^2/2)$ (`iteratedDeriv_exp_quadratic`); at zero this is $H_j(x)$. Therefore the Taylor coefficient of degree $j$ is $H_j(x)/j!$, and evaluating the series at real $t$ gives the asserted identity after restricting from the complex equality to the real numbers.

**Key facts.** `BooleanAnalysis.GaussianSpace.iteratedDeriv_exp_quadratic`.
