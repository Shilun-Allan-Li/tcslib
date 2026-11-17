<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.contracted_probability_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interior Under Contraction

**Claim.** If $a\in(0,1)$, $a+b\in[0,1]$, and $0\le\rho<1$, then $a+\rho b\in(0,1)$.

**Proof.** For the lower bound, write $a+\rho b=(1-\rho)a+\rho(a+b)$. Both terms are nonnegative, and the first is strictly positive because $1-\rho>0$ and $a>0$. For the upper bound, write $1-(a+\rho b)=(1-\rho)(1-a)+\rho(1-a-b)$. Again both terms are nonnegative, while the first is strictly positive because $1-a>0$. Thus $0<a+\rho b<1$.
