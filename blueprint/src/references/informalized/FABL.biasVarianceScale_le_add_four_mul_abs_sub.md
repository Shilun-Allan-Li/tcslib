<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasVarianceScale_le_add_four_mul_abs_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Bound for the Bias Variance Scale

**Claim.** For $p,q\in[0,1]$, the bias variance scale at $p$ is at most its value at $q$ plus $4|p-q|$.

**Proof.** Factoring the difference gives $4p(1-p)-4q(1-q)=4(p-q)(1-p-q)$. Since both parameters lie in $[0,1]$, we have $-1\le 1-p-q\le 1$, so $|1-p-q|\le 1$. Taking absolute values in the factorization therefore yields $|4p(1-p)-4q(1-q)|\le 4|p-q|$. The difference itself is at most its absolute value, giving the claimed upper bound.
