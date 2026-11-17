<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.borell_factor_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borell scalar factor estimate

**Claim.** Under the stated assumptions on $p,q,\rho$, for every integer $m\ge2$ one has $\rho(m-q)\le m-p$.

**Proof.** First, $q<1$ follows from $q<p<1$, so $1-q>0$. The relation $\rho^2=(1-p)/(1-q)$ therefore gives $\rho^2(1-q)=1-p$. Consider the quadratic expression $m^2-2m+p+q-pq$. It is nonnegative: its part $m^2-2m$ is nonnegative for $m\ge2$, and $p+q-pq=q+(1-q)p$ is positive. Multiplying this inequality by $p-q\ge0$ and using the displayed relation yields $(m-p)^2(1-q)\ge \rho^2(1-q)(m-q)^2$. Since $1-q>0$, this gives $(m-p)^2\ge (\rho(m-q))^2$. Both sides before squaring are nonnegative: $m-p>0$, and $\rho(m-q)\ge0$. Comparing squares thus gives the claimed inequality.
