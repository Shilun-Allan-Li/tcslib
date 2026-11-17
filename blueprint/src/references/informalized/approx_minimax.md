<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/FiniteMinimax.lean :: approx_minimax -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximate minimax strategies

**Claim.** For every positive error tolerance $\varepsilon$, there are mixed strategies $p$ and $q$ such that every pure payoff against $q$ is at most every corresponding payoff of $p$ against a pure column, up to the additive error $\varepsilon$: $\operatorname{payoffVsPure}(G,p,j)+\varepsilon\geq\operatorname{pureVsPayoff}(G,i,q)$ for all $i,j$.

**Proof.** Choose the learning rate $\eta=\min(1,4\varepsilon/5)$, which is positive and at most $4\varepsilon/5$. Since $M>1$, $\log M>0$. Choose a positive integer $T$ large enough that $\log M/(\eta T)\leq\varepsilon/2$; taking $T$ greater than the ceiling of $2\log M/(\eta\varepsilon)$ suffices. The hedge construction (hedge_construction) then supplies mixed strategies whose payoff gap is bounded by $(\log M/\eta+\eta T/8)/T$. This error is $\log M/(\eta T)+\eta/8$. The first term is at most $\varepsilon/2$, while the second is at most $(4\varepsilon/5)/8=\varepsilon/10\leq\varepsilon/2$. Thus the gap is at most $\varepsilon$, giving the claimed inequalities for every pair of pure strategies.

**Key facts.** `hedge_construction`.
