<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: log_potential_telescope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Telescoping log potential

**Claim.** For any natural numbers $N,T$, real learning rate $\eta$, and loss sequence $\ell$, the sum of successive changes in log potential over $T$ rounds equals the total change from time $0$ to time $T$.

**Proof.** Let $f(n)=\log W_n$, where $W_n$ is the potential at time $n$. The sum over rounds indexed by $\mathrm{Fin}\,T$ is the same as the sum over integers $n=0,\ldots,T-1$ of $f(n+1)-f(n)$. In this finite sum each intermediate value $f(1),\ldots,f(T-1)$ occurs once with each sign, so they cancel, leaving $f(T)-f(0)$.
