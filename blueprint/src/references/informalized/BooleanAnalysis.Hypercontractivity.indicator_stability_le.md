<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/Influence.lean :: BooleanAnalysis.Hypercontractivity.indicator_stability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-set Stability Bound

**Claim.** If a Boolean function takes only the values $0$ and $1$, then its noise stability at any $0<\rho\leq 1$ is at most its mean raised to $2/(1+\rho)$.

**Proof.** Let $A$ be the set of cube points where $f$ equals $1$. At each point, the indicator of $A$ agrees with $f$: if $f(x)=1$, then $x\in A$, and if $f(x)=0$, then $x\notin A$. Apply the small-set expansion inequality to $A$, which bounds the indicator's noise stability by the volume of $A$ raised to $2/(1+\rho)$. Since the indicator equals $f$, its stability is $\langle f,T_\rho f\rangle$ and its volume is $\mathbb E[f]$, giving the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.small_set_expansion`.
