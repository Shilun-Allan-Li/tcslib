<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyDictator_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Monotonicity

**Claim.** If $S\subseteq T$, then the dictator function on subsets of a one-element set satisfies $f(S)\le f(T)$.

**Proof.** Fix $S\subseteq T$. If the distinguished element belongs to $S$, it also belongs to $T$, so both function values are $1$. If it does not belong to $S$, then $f(S)=0$, while $f(T)$ is either $0$ or $1$. In each case $f(S)\le f(T)$.
