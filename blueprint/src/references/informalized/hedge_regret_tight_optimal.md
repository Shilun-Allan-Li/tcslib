<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: hedge_regret_tight_optimal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimal Tight Hedge Regret

**Claim.** For $N>1$ and $T>0$, choosing $\eta=\sqrt{8\log N/T}$ gives Hedge regret at most $\sqrt{(T/2)\log N}$ on every valid loss sequence.

**Proof.** Because $N>1$ and $T>0$, the logarithm and the horizon are positive, so the chosen learning rate is positive. Apply the tight regret bound to obtain $\log N/\eta+\eta T/8$. The balancing identity `optimalEta_balance`, with $a=\log N$ and $c=8$, reduces this expression to $\sqrt{4\log N\,T/8}$. Simplifying inside the square root gives the claimed $\sqrt{(T/2)\log N}$.

**Key facts.** `hedge_regret_bound_tight`, `optimalEta_balance`.
