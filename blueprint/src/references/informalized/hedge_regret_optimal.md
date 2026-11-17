<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: hedge_regret_optimal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Regret at the Chosen Learning Rate

**Claim.** Under the stated conditions on $N$ and $T$, the learning rate $\eta=\sqrt{2\log N/T}$ gives Hedge regret at most $\sqrt{2T\log N}$.

**Proof.** Since $N>1$, $\log N>0$, and since $T>0$, the chosen learning rate is positive. The assumption $2\log N\le T$ also implies that it is at most $1$. Thus the general Hedge bound applies, giving regret at most $\log N/\eta+\eta T/2$. The balancing identity `optimalEta_balance`, with $a=\log N$ and $c=2$, simplifies this expression to $\sqrt{4\log N\,T/2}$. Rearranging the factors under the square root gives $\sqrt{2T\log N}$.

**Key facts.** `hedge_regret_bound`, `optimalEta_balance`.
