<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: cumLoss_horizon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cumulative Loss at the Horizon

**Claim.** For each expert, the cumulative loss through round $T$ equals the sum of its losses over all $T$ rounds.

**Proof.** At the horizon, the condition selecting rounds in the cumulative loss is $s<T$. Every element $s$ of $\mathrm{Fin}\,T$ already satisfies this condition. Hence the filtered set of rounds is the full set of rounds, and the cumulative loss is exactly $\sum_{t:\mathrm{Fin}\,T}\ell_t(i)$.
