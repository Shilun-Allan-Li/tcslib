<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: hedge_regret_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hedge Regret Bound

**Claim.** For a valid loss sequence and a learning rate $0<\eta\le 1$, Hedge's regret is at most $\log N/\eta+\eta T/2$.

**Proof.** For each round, the logarithmic potential change is at most $-(1-e^{-\eta})$ times Hedge's loss (`log_potential_step`). Since each round's Hedge loss lies between $0$ and $1$ (`hedgeLoss_nonneg`, `hedgeLoss_le_one`), and $1-e^{-\eta}\ge \eta-\eta^2/2$ for $\eta>0$ (`one_sub_exp_neg_ge`), this change is at most $-\eta$ times the round's loss plus $\eta^2/2$. Applying the cumulative potential argument `regret_le_of_log_potential_step` with this per-round error gives regret at most $\log N/\eta+(\eta^2/2)T/\eta$. Simplifying the latter term yields $\eta T/2$.

**Key facts.** `log_potential_step`, `one_sub_exp_neg_ge`, `hedgeLoss_le_one`, `hedgeLoss_nonneg`, `regret_le_of_log_potential_step`.
