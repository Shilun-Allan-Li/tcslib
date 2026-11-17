<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: hedge_regret_bound_tight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tight Hedge Regret Bound

**Claim.** For any positive learning rate and valid loss sequence, Hedge's regret is at most $\log N/\eta+\eta T/8$.

**Proof.** The tight one-round potential estimate bounds the change in logarithmic potential by $-\eta$ times Hedge's loss plus $\eta^2/8$ (`log_potential_step_tight`). Use this estimate in the cumulative potential argument (`regret_le_of_log_potential_step`): the roundwise inequalities telescope across the horizon, producing regret at most $\log N/\eta+(\eta^2/8)T/\eta$. Simplifying gives the claimed bound.

**Key facts.** `log_potential_step_tight`, `regret_le_of_log_potential_step`.
