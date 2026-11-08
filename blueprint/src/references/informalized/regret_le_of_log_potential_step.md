<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: regret_le_of_log_potential_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Regret bound from potential increments

**Claim.** If each logarithmic potential increment is at most $-\eta$ times the round's expected loss plus $c$, then the regret is at most $\log(N)/\eta+cT/\eta$.

**Proof.** 1. Sum the assumed bound over all rounds. The logarithmic increments telescope to $\log W_T-\log W_0$, where $W_t$ is the potential at time $t$ (`log_potential_telescope`). The sum of the right-hand sides is $-\eta$ times the cumulative expected loss plus $cT$. Thus $\log W_T-\log W_0\le -\eta L+cT$, with $L$ the learner's cumulative expected loss.

2. At time zero every expert has weight one, so $W_0=N$ (`potential_zero`). At the final time, the potential is at least the weight of a best expert; consequently $W_T\ge \exp(-\eta B)$, where $B$ is the best expert's cumulative loss (`potential_ge_best_expert`). Since the logarithm is increasing, $\log W_T\ge-\eta B$.

3. Combining these inequalities gives $-\eta B-\log N\le -\eta L+cT$, hence $\eta(L-B)\le\log N+cT$. Dividing by the positive parameter $\eta$ yields the stated regret bound.

**Key facts.** `log_potential_telescope`, `potential_zero`, `potential_ge_best_expert`.
