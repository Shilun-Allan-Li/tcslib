<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_run_guarded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Wrapper follows a run before exit

**Claim.** If the original run from a configuration avoids the exit state at every time $j<t$, then for $t$ steps the wrapper run from the state-renamed configuration equals the state-renamed original configuration.

**Proof.** Induct on $t$. At time zero, both runs start at the same state-renamed configuration. For the successor step, apply the induction hypothesis to the first $t$ steps; the guard for those steps follows by restricting the given guard. Now inspect the original configuration at time $t$. If it is halted, both machines stay at that configuration, so their next configurations still agree after renaming. If its state is $q$, then $q$ cannot be the exit state: otherwise the guard at time $t$, which is less than $t+1$, would be violated. On a non-exit state the wrapper uses the original transition, merely renaming its successor state. Hence the next configurations agree, completing the induction. The decomposition of a run of $t+1$ steps into its first $t$ steps and one final transition is the run-successor identity (Turing.MultiTapeTM.runFrom_succ_eq_step').

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
