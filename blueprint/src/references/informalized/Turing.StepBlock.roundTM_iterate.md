<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundTM_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the Round Machine

**Claim.** If the simulated machine remains in a live state through time $t$, then the round machine, started from a represented configuration at its entry state, reaches the representation of the simulated configuration at time $t$ within the stated time bound. Throughout the run its output is unchanged, it avoids halt, its original-tape heads visit only cells visited by the simulated heads, and its auxiliary heads stay in the stated bounded interval.

**Proof.** Proceed by induction on $t$. For $t=0$, take $T=0$. The run is the initial configuration, so its entry state and representation are given. The only time under consideration is zero, and the head-position clauses follow from the representation: original heads agree with those of the simulated configuration, while both auxiliary heads start at zero, inside the required interval.

For the successor case, the simulated configuration is live at time zero, so write its state as $q$. The one-round result `roundTM_visited` supplies a positive time $T_1$, bounded by $50(L+1)$, at which the round machine reaches its live or halting exit and represents the result of applying the transition at $q$. The hypothesis that the simulated machine is live through time $t+1$ forces that transition's successor state to be live, so this exit is the entry state. Apply the induction hypothesis to the simulated configuration after one step, using `runFrom_succ_eq_step` to transfer the remaining liveness assumption. It gives a further run of length $T_2$ that simulates the remaining $t$ steps. Concatenate the two runs and set $T=T_1+T_2`; `runFrom_add` identifies the concatenated endpoint, and the two bounds give $t+1\le T\le (t+1)50(L+1)$.

The first round has unchanged output and avoids halt by its one-round guarantees. At its endpoints the machine is at entry, and in its interior it is neither entry nor halt; the second round's output guarantee therefore preserves the original output throughout, and its no-halt guarantee handles the remainder. For original-tape visits, split the concatenated visit set using `visitedByTapeHead_add_subset`. Visits in the first part, including its starting cell, are covered by `visitedByTapeHead_step_subset` for the simulated first step; visits in the second part are covered by induction, then by the same inclusion for that simulated step. Auxiliary-head visits split into the two round segments and each segment satisfies the same interval bound.

**Key facts.** `Turing.StepBlock.roundTM_visited`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.visitedByTapeHead_add_subset`, `Turing.MultiTapeTM.visitedByTapeHead_step_subset`.
