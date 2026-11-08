<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.maskedClock_lockstep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Masked Clock Runs in Lockstep

**Claim.** After replacing the input of the masked machine’s configuration at time $t$ by the constant word of $|x|$ copies of $z$, the result equals the configuration of $W$ at time $t$ on that constant input.

**Proof.** Induct on the number $t$ of steps. At time zero, both sides are the corresponding initial configuration, so they agree. For the successor step, express each run at time $t+1$ as one transition applied to its time-$t$ configuration (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). The one-step compatibility fact for the masked machine (`Complexity.maskedClock_step`) says that masking after its transition is the same as transitioning after masking. The induction hypothesis identifies the masked time-$t$ configuration with the time-$t$ configuration of $W$ on the constant input. Applying the successor-step identity again yields equality at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.maskedClock_step`.
