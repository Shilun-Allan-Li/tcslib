<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.capture_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep Run Under Output Capture

**Claim.** Under the transition-agreement hypothesis, if the original machine has not halted before time $t$, then the host machine run for $t$ steps from the captured initial configuration equals the capture of the original machine's configuration at time $t$.

**Proof.** First establish the one-step correspondence for any nonhalted original configuration. Its state is present, so the captured state is the image of that state. The captured input symbol equals the original input symbol, and the first $k$ work-tape head symbols agree with the original machine's head symbols. The transition-agreement hypothesis therefore identifies the host's action with the capture transform of the original action. Applying the action-commutation property (`Turing.capture_apply`) gives the desired correspondence after one step.

Now induct on the number of steps. At time zero, both sides are the captured initial configuration. For the induction step, the nonhalting hypothesis ensures the original run is still active at the preceding time, so the one-step correspondence applies to its configuration then. Unfold each run by one step (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) and use the induction hypothesis at that preceding time. This proves equality at time $t$.

**Key facts.** `Turing.capture_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
