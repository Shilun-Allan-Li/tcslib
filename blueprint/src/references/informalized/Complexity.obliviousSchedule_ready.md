<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.obliviousSchedule_ready -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Readiness for the first macrostep

**Claim.** Under the stated time bound for the clock machine and the lower bound on $T$, the schedule machine reaches a macrostep-check configuration with the asserted unary counter and guide tape.

**Proof.** Fix the input $x$. By the clock-capture lemma (`clockStageCfg_captures`), there is a time $	au+1$ at which the schedule has completed the clock phase: its configuration is the prescribed clock-stage configuration associated with a halted run of $W$, whose output is the binary expansion of $T(|x|)$. The budget decoded from that output is therefore exactly $T(|x|)$, by the binary decoding identity (`budgetValue_bits`).

The hypothesis $|x|\le T(|x|)$ implies $|x|+1\le (a+1)(T(|x|)+1)$. This supplies the length bound needed to initialize the schedule’s setup configuration. Applying the setup-initialization lemma (`setupCfg_initializes`) produces a later configuration in the macrostep-check state, with the unary tape holding $(a+1)(T(|x|)+1)$ markers and the guide tape having the specified radius. The clock-stage description (`clockStageCfg_setup`) identifies the configuration after the clock phase with precisely the setup configuration to which this initialization result applies. Finally, decompose the total run time into the clock-stage prefix and this setup interval using `runFrom_add`; the resulting time witnesses the claim.

**Key facts.** `Complexity.clockStageCfg_captures`, `Complexity.budgetValue_bits`, `Complexity.clockStageCfg_setup`, `Complexity.setupCfg_initializes`, `Turing.MultiTapeTM.runFrom_add`.
