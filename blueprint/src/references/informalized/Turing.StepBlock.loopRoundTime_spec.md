<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean :: Turing.StepBlock.loopRoundTime_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Exit Time and One-Step Simulation

**Claim.** Under the stated representation and live-entry hypotheses, the first positive time at which the round machine reaches either exit is at most $50(L+1)$. At that time it is at the live exit precisely when the simulated one-step successor has a present state; the endpoint represents that successor and preserves output, and no earlier positive time is an exit.

**Proof.** Since the source configuration has a present state, choose its state $q$. The round-machine effect theorem (Turing.StepBlock.roundTM_effect) supplies a positive time $T$ bounded by $50(L+1)$ at which the machine reaches the appropriate exit, represents the result of applying the transition action at $q$, and has made no output change; it also excludes either exit at every positive intermediate time. The source machine’s one-step result is exactly that transition action applied to the configuration, by the definition of a machine step in a present state. Thus the endpoint and representation statements have the required form.

It remains to identify the time selected by the definition of $	au$. The effect theorem gives a positive exit time, so the defining set is nonempty and $	au$ is its least element. The first-exit uniqueness theorem (Turing.StepBlock.roundTM_firstExit_unique) says there is exactly one positive exit time having no earlier positive exit. The time $	au$ has this property by minimality. Conversely, $T$ has it by the intermediate-time exclusion just obtained. Hence $	au=T$. Substituting this equality transfers the bound and endpoint facts to $	au$; the same exclusion gives the asserted statement for every positive time below it.

**Key facts.** `Turing.StepBlock.roundTM_effect`, `Turing.StepBlock.roundTM_firstExit_unique`.
