<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedReturn_visited -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited cells under return embedding

**Claim.** For every time and work-tape index, the returned machine from the state-renamed configuration visits the same positions as the original machine.

**Proof.** By definition, both visited sets are images of the times from $0$ through $t$ under the head-position functions, so it suffices to compare those positions at each time $u$. If the original configuration is halted, both machines remain at their starting configurations for every time (`runFrom_of_halt`), and their work-head positions agree. Otherwise, the return-step correspondence iterates to identify the returned run from the return embedding with the return embedding of the original run (`runFrom_comm_of_step`, using `embedReturn_step`). At each such time the original state remains live, since the return action sends a live transition to a left-summand state. The live-state identification (`embedReturnCfg_live`) therefore identifies this configuration embedding with state renaming; renaming leaves the work-head position unchanged. Thus the positions agree at each time, and their visited-position sets are equal.

**Key facts.** `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.embedReturn_step`, `Turing.embedReturnCfg_live`.
