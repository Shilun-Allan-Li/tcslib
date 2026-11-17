<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_lift_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame Preservation Under Symbol Lifting

**Claim.** If the decoded Boolean decrement run has empty output at time $T$, then through time $T$ the lifted run preserves the input-head position and output of the original configuration, and its work-tape head position agrees with the decoded run.

**Proof.** Fix $u\le T$. First use the execution-commutation theorem (`sc_lift_run`) to express the lifted run at time $u$ as the original configuration combined with the decoded Boolean run via the lifting operation. The input-position identities for lifting and decoding (`Cfg.liftOver_inputPos` and `Cfg.decodeSymbols_inputPos`), together with the fact that the decrement machine does not move the input head (`sc_dec_inputPos`), show that the input positions agree. For the output, outputs only grow by extension during a run (`MultiTapeTM.output_prefix`). Since the decoded run's output at time $T$ is empty, its output at time $u$ must be empty as well. The lifting formula for outputs (`Cfg.liftOver_output`) then reduces to the original output. Finally, the lifting operation leaves work-tape head positions equal to those of the decoded configuration (`Cfg.liftOver_workTapePos`).

**Key facts.** `Turing.sc_lift_run`, `Turing.Cfg.liftOver_inputPos`, `Turing.sc_dec_inputPos`, `Turing.Cfg.decodeSymbols_inputPos`, `Turing.MultiTapeTM.output_prefix`, `Turing.Cfg.liftOver_output`, `Turing.Cfg.liftOver_workTapePos`.
