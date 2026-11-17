<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.succFieldTM_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intermediate Successor-Field Run

**Claim.** For every time up to the encoding length, the run is unchanged at time zero; otherwise it is the configuration after the tag transition and then a scan of the first `t-1` unary-field symbols, with copying exactly when enabled. The control is unary before the encoding ends and done at its final step.

**Proof.** Proceed by cases on the time. At zero, iteration has not applied a transition, so the run is the initial configuration. For positive time, separate the first step from the remaining `t` steps using the successor equation for iterated runs (`runFrom_succ_eq_step`). If `s` is absent, the optional-state encoding is the single false bit. The tag transition reads that bit and enters done with false live flag; the bound on time forces the remaining count to be zero, giving the stated configuration. If `s` is present, the first bit is true, so the tag transition advances the source head and enters unary. The remaining source symbols are the unary encoding of the state index, starting at the new head. Apply the unary-field run result (`succFieldTM_unary_run`) to those remaining steps: it copies the scanned prefix when enabled and determines whether the control is still unary or has reached done. Since the original encoding consists of the tag bit followed by that unary word, the inequality relating the remaining time to the unary length gives exactly the claimed phase condition in terms of the original time.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.step_of_tapeAction_move`, `Turing.StepBlock.succFieldTM_unary_run`.
