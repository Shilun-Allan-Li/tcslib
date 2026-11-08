<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.exists_recordStepTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Configuration Record

**Claim.** A deterministic machine can read a configuration record, simulate one transition, and then either write the successor record with the updated tag when the successor stays inside the prescribed window, or reject while restoring the original configuration; its runtime and head movement are bounded linearly in the record and input lengths.

**Proof.** Choose the input-seeking submachine and the record-step control machine supplied by `exists_inputSeekTM`. The read phase, formalized by `recordStep_read_all`, extracts the state, input-position information, work-tape data, tag, and native input symbol into finite control. The record's field-offset bound (`fieldOffset_add_length_le`) ensures that the fields fit inside the joined record interval, and `cfgRecord_length` gives the number of fields used in the ensuing bounds.

If the recorded state is halted, `recordStep_halt_run` takes the cleanup route to the yes verdict. The machine's simulated step leaves a halted configuration unchanged (`step_of_halt`), its output symbol is blank (`outputSymbol_of_halt`), and the hypothesis on the tag update says that a blank output leaves the tag unchanged. Thus the record written at the endpoint is the original record, as required; the alternative outside-window conclusion is impossible because the unchanged configuration satisfies the assumed window condition.

If the state is live, `recordStep_live_native` determines the native input symbol by seeking along the input and returns the observation needed to simulate the transition. The fact `recordStep_observed_action` verifies that this observation makes the record machine's action agree with the original machine's one-step transition, output, and window test. When the successor remains inside the window, `recordStep_apply_run` writes its record, with the tag updated using the emitted output; when it lies outside, `recordStep_reject_run` reaches the no verdict and restores the original configuration. In each branch, compose the read, native-seeking, and apply-or-reject runs using `recordRun_trans`, extending their head-radius bounds when necessary with `recordRun_mono`. Their individual time bounds add to at most the chosen constant times the record and input lengths. The run certificates ensure neither verdict is visited before the endpoint; the yes and no controls are distinct by construction.

**Key facts.** `Turing.exists_inputSeekTM`, `Turing.recordStep_read_all`, `Turing.fieldOffset_add_length_le`, `Turing.cfgRecord_length`, `Turing.recordStep_halt_run`, `Turing.MultiTapeTM.step_of_halt`, `Turing.MultiTapeTM.outputSymbol_of_halt`, `Turing.recordStep_live_native`, `Turing.recordStep_observed_action`, `Turing.recordStep_apply_run`, `Turing.recordStep_reject_run`, `Turing.recordRun_trans`, `Turing.recordRun_mono`, `Turing.recordStepSnapshot_empty`.
