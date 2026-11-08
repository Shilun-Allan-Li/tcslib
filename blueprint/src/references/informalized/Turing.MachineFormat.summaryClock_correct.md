<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.summaryClock_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary clock correctness

**Claim.** Starting the summary clock at configuration $c$ with the summary of its current output gives true exactly when the configuration reached after $t$ steps is halted and its output has summary true.

**Proof.** Induct on the number of steps. At zero steps, the clock checks whether the current configuration is halted and whether its supplied output summary equals `some true`; the run at time zero is the original configuration (`runFrom_zero`), so this is exactly the claimed condition. For a successor number of steps, the clock first advances the machine by one step and updates the summary with the symbol emitted in that step. The output of a machine step is the old output followed by that emitted symbol (`step_output`), and the summary of such an appended output is obtained by applying `summaryEmit` to the old summary and the emitted symbol (`outputSummary_append`). Thus the recursive clock call is precisely the induction hypothesis applied to the configuration after one step and its updated output summary. The run-after-successor identity (`runFrom_succ_eq_step`) identifies its endpoint with the configuration after the full number of steps, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.step_output`, `Turing.StepBlock.outputSummary_append`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
