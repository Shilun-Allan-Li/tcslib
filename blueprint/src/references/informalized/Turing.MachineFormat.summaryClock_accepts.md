<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.summaryClock_accepts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary clock recognizes acceptance

**Claim.** The summary clock started on the initial configuration with no output summary returns true exactly when the machine halts after $t$ steps with output $[true]$; the computation definition also records that the machine uses some finite amount of work-tape space.

**Proof.** The correctness theorem for the summary clock (`summaryClock_correct`) identifies its value, when initialized with the summary of the current output, with the conjunction that the configuration after $t$ steps is halted and its output summary is `some true`. The initial output is empty, whose summary is none, so this applies to the stated initialization. By the output-summary characterization (`outputSummary_true`), having summary `some true` is equivalent to the output being exactly $[true]$. Finally, the finite-machine computation characterization (`computesInTime_iff`) says that computing that output in time $t$ is equivalent to halting at that time with that output; its existential space witness supplies the stated finite space use. Combining these equivalences proves both directions.

**Key facts.** `Turing.MachineFormat.summaryClock_correct`, `Turing.StepBlock.outputSummary_true`, `Turing.FinTM.computesInTime_iff`.
