<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonBlankLift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation with Blank Auxiliary Tapes

**Claim.** Embedding a machine into a larger collection of work tapes preserves its run from an all-blank configuration: after any number of steps the larger-machine configuration is the embedding of the original configuration, with auxiliary tapes blank and their heads at zero, and with the output unchanged.

**Proof.** Apply the general run-preservation theorem for an embedded machine (`Turing.embedEmitTM_runFrom`) to the initial configuration. To put that initial configuration in the theorem’s required embedded form, use the equality of word configurations under embedding (`Turing.MachineFormat.canonEmbedWords`): choose the same empty word on every larger tape, so the selected tapes agree with the original empty tapes and all unselected tapes agree with the ambient empty tapes. The run theorem then identifies every later configuration with the embedding of the original run; the ambient blank tapes, zero head positions, and empty output prefix give the stated description.

**Key facts.** `Turing.MachineFormat.canonEmbedWords`, `Turing.embedEmitTM_runFrom`.
