<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.exists_fieldsCopyTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine Copying Joined Fields

**Claim.** For every alphabet and natural number of fields, there are a finite-state deterministic two-work-tape machine, entry and exit states, and a constant satisfying the stated copying, first-exit, head-displacement, and final-configuration properties.

**Proof.** Fix the number of fields. The machine `rt_copyMachine` with states `rt_copyState` and designated entry and exit states is already accompanied by `rt_copy_run`, which proves the required run, time bound, absence of an earlier visit to the exit state, head-displacement bound, and final tape contents for every input satisfying the hypotheses. Choose the machine, states, and constant supplied by that result. Its state type is finite and decidable, so it also supplies the required finite-state data. The conclusion is exactly the asserted property.

**Key facts.** `Turing.rt_copy_run`.
