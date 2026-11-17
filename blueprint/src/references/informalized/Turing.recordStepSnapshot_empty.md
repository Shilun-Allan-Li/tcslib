<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStepSnapshot_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Snapshot on Blank Tapes

**Claim.** When every tape except tape zero is blank, the snapshot with zero displacement and empty buffers has the stated configuration fields and unchanged work-tape contents and head positions.

**Proof.** The state, input-head position, output, and head positions agree directly from the snapshot definition: the new state is $q$, and zero displacement leaves every head where it was. For tape contents, tapes other than $1$ and $3$ retain their original contents. On tapes $1$ and $3$, the empty buffer contributes no symbol at any relative position, so the snapshot gives a blank cell; the hypothesis says those tapes were already blank. Tape zero is unchanged. Hence every work-tape cell agrees, and the configurations are equal.
