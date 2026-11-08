<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universalRelation_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output at Checkpoints

**Claim.** Whenever the checkpoint relation holds between a source configuration and its corresponding universal-machine configuration, their output words are equal.

**Proof.** Unpack the checkpoint relation. It identifies the destination with a right-extended universal simulation configuration built from the source configuration. By definition, that simulation configuration copies the source output unchanged, and the right extension also preserves output. Thus the two output words are equal.
