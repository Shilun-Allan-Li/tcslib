<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.embedCfg_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Update and Embedding

**Claim.** Replacing a configuration’s output by a word and then embedding it gives the same configuration as embedding first and replacing the output by that word.

**Proof.** The embedding copies the input-head position, work tapes, and work-tape head positions unchanged, and maps only the state while copying the output. Replacing the output before or after this operation therefore leaves all fields equal.
