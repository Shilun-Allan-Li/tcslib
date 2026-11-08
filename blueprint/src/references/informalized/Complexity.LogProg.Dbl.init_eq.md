<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.init_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Representation

**Claim.** The specified machine's initial configuration equals the represented configuration with state $vU0$, input-head position $1$, the binary expansion of zero on the work tape, head position zero, and empty output.

**Proof.** The initial configuration and the stated represented configuration agree immediately in their state, input-head position, work-tape head position, and output. For the work-tape contents, both are the everywhere-blank tape: the binary expansion of zero is empty, so the buffer tape stores no symbol at any cell (`Nat.zero_bits`). Extensionality of configurations and of the tape functions gives the equality.
