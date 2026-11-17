<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_lastLayout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Tape Layout

**Claim.** Embedding a one-tape configuration as the last tape, alongside the first $k$ tapes of the given configuration, produces the corresponding clock configuration when the input positions and outputs agree.

**Proof.** Apply the configuration-embedding characterization (`embedEmitCfg_eq`). The embedded one-tape configuration has the same state as the target clock configuration by definition, and the input positions agree by hypothesis. The output condition follows from the assumed equality of outputs and the empty prefix. Its only selected tape is tape zero, which the embedding `lastEmb` sends to the final tape; the tape content and head position therefore agree with the clock tape taken from the one-tape configuration. Every other tape lies outside the embedding's range and retains the given configuration's tape content and head position. These component agreements establish equality of the configurations.

**Key facts.** `Turing.embedEmitCfg_eq`, `Turing.lastEmb_apply`.
