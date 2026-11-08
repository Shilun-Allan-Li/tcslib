<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_layout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Configuration Layout

**Claim.** Embedding a configuration into the first $k$ tapes and assigning the additional tape content $ct$ and head position $cp$ gives the clock configuration with the same state and input position.

**Proof.** Use the configuration-embedding characterization (`embedEmitCfg_eq`). The embedded and target configurations have the same state and input position; their outputs agree because the added prefix is empty. Each of the original $k$ tapes is selected by the embedding and retains its content and head position. For the remaining tape, induction on its index using the last-index decomposition shows it is the additional tape: it is outside the embedding's range, and its assigned content and head position are exactly $ct$ and $cp$. Thus all configuration components agree.

**Key facts.** `Turing.embedEmitCfg_eq`.
