<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.tapeRow_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a single block

**Claim.** For any configuration, integer coordinate, and read flag, the block encoding that coordinate has length $k$.

**Proof.** A single block is formed by mapping one entry for each element of `List.finRange k`. This list has length $k$, and mapping preserves length. Therefore the block has length $k$, independently of the entries and read flag.
