<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.tapeBlocks_buffer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer value

**Claim.** The three-block assembly of the left family, buffer value, and right family takes the buffer value at its middle buffer position.

**Proof.** By definition, the assembly uses the left family on the first block and, after that block, uses a second case split for the buffer and right blocks. The index in the statement lies in the buffer block, so this case split returns the constant value $b$.
