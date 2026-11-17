<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.FinTM.bufferTape_map_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decode an embedded buffer tape

**Claim.** Reading the embedded-word buffer tape at cell $p$ and decoding through $e$ yields exactly the buffer-tape symbol for $w$ at that cell.

**Proof.** If $p$ is negative, both tape values are absent. If $p$ is nonnegative, the embedded tape value is the optional entry of the mapped word at the corresponding natural index, hence is the image under $e$ of the original optional entry. When the entry is absent, decoding remains absent. When it is present, it is $e$ of a Boolean; the decoder returns that Boolean, since the embedding is injective and its two Boolean images are distinguishable. Therefore decoding recovers exactly the original optional tape value.
