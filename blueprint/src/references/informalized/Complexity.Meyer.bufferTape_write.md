<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.bufferTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing the next symbol

**Claim.** Updating the tape that stores $w$ at cell $|w|$ to contain $b$ yields the tape that stores the concatenation of $w$ with the one-symbol word $[b]$.

**Proof.** The tape for the concatenated word $w ++ [b]$ is exactly the update of the original tape at cell $|w|$ with value `some b`, by the append law for `bufferTape` (`bufferTape_append`). The claimed equality is this law read in the reverse direction.

**Key facts.** `Turing.FinTM.bufferTape_append`.
