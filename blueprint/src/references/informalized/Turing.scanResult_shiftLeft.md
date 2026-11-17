<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.scanResult_shiftLeft -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left-Shift Scan Output

**Claim.** The left-shift scan returns the first get-value of the word, or b₀ if it is empty, and replaces each symbol by setting its stored value to the next symbol's get-value, using b₀ at the end.

**Proof.** Apply the right-shift scan result to the reversed input. The first pass of the leftward scan is a keep scan, so it leaves the input unchanged (`Turing.scanResult_keep`); the remaining backward pass can therefore be expressed as the corresponding right-shift computation on the reversed word (`Turing.scanResult_shiftRight`). Reversing its output word changes the pairing of symbols and stored values into the left-shift pairing: each symbol is paired with the get-value of its successor, and the last receives b₀ (`Turing.shiftLeft_list`). The state is the last get-value on the reversed word, which is the first get-value on the original word; in the empty case both conventions return b₀.

**Key facts.** `Turing.scanResult_keep`, `Turing.scanResult_shiftRight`, `Turing.shiftLeft_list`.
