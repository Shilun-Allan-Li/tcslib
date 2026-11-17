<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeEraseSymbols -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol row erasure

**Claim.** For any type $A$, reader $r$ returning an $A$-value and suffix or failure, and bit string $x$, discarding the three-entry row decoded by the row reader gives exactly three successive applications of the value-discarding version of $r$.

**Proof.** The row reader applies $r$ three times in sequence, each time to the suffix left by the preceding read, and then packages the three values into a row. After discarding that row, only the final suffix matters. The repeated skipper performs those same three reads of suffixes while discarding each value. Expanding the reader, the repeated skipper, and their option binds therefore gives the same computation, including failure at any of the three stages.
