<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadTable2_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-tape table decoding

**Claim.** For every $n$, transition table $t$, and bit string $x$, the two-tape table reader reads the serialization of $t$ followed by $x$ and returns $(t,x)$.

**Proof.** The table reader is built from three nested symbol-row readers inside a vector reader. First, each action is read from its own encoding followed by the remaining bits, by the prefix-inverse property of the action reader (`codeReadActionK_append`). Applying the symbol-row prefix-inverse property (`codeReadSymbols_append`) at each of the three scanned-symbol positions reconstructs the table entries for each state and input/work-tape symbol combination while preserving the remaining suffix. Finally, the vector prefix-inverse property (`codeReadVec_append`) performs this reconstruction across the states in order. The resulting function agrees with $t$ at every state and symbol triple, and the final suffix is $x$.

**Key facts.** `Turing.codeReadActionK_append`, `Turing.codeReadSymbols_append`, `Turing.codeReadVec_append`.
