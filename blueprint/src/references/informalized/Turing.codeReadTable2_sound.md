<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadTable2_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-tape table decoding is sound

**Claim.** Whenever the two-tape table reader returns a table $t$ and suffix $r$ on input $x$, the input is the serialization of $t$ followed by $r$.

**Proof.** Use the soundness of the vector reader (`codeReadVec_sound`) to express the input as the ordered concatenation of the encodings of the state rows, followed by $r$. Each state row is decoded by three nested symbol-row readers; apply symbol-row soundness (`codeReadSymbols_sound`) at each level to expand those rows into their ordered symbol entries. The innermost entries are actions, and action-reader soundness (`codeReadActionK_sound`) replaces each successful action read by its action encoding followed by the next suffix. Combining these nested decompositions in their original order gives exactly the table serialization of $t$, followed by $r$.

**Key facts.** `Turing.codeReadActionK_sound`, `Turing.codeReadSymbols_sound`, `Turing.codeReadVec_sound`.
