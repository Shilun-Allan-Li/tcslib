<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleCall.lean :: Turing.OracleTM.queryString_bufferTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query String on a Buffer Tape

**Claim.** If the query tape of a configuration stores the buffer tape for $w$, then the configuration’s query string is $w$.

**Proof.** At every position $i<|w|$, the buffer tape contains the $i$-th symbol of $w$: the natural-index buffer-tape identity (`Turing.FinTM.bufferTape_nat`) identifies that cell with the corresponding list lookup. At position $|w|$, the buffer tape is blank, since the list has no symbol at that index. The theorem that these cell conditions determine the query string (`Turing.OracleTM.queryString_eq_of_cells`) now gives that the query string equals $w$.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.OracleTM.queryString_eq_of_cells`.
