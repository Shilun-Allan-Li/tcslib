<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleQueryWindow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Query Tape Window

**Claim.** If cell $r$ of the query tape is blank, then blanking cell $-1$ leaves the tape equal to the buffer holding the query string at every integer position from $-1$ through the length of that string.

**Proof.** Let $n$ be the least natural number whose query-tape cell is blank, which exists by the hypothesis at $r$, and form the length-$n$ word $z$ by reading cells $0$ through $n-1$. Minimality of $n$ makes every one of those cells nonblank, so each contains the corresponding letter of $z$; cell $n$ is blank by the choice of $n$. The query-string characterization from these consecutive cells and the blank cell then identifies the query string with $z$ (`Turing.OracleTM.queryString_eq_of_cells`). For $p=-1$, the update blanks that cell, as does the buffer tape at negative positions. For $p\ne-1$ in the stated interval, $p\ge0$, so the update does not change cell $p$ and the buffer-tape value is the list lookup at index $p$. If that index is below $z$'s length, the cell contains the corresponding letter; if it is not, the upper bound forces it to be exactly the length, where the cell is blank. The buffer-tape natural-index identity (`Turing.FinTM.bufferTape_nat`) identifies these values in both cases.

**Key facts.** `Turing.OracleTM.queryString_eq_of_cells`, `Turing.FinTM.bufferTape_nat`.
