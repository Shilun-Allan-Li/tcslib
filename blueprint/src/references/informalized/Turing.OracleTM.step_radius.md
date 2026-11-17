<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.step_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step tape radius bound

**Claim.** If the head on a work tape is within distance $n$ of the origin and all cells at distance at least $n$ are blank, then after one step the head is within distance $n+1$ and all cells at distance at least $n+1$ are blank.

**Proof.** First bound the new head position. The head moves by at most one in a step (`Turing.OracleTM.workTapePos_step_le`), so the triangle inequality together with the assumed bound gives $|p_i'|\le |p_i|+1\le n+1$. Now take any cell $z$ with $|z|\ge n+1$. It cannot be the old head position: if it were, the hypothesis $|p_i|\le n$ would contradict $|z|\ge n+1$. A step leaves every cell away from the old head unchanged (`Turing.OracleTM.workTapes_step_eq_of_ne`); since $|z|\ge n$, the original cell was blank by hypothesis. Thus every such cell remains blank.

**Key facts.** `Turing.OracleTM.workTapePos_step_le`, `Turing.OracleTM.workTapes_step_eq_of_ne`.
