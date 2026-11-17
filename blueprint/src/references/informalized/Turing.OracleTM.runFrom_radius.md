<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Support Radius

**Claim.** If a tape head begins within distance $n$ of the origin and all cells at distance at least $n$ are blank, then after $s$ steps the head is within distance $n+s$ and every cell at distance at least $n+s$ is blank.

**Proof.** Induct on $s$. At time zero, the head bound and blank-cell condition are exactly the hypotheses. For the successor, the run successor equation (`Turing.OracleTM.runFrom_succ_eq_step'`) expresses the next configuration as one step from the current one. Apply the one-step radius theorem (`Turing.OracleTM.step_radius`) to the induction bounds with radius $n+s$. It increases the radius by one, giving the claimed head bound and blankness outside radius $n+s+1$.

**Key facts.** `Turing.OracleTM.runFrom_succ_eq_step'`, `Turing.OracleTM.step_radius`.
