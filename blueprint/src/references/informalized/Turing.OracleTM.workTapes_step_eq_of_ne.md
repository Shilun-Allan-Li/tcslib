<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.workTapes_step_eq_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unscanned work cells are unchanged

**Claim.** For any tape and any cell other than the head's current position, the cell's content is unchanged by one step of the oracle machine.

**Proof.** Unfold the step and split into the halted case, the query-state case, and the remaining transition case. A halted step leaves the configuration unchanged, and a query-state step updates only the state, so the cell is unchanged in both cases. In the remaining case, the machine applies its transition action. An action leaves each cell away from that tape's head unchanged (`Turing.OracleTM.apply_workTapes_eq_of_ne`); the given inequality identifies $z$ as such a cell.

**Key facts.** `Turing.OracleTM.apply_workTapes_eq_of_ne`.
