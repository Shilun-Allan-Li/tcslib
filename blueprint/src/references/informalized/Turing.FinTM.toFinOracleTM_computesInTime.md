<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleFinite.lean :: Turing.FinTM.toFinOracleTM_computesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Compilation Preserves Time

**Claim.** For every oracle language $O$, the machine obtained by viewing $M$ as an oracle machine computes $y$ relative to $O$ at time $t$ exactly when $M$ computes $y$ from the same input within $t$ steps.

**Proof.** The ordinary machine's time-computation predicate is equivalent to halting with output $y$ at time $t$ (`computesInTime_iff`). The oracle machine obtained from an ordinary machine has the same time-$t$ halting and output behavior: its computation predicate is equivalent to those same two conditions (`OracleTM.computesInTime_ofMultiTapeTM`). Combining these equivalences gives the result; the oracle language does not affect the simulation of this compiled machine.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.OracleTM.computesInTime_ofMultiTapeTM`.
