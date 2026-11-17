<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_transfer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer Between Stage and Limit Oracles

**Claim.** On the specified unary input, running $N_i$ with the union of all stage-positive sets halts within the time bound with output $y$ if and only if running it with the stage-$i$ positive-set oracle does so.

**Proof.** The consistency property says that every query made during the run with the stage-$i$ oracle receives the same membership answer from the union oracle. The oracle-run agreement theorem (Turing.OracleTM.runFrom_eq_of_agree_queriesWithin) therefore makes the configurations after the specified number of steps identical for the two runs. In particular, their halting states and outputs coincide, which gives both directions of the claimed equivalence.

**Key facts.** `Complexity.stage_consistent`, `Turing.OracleTM.runFrom_eq_of_agree_queriesWithin`.
