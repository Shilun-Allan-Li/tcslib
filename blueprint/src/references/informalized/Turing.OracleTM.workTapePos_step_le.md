<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.workTapePos_step_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on work-head movement

**Claim.** For any work tape, the head position changes by at most one in absolute value after one step of the oracle machine.

**Proof.** Unfold the step definition and split on whether the configuration is halted, and then, when it is not halted, whether its state is the query state. In the halted case the configuration is unchanged, so the displacement is zero. In the query-state case the oracle step changes only the state, again leaving the head position unchanged. In every other state the machine applies its transition action; an action moves each work-tape head by at most one (`Turing.workTapePos_apply_le`).

**Key facts.** `Turing.workTapePos_apply_le`.
