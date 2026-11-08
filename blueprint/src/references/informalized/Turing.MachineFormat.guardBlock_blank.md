<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardBlock_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank input halts the guard scan

**Claim.** At the right blank cell of the input, one step of the guard machine in any phase reaches the halting state at that same cell, leaving the output unchanged.

**Proof.** At the right boundary, the input symbol is blank. Thus the guard machine's transition is the input-only action that halts and makes no head movement. The general step rule for an input-only action (Turing.step_of_inputMoveAction) identifies the resulting state and head position; a zero movement leaves the position fixed (Turing.moveInputPos_zero). Since the action writes nothing and emits no output, the work tapes and output are unchanged, giving the stated configuration.

**Key facts.** `Turing.step_of_inputMoveAction`, `Turing.moveInputPos_zero`.
