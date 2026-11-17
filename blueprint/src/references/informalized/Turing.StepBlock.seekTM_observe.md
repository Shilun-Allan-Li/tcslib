<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.seekTM_observe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Observation in the Search Machine

**Claim.** Starting from the recording machine's initial state in the observe control state, the search machine reads the input and work-tape symbols to determine their rank, then reaches the state carrying that rank after two steps. The summary head advances by two, done is not reached earlier, and the stated input, tape, output, and other-head data are preserved through time two.

**Proof.** Let $r$ be the rank determined by the symbols scanned on the input and the first $k$ work tapes. In the first transition, the observe control reads those symbols, stores $r$ in the control, and moves the summary head one cell to the right. The tape-action transition formula (`Turing.step_of_tapeAction_move`) makes explicit that this move changes only the indicated head position and control state. A second transition in the advance state moves the summary head one more cell and changes the control to the state carrying $r$. The summary and table tapes are distinct (`summary_ne_table`), so these two moves do not affect any other work-tape head. Thus the two-step run has the asserted configuration. At times zero and one the control is observe or advance, never done; checking these two times also gives the preservation claims through time two.

**Key facts.** `Turing.step_of_tapeAction_move`, `Turing.StepBlock.summary_ne_table`.
