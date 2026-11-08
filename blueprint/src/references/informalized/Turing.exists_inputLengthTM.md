<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.exists_inputLengthTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine Computing Input Length

**Claim.** There exist a number of auxiliary work tapes, a finite-state deterministic binary Turing machine with entry and exit states, and a constant satisfying the stated time, first-exit, head-displacement, and final tape requirements for computing the binary representation of the input length.

**Proof.** Use the input-length machine with entry state `count` and exit state `done`, and take the constant to be 6. From a qualifying configuration, `inputLength_count` runs the counting phase for `x.length` rounds. It reaches a configuration whose input head is at the right boundary and records the binary digits of the input length, while keeping the first work-tape head within the stated interval. One step dispatches to the return phase. The machine then rewinds the input head to position 1 by `rewind_heads`; throughout that phase the work-tape heads remain fixed, and the return takes at most `x.length + 3` steps. The two run-composition identities, `runFrom_succ_eq_step'` and `runFrom_add`, combine these phases and give the asserted intermediate configuration and total time bound. The run reaches `done` by that bound. Choose the first time at which it is in `done`; `Nat.find` gives that this time is no later than the constructed finish and that the machine was not in `done` earlier. The exit configuration is stationary, so running from the first exit to the constructed finish changes nothing. The head bounds from the counting and rewind phases give the bound through the first exit, and the resulting tape contents and unchanged configuration components are those of the constructed finish.

**Key facts.** `Turing.inputLength_count`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.step_of_inputMoveAction`, `Turing.FinTM.rewind_heads`, `Turing.MultiTapeTM.runFrom_add`, `Turing.moveInputPos_zero`.
