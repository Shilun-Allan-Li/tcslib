<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: Turing.FinTM.inputCall_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-copy machine run

**Claim.** For positive work-tape count, the input-copy machine finishes after $2|x|+2$ steps in the done state, with the input word on work tape $0$, all other work tapes empty, all work-tape heads at the origin, and the standard input-head and output configuration.

**Proof.** Use the run calculation for the input-copy machine from a configuration whose state is sweep and whose input head is at position one (`Turing.inputCopyTM_run_ofCfg`). It identifies the final state as done and says that the only changed tape is the selected tape: on the interval from the initial head position through the input word's length, its contents are given by the buffer tape containing $x$. Here the selected tape is index zero, the initial tape contents are empty, and the initial head position is zero. The buffer of the empty word is nowhere defined (`Turing.FinTM.bufferTape_nil`), so every unselected tape remains empty. On tape zero, the described interval contains exactly the cells holding $x$, and the final head is at the origin. The run calculation's configuration fields, together with the definition of the standard word configuration, therefore give the claimed equality.

**Key facts.** `Turing.inputCopyTM_run_ofCfg`, `Turing.FinTM.bufferTape_nil`.
