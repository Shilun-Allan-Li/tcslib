<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_empty_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Input Record Run

**Claim.** When the record data is live and its width flag is true, the assembled record-step machine clears the destination buffer and reaches the apply phase with empty input data after $2|w|+3$ steps, without an earlier verdict and with all heads within distance $|w|+1$ of their initial positions.

**Proof.** The live-state and width hypotheses select the `clearEmptyD` branch of the read-exit phase. Clear tape 3, whose buffer is $w$, while leaving the other buffer $w$ unchanged. The clearing snapshot theorem (`Turing.recordStep_clear_snapshot`) supplies the endpoint with tape 3 emptied and guarantees that `done` was not reached at an earlier clearing step. The head-bound theorem (`Turing.recordStep_clear_heads`) controls every tape throughout this clearing pass. Apply the phase-run theorem (`Turing.recordStep_phase_run`) to the `clearEmptyD` stage: its endpoint is the host configuration in the apply phase with the input field reset to `none`. The earlier nonterminal-state property rules out a premature transition from that stage; the transition after the completed clear is precisely the specified apply phase. The phase-run result also transports the head bounds and excludes both verdict states before the final step. The clearing takes $2|w|+2$ steps and the host advances phase once, giving $2|w|+3$ steps in total.

**Key facts.** `Turing.recordStep_clear_snapshot`, `Turing.recordStep_clear_heads`, `Turing.recordStep_phase_run`.
