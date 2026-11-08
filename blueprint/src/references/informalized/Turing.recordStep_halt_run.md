<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_halt_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halted-State Record Run

**Claim.** If the record data state is empty, the assembled record-step machine clears both buffers and reaches the true-verdict phase after $4|w|+6$ steps, without reaching either verdict state earlier and with every work-tape head within distance $|w|+1$ of its initial position.

**Proof.** The halted-state hypothesis selects the two-stage halt-cleanup path. First clear tape 1 from the buffer $w$, keeping the tape-3 buffer $w$ intact. The clear-snapshot theorem (`Turing.recordStep_clear_snapshot`) gives the endpoint with tape 1 empty and rules out an earlier `done` state; the head-bound theorem (`Turing.recordStep_clear_heads`) controls every tape during this part. The phase-run theorem (`Turing.recordStep_phase_run`) packages it as the `clearHaltB` stage and advances to `clearHaltD`. Next clear tape 3, now with the tape-1 buffer empty. The same clearing and head-bound results give the second endpoint, with both buffers empty. A second application of the phase-run theorem advances to the true-verdict phase and ensures neither verdict was reached before that final transition. Each clearing stage takes $2|w|+2$ steps followed by one host-phase transition. Concatenating the two runs with the run concatenation theorem (`Turing.recordRun_trans`) yields total length $(2|w|+3)+(2|w|+3)=4|w|+6$ and combines their verdict-avoidance and head-bound assertions.

**Key facts.** `Turing.recordRun_trans`, `Turing.recordStep_clear_heads`, `Turing.recordStep_clear_snapshot`, `Turing.recordStep_phase_run`.
