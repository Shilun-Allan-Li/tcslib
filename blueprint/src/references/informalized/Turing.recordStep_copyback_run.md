<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_copyback_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copyback Run Bound

**Claim.** The assembled record-step machine copies the source buffer into the first work tape in $4|w|+6$ steps, reaches the skip-new-position phase with empty buffers, avoids both verdict states before the final step, and keeps every work-tape head within distance $|w|+1$ of its original position.

**Proof.** The proof divides the run into three consecutive parts. First, the copy machine copies the word from tape 1 back to tape 0 and returns both heads to their origins. Its copy-run theorem (`Turing.copyTM_run_ofCfg`) gives the resulting configuration, the absence of its terminal state at earlier times, and head bounds. With the source buffer matched to $w$, the copied tape contents are exactly the designated updated snapshot. The phase-run theorem (`Turing.recordStep_phase_run`) then packages this copy phase as the `copyBack` stage of the assembled machine and advances to the `clearB` stage. Its phase-cut hypothesis is discharged by the copy machine's preterminal-state result; the phase is not a verdict phase, and the copy-run head bounds imply the required radius bound. Second, clear the buffer on tape 1. The clear-snapshot theorem (`Turing.recordStep_clear_snapshot`) gives the exact emptied-buffer endpoint and rules out premature completion, while the clear-head bound (`Turing.recordStep_clear_heads`) controls all heads. Applying the phase-run theorem again advances from `clearB` to `skipNewPos`, with no verdict state reached in between and with the same radius bound. Each phase takes $2|w|+2$ machine steps plus one transition that advances the host phase. Finally, concatenate the two phase runs using the run concatenation theorem (`Turing.recordRun_trans`). Their total duration is $(2|w|+3)+(2|w|+3)=4|w|+6$, and their shared intermediate configuration ensures the endpoint, verdict avoidance, and head bounds combine as stated.

**Key facts.** `Turing.copyTM_run_ofCfg`, `Turing.recordStep_phase_run`, `Turing.recordStep_clear_snapshot`, `Turing.recordStep_clear_heads`, `Turing.recordRun_trans`.
