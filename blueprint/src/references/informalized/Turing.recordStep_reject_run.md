<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_reject_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejecting an Out-of-Range Recorded Step

**Claim.** When the recorded step data indicate an outward move beyond a recorded work-tape boundary, the record-processing machine clears the first buffer and reaches the rejecting verdict in exactly $2|w|+3$ steps. Before the final step it visits neither verdict state, and every work-tape head remains within distance $|w|+1$ of its initial position.

**Proof.** The out-of-range condition directs the control to the rejecting branch. Starting with $w$ on the first buffer and an empty second buffer, the branch clears the first buffer. The clearing-run result gives the exact endpoint, shows that the clearing phase does not reach its done state early, and bounds head movement (`recordStep_clear_snapshot`). Its head-bound companion gives the required radius $|w|+1$ throughout that phase (`recordStep_clear_heads`).

At the end of the clearing phase, the phase transition enters the rejecting verdict control. The phase-run theorem transfers the run to the full record-processing machine, preserving the fact that no verdict state was visited earlier (`recordStep_phase_run`). The clearing takes $2|w|+2$ steps and the final transition takes one, for a total of $2|w|+3$.

**Key facts.** `Turing.recordStep_clear_snapshot`, `Turing.recordStep_clear_heads`, `Turing.recordStep_phase_run`.
