<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockStageCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Live Clock Step

**Claim.** If $c$ has state $q$, then one schedule-machine step from its clock-stage configuration equals the clock-stage configuration of the masked machine after one step from $c$.

**Proof.** The clock-stage state is the clock phase carrying $q$. In that phase, the schedule machine applies $W$'s transition using the input read replaced by false and the original work-tape reads decoded from the encoded tapes. The input-read preservation fact `clockStageCfg_input` and the work-read decoding fact `clockStageCfg_work` identify these arguments with exactly those used by the masked machine. Compare the resulting configuration fields: the input-head movement is shared; each original work-tape write and movement is copied, with Boolean symbols encoded as tagged bits; and the state advances to the clock phase for the new state, or to reset-start if the transition halts. If the transition emits a bit, the schedule machine appends its tagged version to the captured output tape. The tape update is exactly the update at the next output coordinate, by `clockTape_append`. If no bit is emitted, the tape and output-head position stay fixed. The added unary and guide tapes retain their required contents and positions, while the budget head advances precisely when output is appended. The output fields are empty in both clock-stage encodings. Hence the configurations agree field by field.

**Key facts.** `Complexity.clockStageCfg_input`, `Complexity.clockStageCfg_work`, `Complexity.clockTape_append`.
