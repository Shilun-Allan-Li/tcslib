<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecordOutput_compute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorder Trajectory Output

**Claim.** The recorder output machine computes the serialized recorder rows through time $T$ on the packed input $x$ in the stated number of steps.

**Proof.** Apply the recorder-completion result (`clRecord_complete`) to obtain a time $a$ at which the recorder machine has reached its return state, with its output still empty and its designated output tape containing the complete record, positioned at the end of that word. Its time is at most $2|x|+4+((k'+4)(3W+7)+(4F+7)(T+1)^2)$. The selected-tape embedding facts (`embedEmitCfg_selected_tape` and `embedEmitCfg_selected_pos`) identify the corresponding tape and head position in the larger machine configuration with those of the recorder configuration. The output wrapper can therefore replay that tape to its output, producing exactly the record and halting after a further $2R+4$ steps, where $R$ is the record length; this is the output-conversion result (`clOutput_compute`). The record is at most $2F(T+1)^2$ bits long: `clRecords_length` bounds its length by $(T+1)F(2T+2)$, which simplifies to that expression. Combining the recorder time and replay time with `clRecord_replay_budget` gives the claimed total bound. Finally, the computation persists at every later step because the recorder return state is idle (`clRecord_idle`), so the wrapper's computation at the larger prescribed time follows by time monotonicity (`ComputesInTime.mono`).

**Key facts.** `Complexity.clRecord_complete`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Complexity.clOutput_compute`, `Complexity.clRecords_length`, `Complexity.clRecord_replay_budget`, `Complexity.clRecord_idle`, `Turing.FinTM.ComputesInTime.mono`.
