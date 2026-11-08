<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_tape_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorded Tape Update Run

**Claim.** Starting in the forward writing phase for tape $i$, the recording machine completes the tape update in exactly $4(2s+1)+6$ steps, avoids both verdict states before the endpoint, keeps every work-tape head within distance $2s+2$ of its initial position, and leaves the updated tape record at the endpoint while preserving cells outside its specified interval.

**Proof.** Let the old record be the length-$2s+1$ word for tape $i$, and let $a$ be the action prescribed by the simulated machine from the stored data. The proof divides the run into two scan phases. First, the forward scan applies the prescribed write to each record cell. The scan-run formula (`Turing.scanTM_run_ofCfg`) gives the endpoint configuration and its time and head bounds; the pointwise write identity (`Turing.recordStep_cell_write`), together with the scan-map identity (`Turing.scanResult_map`), identifies the resulting word as the old record with the marked cell updated. The initial buffer hypothesis ensures the simulator’s tape contains precisely this word over the scan interval; the endpoint blank and unchanged-cell cases follow from that same buffer description.

Next, the shift phase scans the written word, moving its head mark left, keeping it fixed, or moving it right according to the action. The recorded-word update identity (`Turing.recordStep_tape_word`) identifies the resulting word with the record of the configuration obtained by applying $a$. Apply the scan-run formula again to obtain the second phase’s endpoint and head bounds. The phase-run result (`Turing.recordStep_phase_run`) promotes each of these scan executions to a run of the full recording machine, including avoidance of the verdict states before each phase endpoint. The two runs concatenate by the run-composition result (`Turing.recordRun_trans`). Each phase takes $2(2s+1)+2$ steps, so together they take $4(2s+1)+6$. The head bound holds throughout both phases, and the final tape patch changes only tape $0$ within the interval from its initial head position through that position plus $2s$.

**Key facts.** `Turing.scanTM_run_ofCfg`, `Turing.recordStep_cell_write`, `Turing.scanResult_map`, `Turing.recordStep_tape_word`, `Turing.recordStep_phase_run`, `Turing.recordRun_trans`.
