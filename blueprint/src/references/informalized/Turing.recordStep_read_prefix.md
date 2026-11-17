<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_read_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Recorded Prefix

**Claim.** The record-processing machine reads the recorded state and input-position fields, then copies the binary input-head position word into both buffers. It reaches the position-skip stage with the position-field head shifted by two, in exactly $6|w|+17$ steps, without visiting either verdict state before the final step and with every work-tape head within distance $L+1$ of its initial position.

**Proof.** 1. Write $L$ for the joined record length and $w$ for the encoded input-head position. The record has $k+3$ fields, and the position field begins at offset two. The field-offset bound and the field-reading identity (`fieldOffset_add_length_le`, `fieldsTape_field`) therefore show that the designated record tape presents the state word and position word to the machine exactly as buffers containing those fields would. The blankness of the other tapes lets each intermediate snapshot be represented with empty buffers (`recordStepSnapshot_empty`).

2. The initial scan reads the state cell, stores the configuration's state in the step data, and reaches the state-skip stage in five steps. The state-scan run theorem supplies this exact run and its head bound (`recordStep_state_run`). The machine then skips the state field to the beginning of the position field in three more steps: the skip-run theorem gives the two-step scan, and the phase transition contributes the third (`skipTM_run_ofCfg`, `recordStep_phase_run`).

3. The position scan folds the binary digits, counting their length up to two and checking whether all digits are zero. The binary-digit value theorem identifies the represented number with the input-head position, while the position-width bound ensures that this number fits in the chosen digit width (`record_digits_value`, `record_pos_lt`). Thus the scan data records whether the width is one and whether the position is zero; the scan-preservation theorem gives the exact scan and its head bound (`recordStep_position_fold`, `recordStep_scan_preserves`). After the phase transition, the control is at the copy stage.

4. Each copy pass takes $2|w|+2$ steps: it copies the source word while moving forward, then returns the heads to their anchors. The copy-run theorem verifies the resulting buffer and bounds all head movement (`copyTM_run_ofCfg`). Applying this first to buffer 1 and then to buffer 3, with one phase transition after each pass, leaves both buffers equal to $w$ and the control at position-skip. The phase-run theorem preserves the absence of verdict states across these transitions (`recordStep_phase_run`).

5. The total is $5+3+(2|w|+3)+(2|w|+3)+(2|w|+3)=6|w|+17$. The run-composition theorem combines the successive segments while preserving their no-verdict and head-radius bounds (`recordRun_trans`). Every segment keeps each head within $L+1$ of its initial position, so the composed run has the stated bound.

**Key facts.** `Turing.fieldOffset_add_length_le`, `Turing.fieldsTape_field`, `Turing.recordStepSnapshot_empty`, `Turing.recordStep_state_run`, `Turing.skipTM_run_ofCfg`, `Turing.recordStep_phase_run`, `Turing.record_digits_value`, `Turing.record_pos_lt`, `Turing.recordStep_position_fold`, `Turing.recordStep_scan_preserves`, `Turing.copyTM_run_ofCfg`, `Turing.recordRun_trans`.
