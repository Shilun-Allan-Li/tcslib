<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_read_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Recorded Fields

**Claim.** Starting at the position-skip stage with both buffers holding the input-position digits, the record-processing machine reads the configuration fields and tag and reaches the specified read-exit snapshot within $10(k+3)(L+1)$ steps. It avoids both verdict states before the final step and keeps every work-tape head within distance $L+1$ of its initial position.

**Proof.** Write $f_0,f_1,\ldots,f_{k+2}$ for the fields of the record: state, input position, the $k$ work tapes, and tag. The record-at hypothesis identifies each field, including the separating blank positions, with its corresponding interval on tape 0. The field-offset bound ensures each scan and return stays within the joined record; the record-length fact gives $k+3$ fields.

1. From the position-skip snapshot, the machine skips the input-position field and enters the first work-tape read. For each work-tape field, a forward scan folds over its cells to recover the symbol under the simulated head and whether that head is at either edge of the represented window. The fold identity for this scan follows from the in-window hypothesis (`recordStep_tape_fold`). After each scan the machine skips to the next field. The scan and skip run results give the stated endpoint, prevent premature exit from each phase, and bound head movement (`recordStep_scan_preserves`, `skipTM_run_ofCfg`, `recordStep_phase_run`).

2. Once the work-tape fields are read, the machine scans the final field to recover the tag. It then returns across the record’s separators, one field at a time, to the origin, where the phase transition selects the read-exit control from the collected data. The backward-skip run result supplies the return endpoint and head bound (`skipBackTM_run_ofCfg`, `recordStep_phase_run`).

3. There are $k$ work-tape read-and-skip rounds, each costing at most $3|f_j|+5$ steps, and each field’s length is bounded by $L$ through the field-offset estimate. The initial skip, tag scan, and return contribute the remaining costs; summing them gives at most $10(k+3)(L+1)$. Concatenating the phase runs preserves avoidance of both verdict states before the endpoint and the radius $L+1$ bound (`recordRun_trans`).

**Key facts.** `Turing.cfgRecord_length`, `Turing.fieldOffset_add_length_le`, `Turing.fieldsTape_field`, `Turing.recordStep_scan_preserves`, `Turing.skipTM_run_ofCfg`, `Turing.recordStep_phase_run`, `Turing.recordStep_tape_fold`, `Turing.recordStepReadData_succ`, `Turing.scanResult_fold`, `Turing.recordRun_trans`, `Turing.recordRun_zero`, `Turing.fieldOffset_succ`, `Turing.skipBackTM_run_ofCfg`, `Turing.fieldOffset_cons_succ`.
