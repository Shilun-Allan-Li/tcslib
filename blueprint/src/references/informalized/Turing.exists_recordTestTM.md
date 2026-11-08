<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.exists_recordTestTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Testing a Configuration Record

**Claim.** A one-work-tape deterministic machine can test any predicate of a configuration's state and tag by scanning the joined record, then enter the corresponding yes or no state without visiting either verdict earlier, with linear time and head movement.

**Proof.** Let the fields of the record be $f_0,\ldots,f_{k+2}$. For each field, the proof shifts the tape head to that field's offset. The field-offset bound (`fieldOffset_add_length_le`) keeps every such shift within the total record length, while `fieldsTape_field` identifies the symbols seen there with the field's actual contents. A scan of a field folds the appropriate update over its symbols (`scanResult_fold`), and `scanTM_run_ofCfg` supplies the run and its head bound. The special one-symbol state field is scanned to recover the configuration state; the final one-symbol tag field is scanned to evaluate the predicate on that state and tag.

The machine traverses the fields forward and then backward. Each forward transition skips one field using `skipTM_run_ofCfg`; each backward transition returns across one field using `skipBackTM_run_ofCfg`. The field-offset successor identity (`fieldOffset_succ`) verifies that these traversals land at adjacent fields. Induction on the field index composes these runs with `recordRun_trans`; `recordRun_zero` supplies the zero-length base run. The phase controller connects each scan and skip while preserving the intended phase progression (`phaseHostTM_run`), and `recordRun_tagged` records that neither verdict is entered during these intermediate phases. The final traversal returns to the original head position and enters the verdict determined by the predicate. Each field costs at most a constant times its length, and there are $k+3$ fields whose total joined length is the record length (`cfgRecord_length`). Enlarging the constant gives the stated linear time and head-distance bounds.

**Key facts.** `Turing.cfgRecord_length`, `Turing.fieldOffset_add_length_le`, `Turing.fieldsTape_field`, `Turing.scanTM_run_ofCfg`, `Turing.scanResult_fold`, `Turing.skipTM_run_ofCfg`, `Turing.skipBackTM_run_ofCfg`, `Turing.fieldOffset_succ`, `Turing.phaseHostTM_run`, `Turing.recordRun_tagged`, `Turing.recordRun_trans`, `Turing.recordRun_zero`.
