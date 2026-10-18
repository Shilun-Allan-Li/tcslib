# NDCodes fill report

**Complete: 1/1 target proved.** `Turing.exists_effectiveNDMachineCode` is admission-free.
No proved-modulo citations, unfinished private helpers, requested shared lemmas, or escalations.

## Base and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch: `complexity/arora-barak-ch3-4`.
- Base: `1e9361b5fe2022594f5b62d6d48b629d88214794`.
- Working branch: `fill/ndcodes`; delivery commit: `152e9c4db52ac5b86be1698e4d7c6ec1ba39e6c8`.
- `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD` succeeded before source work (exit 0).
- The commits after the brief's ancestor changed no Lean sources. The actual base admission inventory matches all 43 named entries of `audits/logs/ndcodes-fill-base-sorries.txt`; no parallel fill had landed in this base.
- The only tracked file changed is `TCSlib/Complexity/TuringMachine/NDCodes.lean`. No rebase, push, or PR.

## Implementation and frozen statements

The new private `ndFormat : CodeFormat` uses `CodeNDTM`, a pair of `CodeTable2` tables with the false-choice table first, the frozen serializer, and guard 702. Its fallback is the one-state, silent, immediately halting NDTM.

1. `serialize_assemble` simplifies the frozen serialization using `actionBits₂_eq_actionBitsK`, as in the maintainer's probe.
2. `assemble_surj` reconstructs both choice tables and proves equality of every work-read function from its two `Fin 2` coordinates.
3. `codeReadTable2_append`, `codeReadTable2_sound`, and `codeEraseTable2` each compose twice. No parser, record reader, or generic loop is reimplemented.
4. Adding the two public 351-bit table lower bounds proves the 702-bit guard.
5. `codePrimRepeat` applied to `codePrimSkipTable2` proves the doubled skipper primitive recursive. The public `CodeFormat.decode_serialize_pad` and `CodeFormat.exists_canonizer` discharge the representation and effectivity fields.

The canonizer has the audited arbitrary length-only time bound. No polynomial-time claim is made.

**Every new source declaration:**

| Declaration | Visibility | Role |
|---|---|---|
| `Turing.ndFormat` | private | The third format instance, including all serialization, parsing, erasure, surjectivity, and guard laws. |

No new public declaration was added. A comment-stripped comparison verifies the ordered list of all seven existing public declarations, all their signatures, and all six non-target bodies unchanged. The target's signature is unchanged. The only code additions are the sanctioned import, the private format instance, and the target proof.

**Flagged changes permitted by the brief:**

- Import: exactly `TCSlib.Complexity.TuringMachine.MathlibBridge`; no other imports added.
- Module status paragraph: changed to proved, specifying the arbitrary time bound.
- Main-results tag for the target: changed to proved.
- Target's `(spec, fill pending …)` tag: changed to proved.
- Module **Fill appendix**: records completion of the historical item-8 obligation.
- Target docstring **Fill appendix**: identifies the route through `CodeFormat` and the primitive recursive doubled skipper; the original sketch is retained.
- The private instance has a statement docstring and a proof sketch.

## Verification

All Lean checks used the unchanged `scripts/lean_check_tree.sh`. No `lake build` was run.

| Check | Result |
|---|---|
| Baseline bootstrap, prescribed 77-module order | Exit 0; zero errors; exactly the 43 base admission warnings. |
| Final sweep, the same 77-module order | Exit 0; zero errors; exactly 42 admission warnings, the base set minus the target. |
| Owned module | Exit 0; zero errors and zero warnings. |
| Maintainer's pre-ship probe, copied verbatim | Exit 0; zero errors and zero admission warnings. |
| Target axiom print | Only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. |
| Required style lint | `style_lint: 0 FAIL, 15 WARN over 58 files` |
| Freeze, ownership, and warning-name checks | PASS; see `logs/verification.log`. |

The bootstrap and final sweep use separate fresh TCSlib output trees. The final sweep's first 66 unchanged modules and its final 11 modules were invoked in two consecutive segments of the prescribed order; every module is checked exactly once in that final log. The target, probe, and axiom prints use the final fresh output tree.

Environment: Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; Mathlib pinned to `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Initial `lake exe cache get` attempts encountered runtime discovery and shared-disk constraints. Existing dependency caches were reused after checking their manifest pins and clean tracked sources (`evidence/dependency-pins.txt`); no TCSlib proof artifacts were reused. The environment exposes host procfs inside a PID namespace, so the included compatibility shim maps only `/proc/<this-process-id>/exe` to `/proc/self/exe`. It changes neither the Lean binary nor any proof or kernel behavior. Checks set `LD_PRELOAD` to that shim. The repository check script is untouched.

Final owned-file size: **270 lines; 7 public and 1 private source declarations** (compiler-generated fields/projections are not counted as separate source declarations).

### Exact base admission inventory

```text
TCSlib/Complexity/ClassOracle/Classes: 1: POracle_eq_P_of_mem_P
TCSlib/Complexity/TuringMachine/Build/CfgRecord: 1: exists_recordStepTM
TCSlib/Complexity/Diagonalization/EXPCOM: 6: exists_uniformMachineCode, EXP_subset_POracle_EXPCOM, NPOracle_EXPCOM_subset_EXP, POracle_EXPCOM_eq_EXP, NPOracle_EXPCOM_eq_EXP, POracle_EXPCOM_eq_NPOracle_EXPCOM
TCSlib/Complexity/Diagonalization/Relativization: 1: baker_gill_solovay
TCSlib/Complexity/TuringMachine/NDCodes: 1: exists_effectiveNDMachineCode
TCSlib/Complexity/Diagonalization/NTimeHierarchy: 6: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
TCSlib/Complexity/TuringMachine/Build/InputLength: 1: exists_inputLengthTM
TCSlib/Complexity/TuringMachine/Build/RecordTable: 20: joinFields_length, fieldOffset_length, joinFields_cfgRecord_length, cfgRecord_field_ne_nil, cfgRecord_init, recordValid_iff_exists_cfg, joinFields_recordTemplate_length, binDigits_posWidth_succ, TableWF.field_ne_nil, tableOffset_eq, tableOffset_length, TableAt.recordAt_take, tableRewindTM_run_ofCfg, exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
TCSlib/Complexity/TuringMachine/Build/CertShell: 1: FinTM.exists_certificateShell
TCSlib/Complexity/TuringMachine/Build/OracleSim: 2: FinOracleTM.exists_plain_simulation, FinOracleNDTM.exists_choiceTM
TCSlib/Complexity/TuringMachine/CodeSimulator: 2: exists_polyCanonizer, exists_uniformSimulator
TCSlib/Complexity/TuringMachine/Codes2Tape: 1: exists_uniformMachineCode2
TOTAL 43
```

The final named inventory is included as `logs/final-sorries-actual.txt` and was matched to the final diagnostic locations. The sole deletion is `Turing.exists_effectiveNDMachineCode`.

### Final sweep tail

```text
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:281:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:293:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:307:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:342:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:383:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:456:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:507:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:559:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:610:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:668:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:729:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/CertShell
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:71:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/OracleSim
TCSlib/Complexity/TuringMachine/Build/OracleSim.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/OracleSim.lean:398:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/CodeSimulator
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:205:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:239:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:547:8: warning: declaration uses 'sorry'
FINAL_SWEEP_EXIT=0
```

### Axiom print

```text
'Turing.exists_effectiveNDMachineCode' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Re-run pre-ship probe

```text
CodeFormat.exists_canonizer : ∀ (F : CodeFormat),
  Primrec₂ F.skipTable → ∃ M T, M.ComputesFunInTime (fun xs => F.serialize (F.decode xs)) T
CodeFormat.decode_serialize_pad : ∀ (F : CodeFormat) (M : F.Code) (m : ℕ),
  F.decode (F.serialize M ++ List.replicate m true) = M
CodeFormat.canonical_eq : ∀ (F : CodeFormat) (xs : List Bool), F.canonical xs = F.serialize (F.decode xs)
@codePrimRepeat : ∀ {A : Type} [inst : Primcodable A] (r : A → List Bool → Option (List Bool)),
  Primrec₂ r → ∀ (count : A → ℕ), Primrec count → Primrec₂ fun a xs => codeSkipRepeat (r a) (count a) xs
codePrimSkipTable2 : Primrec₂ codeSkipTable2
@codeReadTable2_append : ∀ {n : ℕ} (t : CodeTable2 n) (xs : List Bool),
  codeReadTable2 n (codeTable2Bits t ++ xs) = some (t, xs)
codeSkipTable2 : ℕ → List Bool → Option (List Bool)
@codeTable2Bits_length : ∀ {n : ℕ} (t : CodeTable2 n), 351 * (n + 1) ≤ (codeTable2Bits t).length
@actionBits₂_eq_actionBitsK : ∀ {n : ℕ} (a : Action 2 Bool (Fin (n + 1))), actionBits₂ a = actionBitsK a
'Turing.probe_ndSerialize' depends on axioms: [propext, Quot.sound]
```

## Duplication ledger

**new copies: none.** There are no new cross-file or in-file pairs meeting the required screen's threshold. The two added screened bodies are the private instance and the now-filled public theorem; all 82 baseline pairs and the 13,040-character total remain unchanged.

The brief's pre-disclosed instance-boilerplate comparisons were measured even though neither reaches the screen threshold:

| Pair | Matched characters / other body | Fraction of other body | Matched characters / `ndFormat` body |
|---|---:|---:|---:|
| `ndFormat` versus `CodeFormat.oneTapeFormat` | 207 / 1959 | 10.57% | 207 / 1597 = 12.96% |
| `ndFormat` versus `Codes2Tape`'s private `twoTapeFormat` | 288 / 794 | 36.27% | 288 / 1597 = 18.03% |

These are the sanctioned format-instance boilerplate similarities; the shared arguments are cited from public infrastructure. No additional copied helper or promotion candidate is present. The figures use the supplied screen's whitespace/comment-stripped bodies and greedy tiling, not line counts.

### Before screen (verbatim)

```text
declarations screened: 177; copy pairs (target reproduces >= half of source): 82; reproduced text: 13,040 chars
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   CodeFormat.lean::actionBits₂  reproduces  Encoding.lean::actionBits: 119/119 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   MathlibBridge.lean::codePrimBitsNat  reproduces  MathlibBridge.lean::bridgePrimNumber: 128/129 = 99%
   MathlibBridge.lean::bridgePrimNumber  reproduces  MathlibBridge.lean::codePrimBitsNat: 128/129 = 99%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 290/310 = 94%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeFormat.lean::codeTable2Bits: 208/234 = 89%
   MathlibBridge.lean::bridgeCfg_push  reproduces  MathlibBridge.lean::bridgeCfg_pop: 674/761 = 89%
   NDCodes.lean::CodeNDTM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   NDCodes.lean::NDMachineCode  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   Codes2Tape.lean::MachineCode2  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeSimulator.lean::tableBitsK: 120/141 = 85%
   CodeParser.lean::codeSkipAction  reproduces  CodeFormat.lean::codeSkipActionK: 106/125 = 85%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   NDCodes.lean::NDMachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Encoding.lean::MachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Codes2Tape.lean::Code2TM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 290/348 = 83%
   Encoding.lean::MachineCode  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   Codes2Tape.lean::MachineCode2  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   Codes2Tape.lean::Code2TM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   CodeFormat.lean::actionBitsK  reproduces  Encoding.lean::actionBits: 93/119 = 78%
   MathlibBridge.lean::bridgeCfg_pop  reproduces  MathlibBridge.lean::bridgeCfg_push: 674/871 = 77%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeFormat.lean::codeEraseWork: 167/216 = 77%
   MathlibBridge.lean::bridgeCfg_push_input  reproduces  MathlibBridge.lean::bridgeCfg_pop_emit: 195/259 = 75%
   CodeFormat.lean::parseFull  reproduces  CodeFormat.lean::scan: 151/202 = 75%
   Encoding.lean::CodeTM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 104/141 = 74%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadWrite_sound: 143/195 = 73%
   MathlibBridge.lean::CodeFormat.primrec_scan  reproduces  MathlibBridge.lean::codePrimSkipFin: 188/257 = 73%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadSign_sound: 159/227 = 70%
   CodeParser.lean::codeReadSign_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 159/233 = 68%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimUnary: 367/542 = 68%
   CodeFormat.lean::codeSkipActionK  reproduces  CodeParser.lean::codeSkipAction: 106/157 = 68%
   Encoding.lean::CodeTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 209/310 = 67%
   CodeFormat.lean::codeTable2Bits  reproduces  CodeSimulator.lean::tableBitsK: 95/141 = 67%
   Encoding.lean::actionBits  reproduces  CodeFormat.lean::actionBits₂: 119/177 = 67%
   MathlibBridge.lean::codePrimSkipTable1  reproduces  MathlibBridge.lean::codePrimSkipTable2: 135/201 = 67%
   CodeFormat.lean::codeTable2Bits  reproduces  Codes2Tape.lean::Code2TM.serialize: 206/310 = 66%
   CodeFormat.lean::scan  reproduces  CodeFormat.lean::parseFull: 151/234 = 65%
   CodeFormat.lean::oneTapeFormat  reproduces  Codes2Tape.lean::Code2TM.serialize: 192/310 = 62%
   Encoding.lean::actionBits  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   CodeFormat.lean::actionBits₂  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   CodeParser.lean::codeReadWrite_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 143/233 = 61%
   Encoding.lean::CodeTM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 209/348 = 60%
   MathlibBridge.lean::bridgeCfg_pop_emit  reproduces  MathlibBridge.lean::bridgeCfg_push_input: 195/327 = 60%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipState: 215/361 = 60%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeParser.lean::codeReadSymbols_sound: 142/239 = 59%
   CodeFormat.lean::codeTable2Bits  reproduces  NDCodes.lean::CodeNDTM.serialize: 206/348 = 59%
   CodeParser.lean::codeReadWrite  reproduces  CodeParser.lean::codeReadOutput: 65/110 = 59%
   Codes2Tape.lean::zfB3_uniform_of_simulator  reproduces  Codes2Tape.lean::exists_effectiveMachineCode2: 85/144 = 59%
   CodeFormat.lean::oneTapeFormat  reproduces  Encoding.lean::CodeTM.serialize: 147/254 = 58%
   Encoding.lean::CodeTM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 134/234 = 57%
   CodeParser.lean::codeReadState_sound  reproduces  CodeParser.lean::codeReadUnary_sound: 223/390 = 57%
   MathlibBridge.lean::bridge_back  reproduces  MathlibBridge.lean::bridge_scan: 422/747 = 56%
   NDCodes.lean::CodeNDTM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   CodeFormat.lean::oneTapeFormat  reproduces  NDCodes.lean::CodeNDTM.serialize: 192/348 = 55%
   Codes2Tape.lean::zfB3Answer_malformed  reproduces  Codes2Tape.lean::zfB3Answer_zero: 68/124 = 55%
   MathlibBridge.lean::codePrimSkipTable2  reproduces  MathlibBridge.lean::codePrimSkipTable1: 135/249 = 54%
   CodeFormat.lean::codeTable2Bits  reproduces  Encoding.lean::CodeTM.serialize: 134/254 = 53%
   CodeFormat.lean::actionBitsK  reproduces  CodeFormat.lean::actionBits₂: 93/177 = 53%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 127/242 = 52%
   CodeParser.lean::codeEraseVec  reproduces  CodeFormat.lean::codeEraseWork: 113/216 = 52%
   CodeFormat.lean::codeReadActionK_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 126/242 = 52%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   CodeParser.lean::codeEraseVec  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseWork  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeParser.lean::codeReadUnary_sound  reproduces  CodeParser.lean::codeReadState_sound: 223/439 = 51%
   Codes2Tape.lean::zfB3_decode_length  reproduces  Codes2Tape.lean::zfB3_decode_states: 79/158 = 50%
```

### After screen (verbatim)

```text
declarations screened: 179; copy pairs (target reproduces >= half of source): 82; reproduced text: 13,040 chars
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   CodeFormat.lean::actionBits₂  reproduces  Encoding.lean::actionBits: 119/119 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   MathlibBridge.lean::codePrimBitsNat  reproduces  MathlibBridge.lean::bridgePrimNumber: 128/129 = 99%
   MathlibBridge.lean::bridgePrimNumber  reproduces  MathlibBridge.lean::codePrimBitsNat: 128/129 = 99%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 290/310 = 94%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeFormat.lean::codeTable2Bits: 208/234 = 89%
   MathlibBridge.lean::bridgeCfg_push  reproduces  MathlibBridge.lean::bridgeCfg_pop: 674/761 = 89%
   NDCodes.lean::CodeNDTM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   NDCodes.lean::NDMachineCode  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   Codes2Tape.lean::MachineCode2  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeSimulator.lean::tableBitsK: 120/141 = 85%
   CodeParser.lean::codeSkipAction  reproduces  CodeFormat.lean::codeSkipActionK: 106/125 = 85%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   NDCodes.lean::NDMachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Encoding.lean::MachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Codes2Tape.lean::Code2TM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 290/348 = 83%
   Encoding.lean::MachineCode  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   Codes2Tape.lean::MachineCode2  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   Codes2Tape.lean::Code2TM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   CodeFormat.lean::actionBitsK  reproduces  Encoding.lean::actionBits: 93/119 = 78%
   MathlibBridge.lean::bridgeCfg_pop  reproduces  MathlibBridge.lean::bridgeCfg_push: 674/871 = 77%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeFormat.lean::codeEraseWork: 167/216 = 77%
   MathlibBridge.lean::bridgeCfg_push_input  reproduces  MathlibBridge.lean::bridgeCfg_pop_emit: 195/259 = 75%
   CodeFormat.lean::parseFull  reproduces  CodeFormat.lean::scan: 151/202 = 75%
   Encoding.lean::CodeTM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 104/141 = 74%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadWrite_sound: 143/195 = 73%
   MathlibBridge.lean::CodeFormat.primrec_scan  reproduces  MathlibBridge.lean::codePrimSkipFin: 188/257 = 73%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadSign_sound: 159/227 = 70%
   CodeParser.lean::codeReadSign_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 159/233 = 68%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimUnary: 367/542 = 68%
   CodeFormat.lean::codeSkipActionK  reproduces  CodeParser.lean::codeSkipAction: 106/157 = 68%
   Encoding.lean::CodeTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 209/310 = 67%
   CodeFormat.lean::codeTable2Bits  reproduces  CodeSimulator.lean::tableBitsK: 95/141 = 67%
   Encoding.lean::actionBits  reproduces  CodeFormat.lean::actionBits₂: 119/177 = 67%
   MathlibBridge.lean::codePrimSkipTable1  reproduces  MathlibBridge.lean::codePrimSkipTable2: 135/201 = 67%
   CodeFormat.lean::codeTable2Bits  reproduces  Codes2Tape.lean::Code2TM.serialize: 206/310 = 66%
   CodeFormat.lean::scan  reproduces  CodeFormat.lean::parseFull: 151/234 = 65%
   CodeFormat.lean::oneTapeFormat  reproduces  Codes2Tape.lean::Code2TM.serialize: 192/310 = 62%
   Encoding.lean::actionBits  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   CodeFormat.lean::actionBits₂  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   CodeParser.lean::codeReadWrite_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 143/233 = 61%
   Encoding.lean::CodeTM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 209/348 = 60%
   MathlibBridge.lean::bridgeCfg_pop_emit  reproduces  MathlibBridge.lean::bridgeCfg_push_input: 195/327 = 60%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipState: 215/361 = 60%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeParser.lean::codeReadSymbols_sound: 142/239 = 59%
   CodeFormat.lean::codeTable2Bits  reproduces  NDCodes.lean::CodeNDTM.serialize: 206/348 = 59%
   CodeParser.lean::codeReadWrite  reproduces  CodeParser.lean::codeReadOutput: 65/110 = 59%
   Codes2Tape.lean::zfB3_uniform_of_simulator  reproduces  Codes2Tape.lean::exists_effectiveMachineCode2: 85/144 = 59%
   CodeFormat.lean::oneTapeFormat  reproduces  Encoding.lean::CodeTM.serialize: 147/254 = 58%
   Encoding.lean::CodeTM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 134/234 = 57%
   CodeParser.lean::codeReadState_sound  reproduces  CodeParser.lean::codeReadUnary_sound: 223/390 = 57%
   MathlibBridge.lean::bridge_back  reproduces  MathlibBridge.lean::bridge_scan: 422/747 = 56%
   NDCodes.lean::CodeNDTM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   CodeFormat.lean::oneTapeFormat  reproduces  NDCodes.lean::CodeNDTM.serialize: 192/348 = 55%
   Codes2Tape.lean::zfB3Answer_malformed  reproduces  Codes2Tape.lean::zfB3Answer_zero: 68/124 = 55%
   MathlibBridge.lean::codePrimSkipTable2  reproduces  MathlibBridge.lean::codePrimSkipTable1: 135/249 = 54%
   CodeFormat.lean::codeTable2Bits  reproduces  Encoding.lean::CodeTM.serialize: 134/254 = 53%
   CodeFormat.lean::actionBitsK  reproduces  CodeFormat.lean::actionBits₂: 93/177 = 53%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 127/242 = 52%
   CodeParser.lean::codeEraseVec  reproduces  CodeFormat.lean::codeEraseWork: 113/216 = 52%
   CodeFormat.lean::codeReadActionK_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 126/242 = 52%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   CodeParser.lean::codeEraseVec  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseWork  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeParser.lean::codeReadUnary_sound  reproduces  CodeParser.lean::codeReadState_sound: 223/439 = 51%
   Codes2Tape.lean::zfB3_decode_length  reproduces  Codes2Tape.lean::zfB3_decode_states: 79/158 = 50%
```

## Archive and integration

The archive contains this report, the full modified source at its repository-relative path, the `git format-patch` series against the base, an incremental git bundle, the sweep and axiom logs, supporting verification evidence, and `SHA256SUMS` (all archive payload files except the checksum file itself).

Apply the patch to the recorded base (or integrate with `git am -3`). The bundle requires the recorded base as its prerequisite. Verify all archive checksums before integration.
