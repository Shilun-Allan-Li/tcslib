# ZF-B delivery — effective scheme complete; uniform simulator pending

**1/2 targets complete.** This is the brief's permitted target-1-complete delivery.
`Turing.exists_effectiveMachineCode2` is proved without `sorryAx`.
`Turing.exists_uniformMachineCode2` remains exactly the received `by sorry`; no partial simulator was introduced.

## Revision and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Checked-out campaign branch: `complexity/arora-barak-ch3-4`, never `main`.
- Recorded working base: `3e5dd8c7504725750720629a7be08855b89d4e87`.
- Brief issue base: `8f13d74ecba8e73a3642d605f462774092d7ef8a`.
- The owned source is byte-identical at those two bases; the later branch commit adds the briefs and other campaign documentation.
- Working branch: `fill/zone-f1-B`.
- Delivery commit: `c020d6d9f438d1dc4e63234a8253b0579fa4a9c2`.
- Only tracked path changed: `TCSlib/Complexity/TuringMachine/Codes2Tape.lean`.
- No rebase, push, PR, `lake build`, public declaration addition, or audited statement change.
- Read the complete attached/repository brief and all four named audit documents. The attached brief and repository brief match byte-for-byte.

## Completed proof and inherited route

1. The encoder is exactly `Code2TM.serialize`. The decoder reads the canonical binary state count, validates the lower-length guard before table recursion, range-checks the unary initial state and each successor, and reads the fixed state/input/work-0/work-1 enumeration.
2. Each record reads movement, work-0 write/move, work-1 write/move, output, and successor in the inherited `actionBits₂` format. The record lower bound is 13; three nested three-symbol rows give 27 records and at least 351 bits per state. `zfBTable_length` is a proved necessary length guard, not a claim that the whole header-inclusive encoding halves against ND.
3. The suffix must be all true. Any failure selects the fixed one-state immediately halting silent machine. Exact field/vector inverses prove recovery of the whole transition function and initial state under arbitrary true padding, including both physical work-tape coordinates.
4. A suffix-only scanner is proved extensionally equal to the typed parser's suffix. Parser soundness reconstructs the consumed serialization, so taking that prefix (or the fallback serialization) computes exactly `serialize ∘ decode`.
5. The scanner and prefix operation are proved primitive recursive. The **public** `Turing.codePrim_machine` theorem supplies a finite binary canonizer and its arbitrary length-only time bound. Its existing compiler/finite-maximum proof is cited; no machine compiler was copied or reimplemented, and no polynomial canonizer time is claimed.
6. The private regression `zfBFallback_serialize_length` proves the complete fallback serialization has length **354**. It uses ordinary kernel-checked simplification; no native axiom or untrusted evaluator is used. The exact successor-sensitive global serializer identity was optional and is not added.

Public definitions/laws cited directly include `actionBits₂`, `workPair`, `codeReadUnary`, `codeBitsNat`, `codeSkipPair`, `codeSkipFin`, `codeSkipState`, `codeSkipRepeat`, `pairDecode_pairEncode`, `eq_pairEncode_of_pairDecode`, `length_pairEncode`, and `codePrim_machine`. The paired-header soundness law is cited, not re-derived. No proof refers to `exists_effectiveNDMachineCode`.

## Freeze and documentation

`freeze.log` records a byte reconstruction of the received file: remove the one new private implementation block, the two new imports, and the two explicitly marked docstring appendices; restore only target 1's original proof. The result is exactly the recorded-base file. Thus all nine old public declarations retain their signatures and order, all old definition bodies are unchanged, and target 2's entire statement/proof is unchanged. There are no deletions of preexisting declarations.

Added imports: `TCSlib.Complexity.TuringMachine.MathlibBridge` and `Mathlib.Tactic.FinCases`.
Flagged documentation appendices: the module's `ZF-B status appendix` and target 1's `ZF-B implementation appendix`. The received sketches are preserved. All **70** added declarations are private. The source has **1103 lines**; exclusive ownership prevents splitting this batch across shared files. The requested shared-file promotion below is the proposed remedy for both file size and duplicated helpers.

## Verification

The proof was checked with Lean **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, and mathlib **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**. All TCSlib oleans were regenerated into an initially empty scratch tree by the unchanged `scripts/lean_check_tree.sh`; the pinned mathlib cache was unpacked separately.

- Fresh bootstrap status: complete, 73 dependency/facade module checks exited 0. The bootstrap is the 65-module chapter-1 list plus its current dependency closure, all Build files, and the new code module's dependencies; `module-order.txt` records the resolved order.
- Final owned-module check: exit 0, **zero errors**, exactly **one** `declaration uses 'sorry'` warning, at the unchanged uniform target. All target-1 helpers and target 1 are closed. This is explicitly a partial delivery and **does not** claim the full batch's zero-sorry gate.
- Final facade: exit 0, zero errors (see `final-facade.log`). The facade's received imports do not include `Codes2Tape`, `Build.Zone`, or `Build.VirtualInput`; these were checked directly. No facade was edited outside ownership.
- `style_lint: 0 FAIL, 12 WARN over 42 files`. All warnings are retained in `lint.log`, including this file's disclosed size warning.
- `git diff --check`: pass. Bundle verification: pass; the bundle is incremental and requires the recorded base commit.

The two required axiom prints on the fresh owned-module olean are:

```text
'Turing.exists_effectiveMachineCode2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_uniformMachineCode2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The completed target meets the required axiom ceiling exactly. The uniform target's `sorryAx` is the unchanged and explicitly deferred admission.

Final owned-module sweep tail:

```text
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:1100:8: warning: declaration uses 'sorry'
EXIT Codes2Tape 0
```

Remaining admissions observed during the dependency/Build sweep and final owned check (32 warning emissions across 28 declarations; each of the four Zone capacity definitions emits two warnings):

| File | Declaration | Source line | Warning emissions |
|---|---|---:|---:|
| `TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean` | `alphabet_reduction_spaceUsed` | 620 | 1 |
| `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean` | `one_work_tape_spaceUsed` | 1014 | 1 |
| `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean` | `one_work_tape_binary_spaceUsed` | 1036 | 1 |
| `TCSlib/Complexity/TuringMachine/NDCodes.lean` | `exists_effectiveNDMachineCode` | 187 | 1 |
| `TCSlib/Complexity/TuringMachine/CounterProgRun.lean` | `sim_run_of_regs_le` | 343 | 1 |
| `TCSlib/Complexity/Formulas/QBF.lean` | `truth_exPrefix_iff_satisfiable` | 119 | 1 |
| `TCSlib/Complexity/Formulas/QBFEncoding.lean` | `decode_encode` | 88 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneIndex_eq_iff` | 159 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneTape_empty` | 226 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneTape_blank_outside` | 240 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneSide_shiftInW` | 293 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneSide_shiftOutW` | 302 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneShiftInW_full_donor` | 313 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneShiftIn` | 325 | 2 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneShiftOut` | 339 | 2 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneTape_homeWrite` | 358 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneMoveRight` | 370 | 2 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneMoveLeft` | 380 | 2 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneSide_moveRight` | 412 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneSide_cascadeRight` | 458 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneCascadeRight_lengths` | 489 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneCascadeRight_zero` | 511 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneCascadeRight_blocked` | 527 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `zoneCascade_cost_le` | 543 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `exists_zoneShiftInTM` | 571 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `exists_zoneShiftOutTM` | 607 | 1 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `MultiTapeTM.spaceUsedByTape_le_card_Icc` | 640 | 1 |
| `TCSlib/Complexity/TuringMachine/Codes2Tape.lean` | `exists_uniformMachineCode2` | 1100 | 1 |


## Duplication ledger — maintainer review required

**Ledger line:** `Codes2Tape.lean`: received explicit declarations 9, received private helpers 0; new private helpers **70**; copies/adaptations of existing material **69**; genuinely new helper **1** (the 354-bit regression); final explicit declarations **79**. Expanded copied/adapted fraction **69/79 = 87.34%**. Strict textual copies after helper-name and visibility normalization **49/79 = 62.03%**; the remaining **20** are two-tape/grammar/proof retargetings. Counted code-line footprint: **721/787 = 91.61%** for expanded copies/adaptations, **454/787 = 57.69%** for strict copies. These are declaration spans with comments and blank lines removed; generated structure projections/constructors are not counted as explicit declarations.

This is substantial disclosed debt, **not zero duplication**. The reused type-independent proofs are private in their current homes and cannot be cited by their public names from this owned file. Publicly usable definitions and the compiler are cited directly. The brief permits disclosed local copies under exclusive ownership; it does not supply human debt acceptance. **No human acknowledgment is claimed.** Since the file crosses the one-fifth threshold, `workflow.md` requires the maintainer to open the corresponding human-review/backlog item and obtain explicit acceptance naming owner and repayment window before the fill gate can close. This packet does not edit that shared ledger or backlog.

Strict classification compares the complete comment-stripped declaration after renaming the local `zfB…` identifiers back to their listed origins and normalizing `private` visibility and whitespace. It preserves types, constants, binders, and proof text. Expanded classification includes all adaptations, even where the type or grammar changes. Every local copy/adaptation is listed individually below, together with every new private's role. Origins refer to the recorded base.

| New private declaration | Role | Origin at recorded base | Classification | Code lines |
|---|---|---|---|---:|
| `zfBReadUnary_append` | Unary reader leaves an arbitrary suffix untouched. | `CodeParser.lean` · `codeReadUnary_append` | Copy after name/visibility normalization | 7 |
| `zfBReadFin` | Range-check a unary state index. | `CodeParser.lean` · `codeReadFin` | Copy after name/visibility normalization | 3 |
| `zfBReadSign` | Decode the movement dictionary. | `CodeParser.lean` · `codeReadSign` | Copy after name/visibility normalization | 5 |
| `zfBReadOutput` | Decode the optional output dictionary. | `CodeParser.lean` · `codeReadOutput` | Copy after name/visibility normalization | 5 |
| `zfBReadWrite` | Decode the optional-write dictionary. | `CodeParser.lean` · `codeReadWrite` | Copy after name/visibility normalization | 6 |
| `zfBReadState` | Decode halt or a bounded live successor. | `CodeParser.lean` · `codeReadState` | Copy after name/visibility normalization | 4 |
| `zfBReadAction` | Read the seven fields and reconstruct both work-tape actions. | `CodeParser.lean` · `codeReadAction` | Retargeted adaptation | 10 |
| `zfBReadSymbols` | Read one entry for each of the three read symbols. | `CodeParser.lean` · `codeReadSymbols` | Copy after name/visibility normalization | 6 |
| `zfBReadVec` | Read the state-indexed finite table. | `CodeParser.lean` · `codeReadVec` | Copy after name/visibility normalization | 7 |
| `zfBFallback` | The one-state, immediately halting, silent two-tape machine. | `CodeParser.lean` · `codeFallback` | Retargeted adaptation | 2 |
| `zfBFallback_serialize_length` | Kernel-checked 354-bit fallback serialization regression. | New | New regression | 6 |
| `zfBParse` | Canonical header, 351-per-state guard, initial state, table, and padding validation. | `CodeParser.lean` · `codeParse` | Retargeted adaptation | 11 |
| `zfBDecode` | Totalize parsing with the halting fallback. | `CodeParser.lean` · `codeDecode` | Retargeted adaptation | 1 |
| `zfBReadFin_append` | Exact prefix inverse for ReadFin. | `CodeParser.lean` · `codeReadFin_append` | Copy after name/visibility normalization | 3 |
| `zfBReadSign_append` | Exact prefix inverse for ReadSign. | `CodeParser.lean` · `codeReadSign_append` | Copy after name/visibility normalization | 3 |
| `zfBReadOutput_append` | Exact prefix inverse for ReadOutput. | `CodeParser.lean` · `codeReadOutput_append` | Copy after name/visibility normalization | 5 |
| `zfBReadWrite_append` | Exact prefix inverse for ReadWrite. | `CodeParser.lean` · `codeReadWrite_append` | Copy after name/visibility normalization | 6 |
| `zfBReadState_append` | Exact prefix inverse for ReadState. | `CodeParser.lean` · `codeReadState_append` | Copy after name/visibility normalization | 5 |
| `zfBReadAction_append` | Exact prefix inverse for ReadAction. | `CodeParser.lean` · `codeReadAction_append` | Retargeted adaptation | 10 |
| `zfBReadSymbols_append` | Exact prefix inverse for ReadSymbols. | `CodeParser.lean` · `codeReadSymbols_append` | Copy after name/visibility normalization | 14 |
| `zfBReadVec_append` | Exact prefix inverse for ReadVec. | `CodeParser.lean` · `codeReadVec_append` | Copy after name/visibility normalization | 21 |
| `zfBBitsNat_bits` | Invert the canonical binary state-count representation. | `CodeParser.lean` · `codeBitsNat_bits` | Copy after name/visibility normalization | 6 |
| `zfBAction_length` | Every two-tape action record has at least 13 bits. | `CodeParser.lean` · `codeAction_length` | Retargeted adaptation | 16 |
| `zfBFlatMap_length` | Sum a uniform lower bound over a concatenation. | `CodeParser.lean` · `codeFlatMap_length` | Copy after name/visibility normalization | 11 |
| `zfBTable_length` | Derive the 351-per-state lower bound from 27 records. | `CodeParser.lean` · `codeTable_length` | Retargeted adaptation | 29 |
| `zfBReadTable_append` | Recover all 27 transitions per state in the fixed enumeration. | `CodeParser.lean` · `codeReadTable_append` | Retargeted adaptation | 13 |
| `zfBParse_serialize_pad` | Exact parser recovery after arbitrary true padding. | `CodeParser.lean` · `codeParse_serialize_pad` | Retargeted adaptation | 27 |
| `zfBDecode_serialize_pad` | The total decoder satisfies the required padded round-trip. | `CodeParser.lean` · `codeDecode_serialize_pad` | Retargeted adaptation | 3 |
| `zfBReadUnary_sound` | Reconstruct the exact consumed prefix for ReadUnary. | `CodeParser.lean` · `codeReadUnary_sound` | Copy after name/visibility normalization | 20 |
| `zfBReadFin_sound` | Reconstruct the exact consumed prefix for ReadFin. | `CodeParser.lean` · `codeReadFin_sound` | Copy after name/visibility normalization | 9 |
| `zfBReadSign_sound` | Reconstruct the exact consumed prefix for ReadSign. | `CodeParser.lean` · `codeReadSign_sound` | Copy after name/visibility normalization | 8 |
| `zfBReadOutput_sound` | Reconstruct the exact consumed prefix for ReadOutput. | `CodeParser.lean` · `codeReadOutput_sound` | Copy after name/visibility normalization | 8 |
| `zfBReadWrite_sound` | Reconstruct the exact consumed prefix for ReadWrite. | `CodeParser.lean` · `codeReadWrite_sound` | Copy after name/visibility normalization | 8 |
| `zfBReadState_sound` | Reconstruct the exact consumed prefix for ReadState. | `CodeParser.lean` · `codeReadState_sound` | Copy after name/visibility normalization | 20 |
| `zfBReadAction_sound` | Reconstruct the exact consumed prefix for ReadAction. | `CodeParser.lean` · `codeReadAction_sound` | Retargeted adaptation | 14 |
| `zfBReadSymbols_sound` | Reconstruct the exact consumed prefix for ReadSymbols. | `CodeParser.lean` · `codeReadSymbols_sound` | Copy after name/visibility normalization | 13 |
| `zfBReadVec_sound` | Reconstruct the exact consumed prefix for ReadVec. | `CodeParser.lean` · `codeReadVec_sound` | Copy after name/visibility normalization | 20 |
| `zfBSkipAction` | Erase the seven-field reader, retaining only the suffix. | `CodeParser.lean` · `codeSkipAction` | Retargeted adaptation | 8 |
| `zfBEraseFin` | Identify Fin reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseFin` | Copy after name/visibility normalization | 6 |
| `zfBEraseSign` | Identify Sign reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseSign` | Copy after name/visibility normalization | 8 |
| `zfBEraseOutput` | Identify Output reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseOutput` | Copy after name/visibility normalization | 8 |
| `zfBEraseWrite` | Identify Write reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseWrite` | Copy after name/visibility normalization | 8 |
| `zfBEraseState` | Identify State reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseState` | Copy after name/visibility normalization | 9 |
| `zfBErase_bind` | Move suffix erasure through an option bind. | `CodeParser.lean` · `codeErase_bind` | Copy after name/visibility normalization | 4 |
| `zfBEraseAction` | Identify Action reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseAction` | Retargeted adaptation | 16 |
| `zfBEraseSymbols` | Identify Symbols reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseSymbols` | Copy after name/visibility normalization | 4 |
| `zfBEraseVec` | Identify Vec reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseVec` | Copy after name/visibility normalization | 11 |
| `zfBParseFull` | Parser retaining the decoded machine and unconsumed padding. | `CodeParser.lean` · `codeParseFull` | Retargeted adaptation | 11 |
| `zfBScan` | Erased full parser with the same guard and padding test. | `CodeParser.lean` · `codeScan` | Retargeted adaptation | 8 |
| `zfBParse_full` | The decoder parser is the first projection of full parsing. | `CodeParser.lean` · `codeParse_full` | Copy after name/visibility normalization | 11 |
| `zfBScan_full` | The scanner is the second projection of full parsing. | `CodeParser.lean` · `codeScan_full` | Retargeted adaptation | 18 |
| `zfBParseFull_sound` | Reconstruct the exact serialization prefix from successful full parsing. | `CodeParser.lean` · `codeParseFull_sound` | Retargeted adaptation | 29 |
| `zfBCanonical` | Return the consumed prefix or fallback serialization. | `CodeParser.lean` · `codeCanonical` | Copy after name/visibility normalization | 2 |
| `zfBCanonical_eq` | Identify that prefix function with serialization after total decoding. | `CodeParser.lean` · `codeCanonical_eq` | Copy after name/visibility normalization | 10 |
| `zfBPrimUnary` | Primitive recursiveness of the public unary reader. | `MathlibBridge.lean` · `codePrimUnary` | Copy after name/visibility normalization | 13 |
| `zfBPrimBit` | Primitive recursiveness of binary bit construction. | `MathlibBridge.lean` · `codePrimBit` | Copy after name/visibility normalization | 7 |
| `zfBPrimBitsNat` | Primitive recursiveness of the public binary-word interpretation. | `MathlibBridge.lean` · `codePrimBitsNat` | Copy after name/visibility normalization | 3 |
| `zfBPrimPair` | Primitive recursiveness of the public pair decoder. | `MathlibBridge.lean` · `codePrimPair` | Copy after name/visibility normalization | 33 |
| `zfBPrimBits` | Primitive recursiveness of natural-number bit lists. | `MathlibBridge.lean` · `codePrimBits` | Copy after name/visibility normalization | 30 |
| `zfBPrimSkipPair` | Primitive recursiveness of the public two-bit suffix reader. | `MathlibBridge.lean` · `codePrimSkipPair` | Copy after name/visibility normalization | 8 |
| `zfBPrimSkipFin` | Primitive recursiveness of bounded unary skipping. | `MathlibBridge.lean` · `codePrimSkipFin` | Copy after name/visibility normalization | 6 |
| `zfBPrimSkipState` | Primitive recursiveness of successor skipping. | `MathlibBridge.lean` · `codePrimSkipState` | Copy after name/visibility normalization | 7 |
| `zfBPrimSkipAction` | Primitive recursiveness of the seven-field suffix reader. | `MathlibBridge.lean` · `codePrimSkipAction` | Retargeted adaptation | 17 |
| `zfBSkipRepeat_iter` | Relate the public repeat operation to function iteration. | `MathlibBridge.lean` · `codeSkipRepeat_iter` | Copy after name/visibility normalization | 14 |
| `zfBPrimRepeat` | Primitive recursiveness of counted suffix-reader iteration. | `MathlibBridge.lean` · `codePrimRepeat` | Copy after name/visibility normalization | 8 |
| `zfBPrimAll` | Primitive recursiveness of the all-true suffix test. | `MathlibBridge.lean` · `codePrimAll` | Copy after name/visibility normalization | 8 |
| `zfBPrimScan` | Assemble primitive recursiveness of the complete erased parser. | `MathlibBridge.lean` · `codePrimScan` | Retargeted adaptation | 21 |
| `zfBPrimDrop` | Primitive recursiveness of dropping a specified number of leading bits. | `MathlibBridge.lean` · `codePrimDrop` | Copy after name/visibility normalization | 10 |
| `zfBPrimPrefix` | Primitive recursiveness of taking the complement-length prefix. | `MathlibBridge.lean` · `codePrimPrefix` | Copy after name/visibility normalization | 3 |
| `zfBPrimCanonical` | Assemble primitive recursiveness of the canonizer function. | `MathlibBridge.lean` · `codePrimCanonical` | Retargeted adaptation | 3 |


## Requested shared lemmas

1. A public field-reader/vector-parser interface in `CodeParser.lean`, exposing its existing prefix inverses, soundness, and suffix-erasure laws, plus the binary-header inverse and common concatenation-length bound. This would remove the type-independent local family. A parameterized record-reader interface should permit the two-tape layer to supply only its seven-field row and three-symbol nesting.
2. Public primitive-recursiveness lemmas in `MathlibBridge.lean` for the public unary, pair, binary, suffix-skipping, repeat, all-true, drop, and prefix operations. The existing `codePrim_machine` is already sufficient and needs no duplication.
3. Keep the actual two-tape record/table/totalization and their type-specific laws local or promote them deliberately at the next shared-file window. Do not silently publish helpers during integration; retain the audited statement freeze.

These are requests for the maintainer's next shared-file window, not changes made in this batch.

## Continuation frontier for target 2

There are no unfinished private proofs and no speculative simulator skeleton. Target 1 is complete. The next agent can work exclusively in this file, reuse the private definitions directly, and choose the **same concrete effective scheme**: build its canonizer through `codePrim_machine zfBCanonical zfBPrimCanonical`, then extend it with a separately constructed simulator. Merely choosing the witness of `exists_effectiveMachineCode2` loses the concrete decoder equation, so the uniform proof should assemble the concrete record in its body or in a new private helper.

The missing work is the full finite-machine implementation and joint polynomial ledger:

1. Parse `pairEncode (pairEncode (Nat.bits t) α) x`, keeping the deadline in binary. Implement the same canonical count, successor range checks, 351-per-state guard, and all-true suffix rule as `zfBDecode`. Compare the guard **in binary before any per-state iteration**, including malformed enormous counts; failed decoding means the fixed fallback.
2. Host the coded machine's two work tapes on two simulator tapes, with administrative tapes separate; cite the proved virtual-input and catalog machinery for input access, scans, bounded loops, and cleanup. There is no tape reduction inside the simulation.
3. Simulate at most the numeric deadline, inspecting the result after the last permitted transition. Maintain the append-only output classification (empty / exactly true / permanently other). Prove that deadline zero rejects because the initial configuration is live.
4. Prove both exact bounded-acceptance branches against `(zfBDecode α).toFinTM.ComputesInTime x [true] t`; derive the same coefficient/degree bound `simDegree * (α.length + x.length + t + 1)^simDegree` for both. The arbitrary-time canonizer theorem cannot supply this polynomial, so it must not be used to hide decoding costs.
5. Fill only the existing `exists_uniformMachineCode2` statement; perform the final zero-sorry owned-module check, both axiom prints, facade check, and subtree lint. Carry or repay this packet's copied-material ledger at integration.

No mathematical counterexample or unprovable-as-stated target was found. The second target is deferred under the brief's continuation-budget rule, not restated or weakened.

## Packet and application

The flattened archive contains this report, the full owned source, the one-commit format-patch series, the incremental bundle, sweep/axiom/style/freeze/bundle logs, the module order, reproducibility notes, and checksums. `verification-environment.md` records the namespace-safe runtime-path wrapper used in this environment and the separate dependency-cache setup. Apply the patch onto the recorded base (or use normal maintainer conflict review on a later branch); do not infer a completed uniform simulator or a closed debt gate from this delivery.
