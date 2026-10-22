# The buffer-word identities (PR #140, an API gate): resolutions (round 1; gate CLOSED)

**Gate:** the API gate of PR #140 (`lean/buffer-words` at `7c963897`): the new module
`TuringMachine/BufferWords` (six `FinTM.bufferTape` identities on composite words) and the
`TuringMachine` facade's import and contents line. Pack `pack.md`; bundle SHA-256
`be242a1cd835ca0172485014ccc58cc0c3520777f580fc152b269df8baffbc38` (27 sections; folder
`57-buffer-words-gate/`). Replay passed (user, 2026-10-21): 2 of 2, 0 failed, static-equal (0).

**Round 1** (`findings.md`, verbatim; received 2026-10-21): **PASS, 0 blockers, 0 majors, 1 minor,
13 notes. The gate is closed.** The minor is records-only (BW-1's census in the duplication ledger
and the backlog): no commit to #140 and no re-replay. The review re-ran the module, the seal, the
controls, the consumer examples, the lint and the screen at the merged head `7c963897` against
`oleans-lbw2` (`evidence/round1-review/`).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | BW-1's per-file accounting is incomplete: its census counts "4 in StepBlock", without the module's side, denominators or spans. | **True; fixed in the records** (`evidence/round1-review/minor1-records.diff`). Ledger BW-1 now carries the source-inclusive census, recomputed independently (lint census at `7c963897`; the span rule): `BufferWords` 4 of 6 declarations, **66.7%**, 45 lines (`_drop` and `_take` have no counterpart); `StepBlock` 4 of 135 (64 public, 71 private), **3.0%**, 42 lines; no copied characters (no screen pair, before or after the merge). No further member: the library's other `bufferTape` lemmas (Meyer, FragDec, ClockLoop, SymbolLift) are special cases or update identities, outside any recorded correspondence. **One-fifth rule:** `BufferWords` is past one fifth; its §1 item is `backlog.md` BW-1 (opened and acknowledged 2026-10-18, before the pack shipped), which now records the crossing. `StepBlock` is under one fifth and byte-unchanged by #140. A minor under failure mode 5: the correction adds no member, file or family, and the module with its four restatements is what the user's ruling chose. |
| 7 | note | The six give the seam layout's buffer reads; the leaves, joins and frame remain the fill's obligations. | **Carried** to the seam-layout fill's brief: list the six in its cited infrastructure, and name the derivations of phase 5's reversed unary read (`bufferTape_nat`, `_left`, `_eq_none_of_not_mem`, `List.getElem?_reverse`) and of `pairSkip`'s pair reads (`_append_shift`, `_append_mid`, by induction on `a`). Checked: the probe's six examples against the published module in the fill's import context, sealed, plus those reads, the phases 7-8 window and the table endpoint (`evidence/round1-review/BufferWordsConsumerReal.*`, exit 0; control `BufferWordsConsumerControl.*`, two failures as intended). A public `FinTM.bufferTape_reverse` (every cell; verified sealed, `BufferReverseCandidate.*`) is an optional later promotion, not part of #140. |
| 8 | note | The Rule 10 evidence covers the relevant definitions; its success logs were supplied, not re-run. | **Done.** At `7c963897` against `oleans-lbw2`: the seal file (the module plus the seal wrapper, checked) elaborates with empty output; the control fails with the same two errors; no `simp`, `simpa`, `unfold` or `dsimp` in the module, and the only other-file names it cites are the published `bufferTape_eq` and `bufferTape_nat` (`rule10-inspection.txt`). |
| 9 | note | The copy-text attestation reproduces; the four correspondences are genuine. | **Done.** The v3 screen at the merged head `7c963897` is byte-identical to `evidence/screen.txt` (140 declarations, 32 pairs, 9,662 characters; no `BufferWords` pair). The dedup schedule stands. |
| 11 | note | Elaboration and axioms were accepted as supplied. | **Done.** The module at `7c963897`, against `oleans-lbw2`: 0 errors, 0 warnings; the six axiom lines are identical to `evidence/elab-BufferWords-axioms.out`. |
| 12 | note | The lint attestation is supported; the full lint was not re-run. | **Done.** The recorded log was the pre-merge tree's. At the merged head `7c963897`: `TuringMachine` 0 FAIL, 63 WARN over 81 files, the same WARN set; `BufferWords` 118 lines, 6 public / 0 private (`lint-tm-7c963897.txt`). |
| 2–6, 10, 13, 14 | notes | Integrity and the code identity; the six statements' faithfulness at their boundaries; names, home and public text; the replay record; the finite checks. | No action. |

**#140** is on the campaign branch's tip (no `.lean` change there since `e9e97970`), so its merge
result is the replayed tree.
