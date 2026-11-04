# E-Q cont1, the stage query's main machine (PR #176, a fill gate): resolutions

**Gate, round 1:** the fill gate of PR #176 (`lean/eq-cont1-landing` at `cecd76a0`). Pack `pack.md`;
bundle SHA-256 `43a728a1192f8ea959ba7b3b9ff03c0ad09519c6c1b4dc9bf004123272e527ca` (282 sections),
the Lean at `cecd76a0f996411d5371f91e8d4e3757e122fd60`, the records at `00757f88`. **Staged
(2026-10-27); dispatched (user, 2026-11-03).** **Findings** (`findings.md`, verbatim, SHA-256
`148f1cb2ecfef849636f59f36aa79ab55b621bfc7016d62281a0f7ced60ae943`; received 2026-11-04): **PASS,
0 blockers, 0 majors, 3 minors, 7 notes.** The gate is closed.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | "Its 289 controls close unsealed and fail sealed" is false: 279 of 289 close unsealed; ten generic `rfl` controls fail unsealed, each covered by an equation control. | **True; erratum** (the pack's rule-10 item). The review's own summary (`campaign/fills/eq/reviews/fill-cont1/out/16-seal-summary.txt`) has the right counts, which the pack condensed wrongly: `rfl` 275 controls, unsealed 265 pass (the ten recursive definitions `FinTM.sweepFold`, `NDTM.runWith`, `codeReadUnary`, `codeReadVec`, `codeSkipRepeat`, `decFixed`, `incFixed`, `mealyRun`, `pairDecode`, `unaryTokenSplit` fail unsealed); equation 10 of 10 and `simp` 4 of 4 pass unsealed; all 289 fail sealed; each of the 275 sealed definitions has a control that closes unsealed and fails sealed. Future packs quote the three counts separately. The dispatched pack is kept as dispatched. |
| 2 | minor | `qy_call_bound`'s local `hb` re-derives `Turing.length_bits_le_self` (`Encoding`). | **True** (the same file cites `length_bits_le_self` at three other sites). **Ruled (user, 2026-11-04): the one-line re-point lands with E-D's landing**, by the maintainer, under E-D's fill gate; #176 merges as gated. Recorded in the ledger's NB-1 until then; E-D's brief lists it as a landing item, not a fill region. |
| 3 | minor | RO-1/NB-1 lack source-inclusive, cumulative per-file accounting; NB-1 omits `SpaceAmplifyPoly`. | **True; fixed** in `campaign/duplication-ledger.md`. NB-1's census is source-inclusive: `SpaceAmplifyPoly` 1 of 20 (5%; `two_pow_bits_le`), `Encoding` 1 of 61 (`length_bits_le_self`, finding 2's original), `Machines/Bin` 2 of 12, and `NTimeDiagonalizer` 3 of 236 (finding 2's inline step counted as RO-1 counts inline steps). A cumulative paragraph adds the families per file: `NTimeDiagonalizer` 4 of 236 (1.7%), `Encoding` 2 of 61 (3.3%). Below one fifth; no new acceptance needed, as the finding says. |
| 4 | note | Integrity, freeze and landing provenance check out. | Agreed. |
| 5 | note | The target is proved as stated; the axiom census mixes source and harness constants. | Agreed. Future censuses label the source namespace (1,291 standard-axiom constants and the admitted `exists_diagonalizer`) and the audit harness (32) separately. |
| 6 | note | The locator, cost ledger and emitted query agree with the frozen contract, boundary cases included. | Agreed. |
| 7 | note | The route is the authorized one; F11's sketch mismatch stays deferred. | Agreed. The deferred docstring cleanup's F11 entry (backlog) now names both corrections: unary rung construction and comparison, and the degree-six accumulated overhead. |
| 8 | note | No forbidden reduction or manual public API; the ref snapshot is smaller than the review's historical census. | Agreed. Future packs distinguish the current ref snapshot from a historical census. |
| 9 | note | The screen comparisons and debt dispositions are supported, subject to findings 2–3. | Agreed; findings 2–3 are resolved above. |
| 10 | note | The replay and lint reproduce; PASS covers this fill gate, not the admitted diagonalizer. | Agreed. |

**The replay:** `replay-leqc1.sh` (`evidence/merged-tree/`), 3 modules from `oleans-lnfapi4`.
**Passed** (user, 2026-10-27): 3 of 3 at `cecd76a0`, static-equal; snapshot `oleans-leqc1`.

**Merge state. #176: not yet clear to merge** (2026-10-27): the replay passed; it waits for gate 87.

**Merge state (2026-11-04).** Gate 87 passed. **Ruled (user, 2026-11-04): #176 merges before
#177** (their downstream closures share `NTimeHierarchy` and `Diagonalization`). The campaign has
had Lean changes since `oleans-lnfapi4` (#175 and `main`'s merge-in, the tree of `oleans-lscp3`), so
#176 takes the campaign merged in and a merged-tree replay of its 3 modules from `oleans-lscp3`
(`replay-leqc2`). **#176: not yet clear to merge**: it waits for `replay-leqc2`.
