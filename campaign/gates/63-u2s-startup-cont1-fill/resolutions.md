# U2-S continuation 1: the `k`-generic startup (PR #147, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #147 (`lean/u2s-startup-cont1` at `28150fc1`: the worker's four
commits, the maintainer's status commit `c6733db3` and a merge of the campaign branch after #145,
#146 and #148). `Turing.exists_selfStartupTMK` is proved and admission-free on the merged tree.
Pack `pack.md`; bundle SHA-256 `d2b3dd1feb414428d254be3551ba154b2eb930d168e6151296ae9d98518aa9b6`
(182 sections; folder `63-u2s-startup-cont1-fill-gate/`). Replay `replay-lu2sc1.sh` passed (user,
2026-10-22): 6 of 6 at `28150fc1`, static-equal (4).

**Round 1** (`findings.md`, verbatim; received 2026-10-22, SHA-256
`44aa6702ed5c0a8cbd950c606d0ec91f17b01ecb9ce06976486d0b36f691eecc`): **PASS, 0 blockers, 0 majors,
4 minors, 15 notes. The gate is closed.** The maintainer checked the four minors directly (the
review sub-agents were all occupied): all true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The frozen sketch's capture time (`3|α| + 4 + E.canonizerTime |α|`) and `timed_rewind` do not describe the construction, which uses the cleaned canonizer's first halt and the rewind contracts. | **True; fixed.** Maintainer commit `741490ee` (docstrings only): an `**Implementation.**` paragraph after the frozen sketch, as for #146, naming the cleaned canonizer's first halting time (`MultiTapeTM.exists_first_halt`), the code buffer's cleanup with its empty-code parameter, and `FinTM.rewind_scan`/`FinTM.rewind_heads`. The statement and the sketch are unchanged; the code is identical with comments stripped; `UniversalK` elaborates against `oleans-lu2sc1` with only the other two stubs' sorry warnings (`evidence/round1/docfix.patch`, `elab-UniversalK-docfix.out`). It is in #147's re-replay after #149. |
| 2 | minor | The worker's probe inventory is incomplete: 121 checks of 118 names, and four cited public lemmas absent. | **True; fixed in the records.** The probe deduplicated and the four added (`FinTM.bufferTape_left`, `FinTM.moveInputPos_neg_val`, `MultiTapeTM.runFrom_zero`, `Cfg.ext`): 122 checks of 122 names, 0 errors as a standalone import against `oleans-lu2sc1` (`evidence/round1/U2SProbeDedup.*`). **Report erratum** `campaign/fills/u2s/reports/startup-cont1-ERRATUM.md`. The auditor's reading of the review's F3 (control and checkpoint observations as qualifications, not report errors) is accepted. |
| 3 | minor | One bundled delivery excerpt (`cache-get.log`) is not byte-identical to its manifest entry: four carriage returns are missing. | **True; the cause is the bundle builder.** The repository copy keeps the four carriage returns and hashes to the manifest's `c33110c6…`. `mkbundle-mixed.py` decoded files with newline translation, and `verifybundle.py` compared with the same translation, so the check missed it. Both now keep carriage returns, and `stage.sh` runs the repository copies (`devtools/seyoon/`); a test build keeps all four. The delivery README now qualifies its byte-for-byte claim for the bundle. |
| 4 | minor | Two review descriptions overstate their saved evidence: the clash check at #144 queried a wrong ref; the fetch retry failed on a missing `timeout`, not the network. | **True; review erratum** (here; the review stays as written). The review's "no clash at #144" reads "the clash check ran against a misnamed ref (`origin/lean/exhaustive-sketches`, no such ref)", and its retry reads "failed with `timeout: command not found` (exit 127)". **Redone:** no `TCSlib` file at the campaign tip (which contains #144) or at #149's head mentions the derived names of the private `ss_RewindState` (`evidence/round1/clash-check.md`). |
| 19 | note | The replay supports `28150fc1`; it does not substitute for the re-replay after #149. | **True.** After #149 merges, the campaign branch is merged into #147 and its six modules re-replay on that tree (with `741490ee`). |
| 5–18 | notes | Integrity and freeze; the quantifier order; the definitions; the buffer machines; the empty-code and one-cell cases; the capture; the rewind; the R2 assembly, silence and space; `k = 0` and `k = 1`; the admission evidence; rules 10 and 11; duplication, lint and status text; the sweep and environment. | No action. Note 18's cache inventory is addendum v2.5's (already issued). |

**Merge state. #147: not yet clear to merge.** It merges after #149 (whose 324-module closure
contains its six), then re-replays on the merged tree.
