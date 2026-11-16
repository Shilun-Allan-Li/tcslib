# Pairing statement draft: evidence

Draft: `stmt/pairings` at `ce9c3728ec582be45fc33ca68d64b5533701093d` (modules
`b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01`), base `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543`.
`$SP` is the session scratchpad (`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`);
the tools expect it in the environment.

Method. No `lake build`, no cache get. Lean 4.25.0 (`PATH=$HOME/.elan/bin:$PATH`), one process at
a time, only on `TCSLIB_OLEANS=$SP/dl-oleans-2`. Python as `python3 -I`.

| Step | Evidence | Result |
|---|---|---|
| Snapshot before | `tree/snapshot-pre.txt` (`tools/snapshot.py`) | 1230 files, `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` |
| Closure and base delta | `build/closure.txt` (`tools/closure.py`, 73 modules at the base), `build/rebuilt-base-modules.txt` (`tools/downstream.py`) | only `Foundations/BitLists` changed since `eff2dcd0`; it and 7 downstream modules rebuilt |
| Backups | `tree/backed-up.txt` | 8 oleans, hashes equal to the snapshot |
| Base rebuild | `build/base-rebuild-1.txt`, `build/base-rebuild-2.txt` | 8/8 rc 0 |
| New modules | `build/summary.txt`, `build/*.log` (`tools/ladder.sh`) | 11/11 rc 0, 0 errors, 4 target `sorry` warnings |
| Axioms | `axioms.txt` (`tools/AxiomProbe.lean`) | 320 declarations + 52 auxiliary constants; standard axioms only, except `sorryAx` in the 4 targets and `bb1_sidSecure` |
| Rule 10 | `seal/summary.txt`, `seal/*.log` (`tools/seal.py`, `tools/runprobes.sh`) | 7/7 modules 0 errors besides "unknown constant" for names outside a closure; controls: negative fails, positive passes |
| Restore | `restore/restore-log.txt`, `restore/empty-dirs-before-prune.txt`, `tree/snapshot-post.txt` | 8 restored, 15 new oleans deleted, 4 empty dirs pruned; snapshot byte-identical |

Style: `scripts/style_lint.py` 0 findings in 11 files; `scripts/campaign_style_lint.py --check8b`
0 FAIL, 2 WARN (check-8 acronym heuristic; readers exist). Widths at most 100 characters; files at
most 553 lines.

`SHA256SUMS` lists every file of `evidence/`.
