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

## Round 2: ruling Q11 (T4 in its own module)

Head `110c2f9db810d243693b9a5e8976a5ad205f1bab` on the local `stmt/pairings`, rebased onto
`523d80d2d4dd8e4ed6799358831e5b3806c6187b` (range-diff 2/2 identical: `8aa111658bd0509c0fd204d605538ff440f08d02`,
`b7ca25477c1685795f2ea45cd895889f7ecaf1c8`); not pushed. Evidence: `$SP/dl-review/stmt-pairings-r2.zip`, SHA-256
`83b05fbea2fc14ab47687e6a4222dc7073f74d21cb49f22420cefdc5301d573d` (`PROVENANCE.txt`, `SHA256SUMS` inside; not committed).

| Step | Result |
|---|---|
| Split | T4 `exists_bb1_distinguisher` (21-line block: docstring, statement, `sorry`) byte-identical in the new `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (78 lines); `BonehBoyenSecurity.lean` 170 lines (T2, T3, `bb1_sidSecure`, imports the new module); facade `IdentityBased.lean` 32 lines |
| Snapshot before | 1230 files, `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` |
| Build | closure 85 modules, 20 rebuilt (8 base, 12 pairing): 20/20 rc 0, 0 errors, 4 target `sorry`s (`Assumptions` 1, `BonehBoyenMachine` 1, `BonehBoyenSecurity` 2) |
| Axioms | 320 declarations + 52 auxiliary constants; standard only except `sorryAx` in the 4 targets and `bb1_sidSecure` |
| Rule 10 | round-1 probes for the 2 changed modules: 0 errors, controls as before; whole-file seals A/B, strict and coe (`-DmaxErrors=0`) of `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased`: 12/12 pass |
| Lint | `style_lint.py` 0 findings (12 files); `campaign_style_lint.py --check8b` 0 FAIL, 2 WARN (round 1's) |
| Root `TCSlib` | 278 modules rebuilt from source (changed or missing since the tree's `eff2dcd0` sources, and downstream): 278/278 rc 0 |
| Restore | 328 backups restored (0 hash failures), 75 new oleans deleted, 13 emptied directories pruned; snapshot byte-identical |

The records branch advanced to `a32ad0df` during the job (#318, #319, #323); no pairing-closure file changed and
the branch merges cleanly.
