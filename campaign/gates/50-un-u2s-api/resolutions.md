# The UN/U2-S API (PR #132, an API gate): resolutions (round 1; gate CLOSED)

**Gate:** the API gate of PR #132 (`lean/un-u2s-api` at `91154701`): `FinTM.pairExtractTM_fst_run`
and `_run_budget` in `Build/Primitives`, and the cast-indexed pair
`FinTM.bufferedSecondCfg_workTapes_cast` / `_workTapePos_cast` in `Simulation`. Pack `pack.md`;
bundle SHA-256 `288f662c2a03f7c777d514fd6c00ebf21ab4f9fab1779850985f0cd2807a9f11` (26 sections;
folder `50-un-u2s-api-gate/`). Replay passed (user, 2026-10-18): 314 of 314, static-equal (93).

**Round 1** (`findings.md`, verbatim; received 2026-10-21): **PASS, 0 blockers, 0 majors, 1 minor,
11 notes. The gate is closed.** The minor is fixed on #132 before it merges (commit `a8fc3aaa`),
and the 314-module closure is replayed again for it (`replay-l132b.sh`).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | Rule 10 binds the maintainer's API proofs too (the pack's question 3): `hinit` reduces `MultiTapeTM.initCfg` and `Cfg.init`, and `hlast` unfolds `MultiTapeTM.step` and `Action.apply`, where published equations exist. | **True; fixed** in `a8fc3aaa` (`evidence/round1-fix/fix.diff`), proof only. `hinit` rewrites by `MultiTapeTM.initCfg_eq` and the `Cfg.init_*` field equations (with `funext` on the pointwise fields); `hlast` steps by `MultiTapeTM.step_of_some` and the `Action.apply_*` field equations, with `Cfg.workTapeSymbols_eq` and `Function.update_eq_self` for the unwritten tape. Checks (`evidence/round1-fix/`): the repaired module elaborates against `oleans-l132` with 0 errors and the head's 51 existing diagnostics unchanged; the freeze shows 49 → 49 public and 236 → 236 private, the only body change the target's; with `MultiTapeTM.initCfg`, `Cfg.init`, `MultiTapeTM.step`, `Action.apply` and `FinTM.bufferTape` `local irreducible`, the proof elaborates; the control (`rfl` on the initial configuration's output) fails under the seal. Irreducibility does not stop a `simp` given a definition explicitly (the control's second example shows it), so every `rw`/`simp` argument was inspected: each one naming another file is a published theorem; the only definitions named are this file's `pairExtractTM` and `extractCfg`. **The gate's answer to question 3 is applied from now on:** maintainer API proofs read other files' definitions only through published equations, as fills do. |
| 7 | note | The additions close the two interface gaps; transport through `prefixCanonTM_eq`, the capture's normalization, cleanup, assembly and the ledgers remain the consumers' obligations. | **Carried** to UN's and U2-S's continuation briefs. |
| 8 | note | The U2-S review's positive sealed run was reviewer-reported; only the two failing logs were supplied. | **Done.** `evidence/round1-fix/U2SPhase2TransportPositive.lean.txt`: both phase-2 goals rewrite under the review's seal by the **published** pair (no draft lemma declared), exit 0, against `oleans-l132`. |
| 11 | note | The lint log was the API tree's, not the merged head's. | **Done.** Lint at `a8fc3aaa` (the merged head with the fix): `TuringMachine` 0 FAIL, 63 WARN over 80 files; `UniversalK` 590 lines, 12 public / 15 private (`evidence/round1-fix/lint-tm-a8fc3aaa.txt`). |
| 2–6, 9, 10, 12 | notes | Integrity and the additions-only freeze; the extractor's exact run, budget corollary and adversarial instances; the cast pair's fields; public text and no new duplication; the elaboration and replay records, with the limits of a packet-based audit. | No action. |

**Re-replay for the fix: passed (user, 2026-10-21):** 314 of 314 at `a8fc3aaa`, 0 failed,
static-equal (93), the module list in the same order (`evidence/round1-fix/replay-l132b.*`).
**#132 merged** (2026-10-22 00:50 UTC, `e9e97970`); the merge brings no change to `TCSlib/`
beyond `a8fc3aaa`'s. The seven waiting PRs (#133, #134, #136–#140) had the campaign merged in
(no conflict; their own files byte-unchanged) and replay from `oleans-l132b`; #139 after #134,
since both closures contain `SpaceComplexity/WindowClock`.
