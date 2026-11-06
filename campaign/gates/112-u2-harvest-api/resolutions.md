# Gate 112 (#221, the U2 harvest API): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256 `9fa721c1fbf3ce6105c5d9bf642b6715b622af72cdca2a7950fd25a01904822e`). **Verdict: PASS: 0 blockers, 0 majors,
2 minors, 6 notes.** No incorrect exported statement and no missing F6 prerequisite were found.
**The gate is CLOSED.**

| # | Severity | Disposition |
|---|---|---|
| 112-01 | minor | **Accepted; the evidence is corrected.** The scratch probe's admitted `F6Probe.route_space` is false as stated, being universally quantified over arbitrary machines and times. The auditor gives a counterexample, and the admitted `aRun` is already false. The four admission-free compositions (`two_scans`, `hosted_startup`, `final_seam`, `layout`) are the probe's evidence. `route_space` is withdrawn as a statement. F6's brief will state the route as a **conditional** check: `aRun`, `aCut` and `hloop` become explicit hypotheses, as in `final_seam`, or are specialized to F6's actual witnesses. This is recorded in the roadmap plan. |
| 112-02 | minor | **Accepted.** `Ax.lean.txt`/`Ax.out` hold **34** axiom prints (22 rows, 10 generated field equations, 2 theorems), not 28. All 34 use only the standard three or fewer. The screen population also included `Build/InterpreterStartup.lean`, which the pack omitted; its `embedSilentCfg_initCfg` is in the existing 100% pair. The counts and results stand. |
| 112-03…08 | note | No change. |

The merge waits for `replay-lhv3` on the campaign after #214 and #223.
