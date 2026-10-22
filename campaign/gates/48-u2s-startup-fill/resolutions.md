# U2-S: the universal startup's first phase (PR #130, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #130 (`lean/u2s-partial` at `0530e5c6`): 15 proved private helpers
toward `Turing.exists_selfStartupTMK` (`TuringMachine/UniversalK.lean`), which stays `sorry`. Pack
`pack.md`; bundle SHA-256 `dc501850bdeacf3e571d602149c5b7389d306693d2320aee906423b63368cee5`
(33 sections; folder `48-u2s-startup-fill-gate/`). Replay passed (user, 2026-10-18): 3 of 3.

**Round 1** (`findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 1 minor, 12 notes.** The
maintainer verified the minor at `0530e5c6`; the notes recommend no change to this landing.
**The gate is closed.** #130 was declared clear to merge (2026-10-18).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `ss_captureInitial` (line 324; 29 tactic lines) has only a statement docstring, no proof sketch (`policy.md` §3); `ss_capture_indices` (line 446) would benefit from a short one. | **True** (the eight lines above each declaration hold one docstring, without "Proof sketch"). **Deferred (user, 2026-10-18: "defer and merge tonight").** The U2-S continuation's brief makes it a required landing item: `ss_captureInitial`'s sketch (partition the host tapes into selected, capture and frame cases; their blank contents and zero heads; conclude by `Cfg.ext`), and a short inequality sketch for `ss_capture_indices`. |
| 2–13 | notes | F1's cast-indexed field gap is real and affects the continuation only; integrity, scope and freeze (590 lines landed); the definitions; the cleaned canonizer; the suffix-uniform first halt; the capture contract; boundary instances; the interfaces; duplication; axioms; the execution records; landable as a partial. | No action for this landing. Carried to the U2-S continuation's brief: note 2 (pin it after the cast API's gate, #132; keep the `prefixCanonTM_eq` transport), note 5 (keep the actual virtual input position when clearing the code buffer), note 7 (keep the selected canonizer time's halt, output and cleanup witnesses), note 8 (the boundary instances as Lean sanity examples), notes 4 and 9 (promote generic adapters before a second consumer), note 13 (endpoint normalization and the seam-layout route, with a common return time). The worker report's "escalations: none" is superseded by the review's F1 (note 2). |
