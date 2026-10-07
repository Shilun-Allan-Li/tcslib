# Chapter 2 fill campaign, Epoch 1 — audit loop resolutions (CLOSED, 2026-10-02)

Protocol: `workflow.md` §§3–4 (epoch gates follow the phase-gate rule).
Round 1: pack `audits/ch2-epoch1-pack.md` (auditing the integrated epoch-1
state, agent commits `07cf205a`…`b5ff4c75` on base `7494522e` plus the
integration record `708779af`), findings `audits/ch2-epoch1-findings.md`
(preserved verbatim) — **0 blockers, 0 majors, 1 minor, 1 note: PASS; the
gate closes in one round**, the campaign's first single-round epoch gate.
All 27 fills and all 19 private helpers examined; no mathematical defect
found; the composition-exponent arithmetic, parser fuel accounting,
truncation direction, and timed complementation were independently
re-derived by the auditor, supplemented by exhaustive finite models
(~240,000 boundary cases). Maintainer dispositions D1–D3 accepted.

## Findings and their sweep

| # | Sev. | Resolution |
|---|---|---|
| E1-1 | minor | **Swept in the closing commit**: `falsifyingCNF_width`'s docstring now reads "Every truth-table clause has width at most the prescribed arity; its constructed length is exactly that arity" (the auditor's proposed text) — matching the exported `WidthAtMost` contract instead of the stronger true-of-the-construction property. Docstring-only; the touched module and its downstream re-swept. |
| E1-2 | note | **Evidence boundary retained, as disposed by the auditor.** The bundle carries the mathematics, sources, reports, and axiom log, not the base checkout, patch archives, checkers, or build environment; those remain maintainer attestations (the standing bundle practice). Offer recorded: a future epoch bundle can attach the freeze-checker scripts and sweep logs on request — the sweep log is already committed at `audits/logs/ch2-e1-sweep-53mod.log`, outside the bundle. |

Auditor's supplementary suggestion recorded: `le_foldr_max_of_mem` joins
`foldr_max_le_of_forall` as a candidate in the deferred D3 shared-utility
promotion (`backlog.md` §2).

## Closure

Epoch-1 gate **CLOSED** 2026-10-02 at the closing commit. State of the
campaign: **27 of 59 Chapter-2 admissions proved** (32 remain: E2 — the
enumerator, the NDTM compilations, Exercise 2.1 + the HALT pair, TMSAT with
the `timed_universal` bridge; E3 — padding, the SAT track, snapshot
locality; E4 — the Cook-Levin summit and the TAUTOLOGY dual). Axiom state
of the fills: zero `sorryAx`, 16 standard-triple, 10 proper-subset, one
axiom-free. Next: the E2 briefs (2A–2D), with the D1 wording correction
("at most the standard triple").
