# External re-audit pack — Chapter-6 circuit surface, round 2

Audits commit `12ff3add` on `complexity/arora-barak-ch1`. Round 1
(pack `audits/ch6-circuits-pack.md`, auditing `28690c01`) returned
**0 blockers, 4 majors, 7 minors, 4 notes**
(`audits/ch6-circuits-findings.md`, attached verbatim); the gate stayed
open. All fifteen findings were accepted after source verification; none
was contested. The repairs — commit `12ff3add`, **documentation only,
zero Lean statements changed**, as §5 of the findings permits for
deliberately deferred bridges — are itemized in
`audits/ch6-circuits-resolutions.md` (attached), which also acknowledges
the two round-1 **pack errata** (the §6.5/§6.6 misplacement and loose
item ranges of finding 10; the 22-vs-23 sweep-list count of finding 11,
explained there). The sent round-1 pack is immutable per protocol.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Freeze.** `12ff3add` touches, relative to the audited `28690c01`:
   eleven in-scope Lean files, the facade, the catalog, and
   `backlog.md` §3 — docstrings, module-docstring ledgers, and one
   section header only. `git diff 28690c01..12ff3add` contains no change
   to any `def`/`theorem`/`lemma`/`structure`/`instance` signature or
   body. Zero sorries in scope, as before.
2. **Elaboration.** Post-repair fresh-olean sweep, Lean 4.25.0 / mathlib
   `029db123ddaa`: the 22-entry circuit list, the 31 Switching/LMN
   reverse-dependency modules, and the catalog — 55 modules, zero
   `error:` lines.
3. **Policy.** Style lint: 0 FAIL / 0 WARN over the `CircuitComplexity/`
   directory, unchanged.

## What round 2 asks

This is a **verification round**, not a fresh audit. The round-1 attack
results (§3 of the findings: all guards held) and the verdicts already
*faithful* or *faithful-with-declared-divergence* are settled unless a
repair touched their text. Tasks:

1. **Majors 1–4.** For each, judge whether the repair discharges the
   finding: the wrapper re-description and its catalog/module-docstring
   propagation (finding 1); the normal-form re-attribution and the
   three-carrier metric ledger (finding 2); the restriction of
   preservation claims to the polynomial union and the de-identification
   of `InSIZE` from AB's fixed `SIZE(T)` in `PPoly.lean`, `Hierarchy.lean`,
   and the facade (finding 3); the hard-function incomparability rewrite
   and the facade's "tree-circuit analogue" phrasing (finding 4).
2. **Re-issue the task-1 verdicts** for [AB09] Def 6.1 and Def 6.2 — the
   two *divergent-undeclared* rows — and the Thm 6.21 row, against the
   repaired ledgers.
3. **Sweep the minor repairs** (findings 5–10 as itemized in the
   resolutions file) for correctness and completeness, including that no
   repair introduced a new misstatement.
4. **Confirm the recordings**: notes 12–15 in `backlog.md` §3 (excerpted
   in the resolutions file), and the two pack errata as acknowledged.
5. **Residual pass.** Anything newly visible in the repaired prose that
   round 1's severity scheme would catch.

Severity scheme and response format as in round 1; findings to
`audits/ch6-circuits-reaudit-findings.md`. The gate closes on zero
blockers/majors in this round.
