# External audit pack — U2-S: the universal startup's first phase (PR #130, a fill gate)

Campaign: the Arora-Barak chapters 1 and 4 work on the universal machine. The fill brief U2-S
(`campaign/fills/u2s/briefs/u2s-fill-startup.md`) targets `Turing.exists_selfStartupTMK`
(`TCSlib/Complexity/TuringMachine/UniversalK.lean`): the `k`-generic startup ending at the step
block's seam.

The worker's delivery (`campaign/fills/u2s/reviews/startup-1/u2s-1-REPORT.md`) completes phase 1
and part of phase 2, with 15 proved private helpers; **the target stays `sorry`**. The
maintainer's review is `campaign/fills/u2s/reviews/startup-1/REVIEW.md`. **It lands as a
partial.**

**The head:** `lean/u2s-partial` at `0530e5c6`, two commits on the campaign branch:
- `d7138d5a`: the worker's commit `259a349d`, cherry-picked from its verified bundle;
- `0530e5c6`: the maintainer's. The worker's "fill appendix" paragraph is removed; the progress is
  in the records. Docstring only.

## Brief for the auditor

1. **Freeze.** 12 → 12 publics, 0 → 15 privates; no statement changed (`evidence/freeze.txt`).
2. **The helpers** (`ss_*`):
   - the cleaned-canonizer bundle and its contracts;
   - the suffix-uniform first halt of the prefix;
   - the restarted returning capture, with its first return, silence and space bound;
   - the tape layout.

   Are they correct, on the brief's route, and reusable by the continuation? Do they read other
   files' definitions only through published lemmas? The review sealed 21.
3. **The review's F1:** normalizing the phase-2 return needs the buffered composite's
   second-phase fields at the composite's own tape-index type. Is the gap real? #132 adds the
   cast-indexed pair.
4. **F3:** two helpers over 20 lines have no "Proof sketch" (`ss_captureInitial`,
   `ss_capture_indices`). Is that a policy finding for this landing, or the continuation's?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lx2b`: 0 errors; 3 warnings, the module's three existing
  contracts (`evidence/elab-UniversalK.out`).
- **The review:** axioms within `[propext, Classical.choice, Quot.sound]`; the seal test; the
  174-check import probe; the v3 screen 655 → 668 declarations, with no new pair.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN.
- **Replay:** `replay-lu2s.sh`, 3 modules (`UniversalK`, `SelfUniversal`, the `TuringMachine`
  facade), from `oleans-lx2b`. **Passed (user, 2026-10-18):** 3 of 3 at `0530e5c6`, 0 failed,
  static-equal (3).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/48-u2s-startup-fill/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `u2s-startup-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
