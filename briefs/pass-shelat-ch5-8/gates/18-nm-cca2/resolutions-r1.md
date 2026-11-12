# Gate 18 · resolutions (round 1) — CLOSED

Codex findings `findings/gate18-nm-cca2-findings.md` (verbatim; `findings/SHA256SUMS`): **CLEAR (PASS)** at
Lean head `1636480237286f538bb75b0021b2285edcd0b5b9`, **0 blockers, 0 majors, 0 minors, 0 notes**.

- No repair. PR #294's head is unchanged from the audited head (verified with `git ls-remote`).
- The auditor's independent replay: 159/159 fresh upstream-closure build, 0 errors; target, both directions and
  both new readers `[propext, Classical.choice, Quot.sound]`; 313 stored constants of the five files standard;
  seals A and B match the review (OracleSecurity B's four errors are inherited and identical at the base).
- The auditor agrees with deferring DL-36 and with the scheduled `OracleSecurity` split (ruling 2026-11-12).
- The findings name a companion ZIP of fresh logs; only the Markdown was received. It is not needed to close the
  gate (no findings to resolve).

The gate closes at zero blockers and zero majors.
