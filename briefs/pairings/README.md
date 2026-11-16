# Pairing campaign

Scope, sources, design decisions, statements, units, questions and the decision log are in
[PairingCryptographyPlan.md](../../PairingCryptographyPlan.md). Binding rules: `policy.md`,
`../pass-shelat-ch5-8/CLAUDE.md` and `../pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2.

## Current checkpoint

Statement PR [#331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) (draft), branch
`stmt/pairings`, audited by Gate 40 at head `110c2f9db810d243693b9a5e8976a5ad205f1bab` (merge base
`523d80d2d4dd8e4ed6799358831e5b3806c6187b`). Rulings Q1–Q13 and the location ruling are accepted.
Four sorried targets, T1–T4; `bb1_sidSecure` is proved from T2–T4.

Gate 40 round 1: **HOLD** (G40-01 encoding fidelity, G40-02 seal coverage, four minors). Ruling
G40-01: injectivity fields in `IBEScheme`, proved for BB1. The maintainer's landing edit LE-gate40
is in progress; Gate 40 round 2 follows.

**Seal coverage at `110c2f9d`.** The canonical Rule 10 suite ("12/12" in the PR description) is
12 probes over three modules only: `BonehBoyenMachine`, `BonehBoyenSecurity` and the
`IdentityBased` facade. `Group`, `Joux`, `Defs`, `BonehBoyen`, `Assumptions` and `Operations`
have round-1 hand-list probes only; LE-gate40 extends the canonical suite to them.

## Contents

* `statement-phase/EVIDENCE.md` — what was checked, and how, for the draft (historical).
* `statement-phase/evidence/` — build logs, axiom census, seal probes and controls, olean-tree
  snapshot and restore records, and the tools used.
* `statement-phase/evidence-r2/` — the round-2 statement evidence for `110c2f9d`.
* `gates/40-pairings-statements/` — the Gate 40 pack, dispatch prompt and findings.

The source PDFs ([Jou00], [BB04]) are not committed; their citations, versions and SHA-256 are
in the plan's § Sources.
