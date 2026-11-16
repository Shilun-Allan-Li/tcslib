# Pairing campaign

Scope, sources, design decisions, statements, units, questions and the decision log are in
[PairingCryptographyPlan.md](../../PairingCryptographyPlan.md). Binding rules: `policy.md`,
`../pass-shelat-ch5-8/CLAUDE.md` and `../pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2.

## Current checkpoint

Statement PR [#331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) (draft), branch
`stmt/pairings`, at head `9e7a96481785d6cac4dea3b2e990c49ac278b060` (merge base with the records
branch `673a27158338437896c624df32bf5421c6ba45cf`). Rulings Q1–Q13, the location ruling and ruling
G40-01 are applied. Four sorried targets, T1–T4; `bb1_sidSecure` is proved from T2–T4.

Gate 40 round 1 (at `110c2f9d`): **HOLD** (G40-01 encoding fidelity, G40-02 seal coverage, four
minors). Since then the head gained LE-gate40 (`3f9c49e5`, `70c1f444`: the injectivity fields
`encPP_inj`, `encSK_inj`, `encCT_inj` of `IBEScheme` with their BB1 proofs, and the minors
G40-03 to G40-05), the signed merge `39d42e23` of the records tip (with #332 and #333; the shared
facades by union) and LE-doc-abs `9e7a9648` (docstring only). Gate 40 round 2 is staged
(`gates/40-pairings-statements/pack-r2.md`; dispositions in `resolutions-r1.md`).

**Seal coverage.** At `110c2f9d` the canonical Rule 10 suite ("12/12" in the round-1 PR
description) was 12 probes over three modules only: `BonehBoyenMachine`, `BonehBoyenSecurity` and
the `IdentityBased` facade; the other modules had round-1 hand-list probes only. LE-gate40 ran the
canonical suite at `70c1f444` on 10 owners: `Group`, `Assumptions`, `Operations`, `Joux`, `Defs`,
`BonehBoyen`, `BonehBoyenMachine`, `BonehBoyenSecurity` and the `IdentityBased` and
`AdvancedEncryption` facades (term-collected seals strict A/B and coe A/B, 40 probes; paired
controls; explicit-unfold scan). The other three changed files (`Pairing.lean`, `KeyExchange.lean`
and the root `TCSlib.lean`) contain imports only.

## Contents

* `statement-phase/EVIDENCE.md` — what was checked, and how, for the draft (historical).
* `statement-phase/evidence/` — build logs, axiom census, seal probes and controls, olean-tree
  snapshot and restore records, and the tools used.
* `statement-phase/evidence-r2/` — the round-2 statement evidence for `110c2f9d`.
* `gates/40-pairings-statements/` — the Gate 40 pack, dispatch prompt and findings; the
  resolutions and the round-2 pack, with the LE-gate40 evidence (`landing-r1/`) and the build of
  the head on the records tip (`integration-tip/`).

The source PDFs ([Jou00], [BB04]) are not committed; their citations, versions and SHA-256 are
in the plan's § Sources.
