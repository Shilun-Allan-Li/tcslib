# Gate 97 (G5's consumer API, #197): resolutions

**Staged (2026-11-05)** on the exchange at `arora-barak-ch3-4/outbox/gates/97-zone-step-api-gate/`
(exchange commit `421de225`): bundle `97-zone-step-api-bundle.md`, 91 sections, SHA-256
`e1de882fd8ddb022d276e61fbc74ab3a3fcb5dc5a2be884dc48abe9a8e3c84b8`. Lean files from the PR head
`0a1b64d59b707df679e66201496f2bced7197a98`, everything else from the records commit
`6ab5d4c8f6e8472abd52ad8c278f447b7a1c359a`. Findings file `zone-step-api-findings.md`.

**Replay (2026-11-05): `replay-lzsa` passed**, 111 modules, 0 failed; the static check 0
mismatches, the campaign's existing 45 `sorry`s (`evidence/merged-tree/`).

#197 is clear to merge once gate 97 closes with zero blockers and zero majors.

**Supplementary sweep before dispatch (2026-11-05, cloud session):** the inline-step sweep and the
statement-shape grep that gates 95 and 96 found missing (their F5 and F6), run on #197's added
lines: no hit, and one candidate, the private `zs_rowPre_mapState`, which is RN-1's kind (at most
an accounting minor) (`evidence/sweep/README.md`). The staged bundle stands.

## Round 1 findings (received 2026-11-05)

`findings.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/zone-step-api-findings.md`,
exchange commit `60bbdc84187f9a910222845eab2e8fd3f304426d`), SHA-256
`a4b9f7a53941f34b1cbb8f2080b5189ae2a7073ebd69c2a42f2f1e1d15336eac`.

**Verdict: PASS.** 0 blockers, 0 majors, 6 minors (F1–F6), 7 notes (F7–F13). The gate closes
with the minors swept in a closing commit on #197, F1 re-verified by a sealed elaboration of
`ZoneRebalance` with `Contract.zero` irreducible, and the merged-tree replay re-run. Dispositions
follow with the sweep.

**Not yet clear to merge: #197** (the closing sweep and its replay are owed).
