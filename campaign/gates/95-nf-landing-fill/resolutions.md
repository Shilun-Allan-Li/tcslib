# NF's landing (PR #191, a fill gate): resolutions

**Staged (2026-11-05):** `pack.md`, at #191's head `e8994dc1` (the campaign after #190 merged in).
Bundle `95-nf-landing-fill-bundle.md`, SHA-256 `15b5843f3f265051df45e46ad3c020a56adb143de72ae468d4ffed7e4ea1baf8` (415 sections), the records at
`1500583b`; in the exchange `arora-barak-ch3-4/outbox/gates/95-nf-landing-fill-gate/`.

**Replay (2026-11-05): `replay-lnf` passed**, 4 modules, 0 failed, 0 `sorry`; the static check 0
mismatches (`evidence/merged-tree/`). `NTimeHierarchy`'s theorems are on the standard axioms
(`evidence/axioms/NTHAx.out`).

#191 is clear to merge once gate 95 closes with zero blockers and zero majors.

**Dispatched (2026-11-05, the user)**, bundle SHA-256 `15b5843f…`, findings file
`nf-landing-fill-findings.md`.

## Round 1 findings (received 2026-11-05)

`findings.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/nf-landing-fill-findings.md`,
exchange commit `4da7789c395d2bad6d86d1520d7faf3709d13af9`), SHA-256
`7aa285060b2bd9d5a5c7c6f957f78c00bd7ea5098f9c8a160565650c6a4413f8`.

**Verdict: does not close.** 0 blockers, 1 major (F1, three inline re-derivations of
`BufferWords` identities in `NDNormalForm`), 4 minors (F2–F5), 4 notes (F6–F9). Dispositions
follow below as the repairs land.

**Not yet clear to merge: #191** (gate 95 has a major open).
