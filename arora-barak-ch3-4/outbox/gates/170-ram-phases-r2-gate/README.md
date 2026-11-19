# 170-ram-phases-r2-gate

Round 2 of the Codex audit for draft PR #386 (gate 170) on the RAM work branch: tier 2 job D, the phase interfaces. Round 1 was HOLD (0/2/2). The Codex repair round cites `Segment.trans`/`Segment.zero` (G170-01) and unifies the one-exit and two-exit structures into one `PhaseCertificate` (G170-02); the kit's admission walk shows both targets reach no admission (G170-03); all citation homes are bundled and screened (G170-04). Replay 172/172, seals and controls pass.
Read `pack-r2.md` (after the standards and round 1's `findings.md`). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate170-ram-phases-r2-bundle.md` | the bundle to attach: 75 sections (one per file, in `BUNDLE-FILES.txt` order), 7297070 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `1616768b0be66f73e8fa350d9fa85f7fc3ded70ea200d31a960e402c6e854743`
- **Built by** `mkbundle-mixed.py`: the Lean files from `113975d68167062693583a9bbbf63a982b80b817`, everything else from the
  campaign commit `4eb2e47c48e493129232d39b407b449f69a126a3`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `75 segments, 0 problems`.
- **Findings:** the auditor delivers `gate170-ram-phases-r2-findings.md` as an attachment in chat; committed as `campaign/gates/170-ram-phases/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
