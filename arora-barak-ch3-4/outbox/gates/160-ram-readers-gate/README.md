# 160-ram-readers-gate

The Codex audit for draft PR #370 (gate 160), the first gate on the RAM work branch `complexity/ram-simulation`: eight new public readers (all `Iff.rfl` or `rfl`, approved by Seyoon) that the tier 3 fill needs to prove the nine class corollaries of `RAMSimulation/Classes` under rule 10. Replay 265/265, seals and controls pass, no sweep flag.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate160-ram-readers-bundle.md` | the bundle to attach: 23 sections (one per file, in `BUNDLE-FILES.txt` order), 3992061 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `db6e8ccdc6de172624f4f959e6c4d2f3a7eade78ae0515b367514c3ee69d779e`
- **Built by** `mkbundle-mixed.py`: the Lean files from `e75d290706e1b05e1e43cd07cfcea94484207b25`, everything else from the
  campaign commit `c1a54b45e2a80c29986b25f2f0d2f5eb37f47d40`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `23 segments, 0 problems`.
- **Export:** only the 23 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate160-ram-readers-findings.md` as an attachment in chat; committed as `campaign/gates/160-ram-readers/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
