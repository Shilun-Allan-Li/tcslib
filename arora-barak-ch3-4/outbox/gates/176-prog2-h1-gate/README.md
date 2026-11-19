# 176-prog2-h1-gate

The Codex audit for draft PR #394 (gate 176) on the RAM work branch: PROG-2 job H1. The vendored light language gains `inBit`, `emit`, `coin` and `half` in place, with output and coin indices on `Light.Exec` and a new stream-aware logic (`Light/IO.lean`, `Light/IO/Exec.lean`), under the signatures frozen by gate 167's mirror. The compiler's four new cases are disclosed temporary admissions until job H2. Replay 39/39; the admission walk confines admissions to the three compiler constants.
Read `pack.md` (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate176-prog2-h1-bundle.md` | the bundle to attach: 60 sections (one per file, in `BUNDLE-FILES.txt` order), 2359222 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `bfe4c61f15c02c14d4fb3a035b6cf8f16182123844c7e90a38f3ca937b1c911c`
- **Built by** `mkbundle-mixed.py`: the Lean files from `3d3d0f1aa0b59cd4ec2a2c1c83176e0b9bc5f010`, everything else from the
  campaign commit `cc42db6448653fdf8d57149652e7d1cc35dbaafc`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `60 segments, 0 problems`.
- **Findings:** the auditor delivers `gate176-prog2-h1-findings.md` as an attachment in chat; committed as `campaign/gates/176-prog2-h1/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
