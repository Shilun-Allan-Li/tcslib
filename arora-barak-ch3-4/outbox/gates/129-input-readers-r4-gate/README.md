# 129-input-readers-r4-gate

The fourth Codex audit for PR #251 checks the repaired input readers,
proof reuse and approved word-seam equation. The bundle pins the successful
current-base replay and the full audit evidence. Return the findings
Markdown in chat and paste the table and verdict there.

| File | What |
|---|---|
| `129-input-readers-r4-bundle.md` | the bundle to attach: 26 sections (one per file, in `BUNDLE-FILES.txt` order), 28058223 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `5486c689847b43033b2e58b29e71077aefcf15ea6d53c877081e8972c89bd74b`
- **Built by** `mkbundle-mixed.py`: the Lean files from `39dfa843b02ae7fdd0acaeacfadf5bba17a60feb`, everything else from the
  campaign commit `26043b0b86cfa060b8eec5b8398b2a748feac239`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `26 segments, 0 problems`.
- **Findings:** the auditor delivers `gate129-input-readers-r4-findings.md` as an attachment in chat; committed as `campaign/gates/129-input-readers/findings-r4.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
