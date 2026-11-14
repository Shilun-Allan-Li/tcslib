# 134-sat-linear-verifier-gate

The first Codex audit for draft PR #301 (gate 134): the approved LD9 reader
`SAT_exists_linear_verifier` in ClassNP/SAT. Read pack.md (after the standards).
Return the findings Markdown in chat.

| File | What |
|---|---|
| `134-sat-linear-verifier-bundle.md` | the bundle to attach: 15 sections (one per file, in `BUNDLE-FILES.txt` order), 1573262 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `a9441142a900dd081dac65429c85b7ec93c9ef82a760402cd6b7bdff854f7b48`
- **Built by** `mkbundle-mixed.py`: the Lean files from `785e34262460b8ad9330e3c403ebfa76cc641cc1`, everything else from the
  campaign commit `50c6d4512fe44bc17ec824595e87fb40f8eaa38c`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `15 segments, 0 problems`.
- **Findings:** the auditor delivers `gate134-sat-linear-verifier-findings.md` as an attachment in chat; committed as `campaign/gates/134-sat-linear-verifier/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
