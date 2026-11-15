# 141-ladner-final-gate

The first Codex audit for draft PR #325 (gate 141): Ladner fill 7, which proves target 6 `SAT_H_intermediate` and so completes Ladner's theorem `Complexity.ladner`.
Read pack.md (after the standards). Return the findings Markdown in chat.

| File | What |
|---|---|
| `141-ladner-final-bundle.md` | the bundle to attach: 17 sections (one per file, in `BUNDLE-FILES.txt` order), 1868439 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `d4a12d4873cf20249b6fb3fea604d1fca1d4a144161279644dd9a2071a6f94ac`
- **Built by** `mkbundle-mixed.py`: the Lean files from `b2d562d926a822cc59545fbc89513ca573effbd2`, everything else from the
  campaign commit `7d231ce04a7a832ce61e43f5c23ec8b1074f8c8e`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `17 segments, 0 problems`.
- **Findings:** the auditor delivers `gate141-ladner-final-findings.md` as an attachment in chat; committed as `campaign/gates/141-ladner-final/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
