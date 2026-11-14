# 135-ladner-readers-gate

The first Codex audit for draft PR #302 (gate 135): the seven Ladner owner readers R1-R6.
Read pack.md (after the standards). Return the findings Markdown in chat.

| File | What |
|---|---|
| `135-ladner-readers-bundle.md` | the bundle to attach: 16 sections (one per file, in `BUNDLE-FILES.txt` order), 6440196 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `ea3c336c161f7e375bced601a7750dcc23809924299d191904d23a3fba26f24d`
- **Built by** `mkbundle-mixed.py`: the Lean files from `50bb801a28ffd86ce7b47c91d47c257ab024fade`, everything else from the
  campaign commit `cfc0428cb6e8cbd1094576dd990d6d3228e800de`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `16 segments, 0 problems`.
- **Findings:** the auditor delivers `gate135-ladner-readers-findings.md` as an attachment in chat; committed as `campaign/gates/135-ladner-readers/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
