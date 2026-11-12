# 121-fe-live1-cleanup-r2-gate

The second Codex audit for draft PR #241 (gate 121) checks the repairs of the
round 1 major and minor on the campaign after #251. The bundle includes the
verbatim round 1 findings, the dispositions and the fresh merged-tree replay,
seals, controls and copy screen. Return the findings Markdown in chat.

| File | What |
|---|---|
| `121-fe-live1-cleanup-r2-bundle.md` | the bundle to attach: 25 sections (one per file, in `BUNDLE-FILES.txt` order), 4999075 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `f44a13d3000bdac0a446158dcf1ec61fc3fc73aac5e59d8acadcaa5aadc20549`
- **Built by** `mkbundle-mixed.py`: the Lean files from `0f6f07eba0c2d91dbb082287f6479cb0962dc377`, everything else from the
  campaign commit `7ea7529e06aed6be55d1979925e31fe0de0fdc68`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `25 segments, 0 problems`.
- **Findings:** the auditor delivers `gate121-fe-live1-cleanup-r2-findings.md` as an attachment in chat; committed as `campaign/gates/121-fe-live1-cleanup/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
