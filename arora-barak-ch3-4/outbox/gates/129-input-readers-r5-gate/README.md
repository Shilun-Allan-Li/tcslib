# 129-input-readers-r5-gate

The fifth Codex audit for draft PR #251 checks the no-write, action and
suffix-copy proof reuse. The bundle includes the verbatim round 4 findings,
the current dispositions and the verified merged-tree replay. Return the
findings Markdown in chat and paste the table and verdict there.

| File | What |
|---|---|
| `129-input-readers-r5-bundle.md` | the bundle to attach: 27 sections (one per file, in `BUNDLE-FILES.txt` order), 21157385 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `9508e91dc39514a9b32e8a99ee2c4c536529fdada0ad88adb89d7903b95e41bb`
- **Built by** `mkbundle-mixed.py`: the Lean files from `c2fbacf42718b16c03fc0e61b571a9cf2f8c6ecb`, everything else from the
  campaign commit `20e8e2825640b1ba0f4e4e870d0b2a86beeeb313`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `27 segments, 0 problems`.
- **Findings:** the auditor delivers `gate129-input-readers-r5-findings.md` as an attachment in chat; committed as `campaign/gates/129-input-readers/findings-r5.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
