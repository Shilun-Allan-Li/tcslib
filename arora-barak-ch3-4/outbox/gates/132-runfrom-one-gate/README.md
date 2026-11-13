# 132-runfrom-one-gate

The Codex audit for draft PR #296 (gate 132, dedup family RO-1) checks the new public
`MultiTapeTM.runFrom_one` in Deterministic and its citation at one-step sites in 59
owners. The bundle includes the merged-tree replay, the base-against-head seal
comparison, the paired controls and the copy screen. Return the findings Markdown in chat.

| File | What |
|---|---|
| `132-runfrom-one-bundle.md` | the bundle to attach: 76 sections (one per file, in `BUNDLE-FILES.txt` order), 24726285 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `d8a68f99849f7050283c6e1d28b8c3ee4905990748314ca3027578ce60d8d534`
- **Built by** `mkbundle-mixed.py`: the Lean files from `677970b0e7bba401a707e409b5c275a664924f0b`, everything else from the
  campaign commit `78e04fd30737af0506560f5c92bcc71d63806ee8`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `76 segments, 0 problems`.
- **Findings:** the auditor delivers `gate132-runfrom-one-findings.md` as an attachment in chat; committed as `campaign/gates/132-runfrom-one/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
