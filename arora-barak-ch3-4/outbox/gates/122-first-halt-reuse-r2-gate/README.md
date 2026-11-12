# 122-first-halt-reuse-r2-gate

The second Codex audit for draft PR #242 (gate 122) checks the resolution of
the maintainer hold M1 on the campaign after #241. The bundle includes the
verbatim round 1 findings, the dispositions and the fresh merged-tree replay,
seals, controls and copy screen. Return the findings Markdown in chat.

| File | What |
|---|---|
| `122-first-halt-reuse-r2-bundle.md` | the bundle to attach: 33 sections (one per file, in `BUNDLE-FILES.txt` order), 9352615 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `c1c648733c804e753bc8ba65474cb76013dd9545b4a360280995458dbcd210e7`
- **Built by** `mkbundle-mixed.py`: the Lean files from `e0b98ac2a2396324bc9ddf76f27dceb3eba5ffe3`, everything else from the
  campaign commit `752ba87f94276bfa414e86b9653bfc7aecb4c209`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `33 segments, 0 problems`.
- **Findings:** the auditor delivers `gate122-first-halt-reuse-r2-findings.md` as an attachment in chat; committed as `campaign/gates/122-first-halt-reuse/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
