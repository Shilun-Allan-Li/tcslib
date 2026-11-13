# 132-runfrom-one-r2-gate

The second Codex audit for draft PR #296 (gate 132, dedup family RO-1) checks the
resolutions of round 1's three minors: the library-wide one-step sweep and its
repairs, now in 68 citing owners, and the corrected counts. The bundle includes the
verbatim round 1 findings, the fresh merged-tree replay, the base-against-head seal
comparison, the paired controls and the copy screen. Return the findings Markdown in chat.

| File | What |
|---|---|
| `132-runfrom-one-r2-bundle.md` | the bundle to attach: 90 sections (one per file, in `BUNDLE-FILES.txt` order), 27549572 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `03bec7f7cf8d8333797e93dae193734f754a1159807994d1cb5c396d40273d70`
- **Built by** `mkbundle-mixed.py`: the Lean files from `ce427bde6ee5464a4146dce2b3add69b7a05677d`, everything else from the
  campaign commit `501f19ddf7f44f966f24c0bc7d82c1bd4a36de1d`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `90 segments, 0 problems`.
- **Findings:** the auditor delivers `gate132-runfrom-one-r2-findings.md` as an attachment in chat; committed as `campaign/gates/132-runfrom-one/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
