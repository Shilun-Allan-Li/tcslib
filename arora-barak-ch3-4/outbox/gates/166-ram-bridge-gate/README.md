# 166-ram-bridge-gate

The Codex audit for draft PR #379 (gate 166) on the RAM work branch: crypto bridge wave 1. Word-RAM programs become PolyTimeComputable functions (progOut, polyTimeComputable_of_computes/_progOut), with polynomial word sizes, and timeConstructible_poly moves to ClassP citing the catalog's public generator. The maintainer's statements and the Codex fill's proofs. Replay 43/43, seals pass, no sweep flag, no new copy pairs.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate166-ram-bridge-bundle.md` | the bundle to attach: 28 sections (one per file, in `BUNDLE-FILES.txt` order), 2658850 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `9270a304536ed177e80f94d4ff9d7b1db0ad7dd6eb2d0c656634ac1aa57300e1`
- **Built by** `mkbundle-mixed.py`: the Lean files from `36fd655a964f319877856bbc0fb787ffc217d4ef`, everything else from the
  campaign commit `f053e735dbf247fb8bb4f121bc7cc457481acc10`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `28 segments, 0 problems`.
- **Export:** only the 28 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate166-ram-bridge-findings.md` as an attachment in chat; committed as `campaign/gates/166-ram-bridge/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
