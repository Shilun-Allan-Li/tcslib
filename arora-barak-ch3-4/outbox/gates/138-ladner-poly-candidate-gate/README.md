# 138-ladner-poly-candidate-gate

The first Codex audit for draft PR #320 (gate 138): Ladner fill 3, the polynomial-time candidate test (target 1, part A), with the maintainer's in-file dedup repair.
Read pack.md (after the standards). Return the findings Markdown in chat.

| File | What |
|---|---|
| `138-ladner-poly-candidate-bundle.md` | the bundle to attach: 17 sections (one per file, in `BUNDLE-FILES.txt` order), 1868828 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `15c42ff3569cc41846c2ed4a74720f83ac6d9143f037bacf68660a4551c68408`
- **Built by** `mkbundle-mixed.py`: the Lean files from `fc72e67b25e79231fbb04a324d9978d9e9f00349`, everything else from the
  campaign commit `9a356d16d5e2b29e48816037603789b2553fba03`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `17 segments, 0 problems`.
- **Findings:** the auditor delivers `gate138-ladner-poly-candidate-findings.md` as an attachment in chat; committed as `campaign/gates/138-ladner-poly-candidate/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
