# 167-prog2-statements-r3-gate

The Codex re-audit for (a5) PROG-2 (gate 167, round 3) on the RAM work branch: the statement mirror of Light with string input and output and coins, revised for round 2's HOLD (0/1/3): StartUp in the compiler edit set, complete readers, the fixed footprint carried by the simulation contract, and the remaining sanity checks. No Lean PR; the mirror elaborates with 0 errors.
Read pack-r3.md (after the standards), then findings-r2.md and resolutions-r3.md. Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate167-prog2-statements-r3-bundle.md` | the bundle to attach: 34 sections (one per file, in `BUNDLE-FILES.txt` order), 630602 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `b2579ed557d275fc886a690d30f573c99128578d0a1c50135269cc895a7fb72b`
- **Built by** `mkbundle-mixed.py`: the Lean files from `b295a77f316cd6c564ad0402ece64bf0b422572e`, everything else from the
  campaign commit `b295a77f316cd6c564ad0402ece64bf0b422572e`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `34 segments, 0 problems`.
- **Export:** only the 34 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate167-prog2-statements-r3-findings.md` as an attachment in chat; committed as `campaign/gates/167-prog2-statements/findings-r3.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
