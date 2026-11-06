# 99-zone-data-eq-api-gate

Gate 99: the API gate of the zone data maps as whole values, PR #207, at `f866f31438630016f8c733dcc452345eddda6b27` (G5's brief review's blocker; the user's ruling of 2026-11-06: publish).
The pack is `campaign/gates/99-zone-data-eq-api/pack.md`, the bundle's first section.

| File | What |
|---|---|
| `99-zone-data-eq-api-bundle.md` | the bundle to attach: 36 sections (one per file, in `BUNDLE-FILES.txt` order), 3005487 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `44c0b904bfec182e69c504f5a4ba5e3ecf75a63182e4c12c41e8064a189aa2a2`
- **Built by** `mkbundle-mixed.py`: the Lean files from `f866f31438630016f8c733dcc452345eddda6b27`, everything else from the
  campaign commit `66f40de528bc43fbd92cefad2042459293cd8520`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `36 segments, 0 problems`.
- **Findings:** the auditor pushes `zone-data-eq-api-findings.md` to `arora-barak-ch3-4/inbox/` on this branch (pull with rebase first, add only that file, never force-push, no PR) and pastes it in its reply; committed as `campaign/gates/99-zone-data-eq-api/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
