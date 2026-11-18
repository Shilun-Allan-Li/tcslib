# fill-ram-bridge

RAM bridge fill, job F (Codex): prove the four statements of PR #379 (polynomial word sizes in `RAMSimulation/WordSize.lean`; polynomial-time functions from word-RAM programs in `RAMSimulation/Classes.lean`). Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` (with its tier 2 addendum) and `fill-ram-bridge.md`.

| File | What |
|---|---|
| `fill-ram-bridge-bundle.md` | the bundle to attach: 15 sections (one per file, in `BUNDLE-FILES.txt` order), 284839 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `7d780c7b4e76b1b965bbbe46b61e143b72efcf6bcbaa976476daabc7b1f74481`
- **Built by** `mkbundle-mixed.py`: the Lean files from `e5fe99819b8ceb11f43894964630a594eb61ff0a`, everything else from the
  campaign commit `56d101eccd731eb9e2ef14e3241fc8e1949d6c8e`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `15 segments, 0 problems`.
- **Export:** only the 15 listed paths, from the same two commits.
- **Delivery:** `fill-ram-bridge.zip` (REPORT.md, the delivered owned files, the patch against the base, check logs), with any `fill-ram-bridge-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-bridge/` on this exchange branch (pull --rebase, no force); the maintainer lands it by PR into `complexity/ram-simulation`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
