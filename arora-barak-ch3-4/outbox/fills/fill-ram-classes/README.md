# fill-ram-classes

RAM fill, tier 3 (Codex): prove the 9 class corollaries of `TCSlib/Complexity/RAMSimulation/Classes.lean` (DTIME, P, SPACE, L, log-space transducers, Savitch's shape, NSPACE, NL) from stage 2's simulation theorems, based on PR #371's head (branch `ram/fills-0-1`), which has the readers and tiers 0 and 1. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` and `fill-ram-classes.md`.

| File | What |
|---|---|
| `fill-ram-classes-bundle.md` | the bundle to attach: 18 sections (one per file, in `BUNDLE-FILES.txt` order), 281058 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `cc841a4b67c8d668753ea060c1a647013738906983c5cbd691024ac4ec228b9b`
- **Built by** `mkbundle-mixed.py`: the Lean files from `24aa40503e183a6de58b67dc4d3f7aea08d670b5`, everything else from the
  campaign commit `883f3cda2200a8d26e54ba37f8c6cb84f65bdde1`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `18 segments, 0 problems`.
- **Export:** only the 18 listed paths, from the same two commits.
- **Delivery:** `fill-ram-classes.zip` (REPORT.md, the delivered `Classes.lean`, the patch against the base, check logs), with any `fill-ram-classes-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-classes/` on this exchange branch (pull --rebase, no force); the maintainer lands it by PR into `complexity/ram-simulation` after #370 and #371 merge.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
