# fill-ram-phases-r3

Tier 2 job D, round 3 (Codex): repair the duplication gate 170 found in your phase proofs (PR #386). Cite the published Segment.trans and Segment.zero instead of re-deriving them, and unify PhaseBlock and PhaseBranch into one certificate over a finite exit family. Statements unchanged; no admission allowed. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` (with its tier 2 addendum) and `fill-ram-phases-r3.md`.

| File | What |
|---|---|
| `fill-ram-phases-r3-bundle.md` | the bundle to attach: 37 sections (one per file, in `BUNDLE-FILES.txt` order), 465660 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `ec5e73b93a79ebabb8bf52d6e887733a8c3c58c1916b486fcf2c54115ce64ffc`
- **Built by** `mkbundle-mixed.py`: the Lean files from `59c7b4be4a3d22b64e390ebc8b9b141ef7786c29`, everything else from the
  campaign commit `818d9cb29785ccf96935a74b863ced04a35c23fd`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `37 segments, 0 problems`.
- **Export:** only the 37 listed paths, from the same two commits.
- **Delivery:** `fill-ram-phases-r3.zip` (REPORT.md, the delivered owned files, the patch against the base, check logs), with any `fill-ram-phases-r3-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-phases/` on this exchange branch (pull --rebase, no force); the maintainer lands it on PR #386.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
