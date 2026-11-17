# fill-ram-steps

RAM fill, tier 0 (Codex): prove the 18 admissions of `TCSlib/Programs/WordRAM/Extended.lean` (the extended word RAM's run calculus: runs, footprints and halting within steps and cells), based on PR #370's head (branch `ram/readers`), which adds the vendored readers it needs. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` and `fill-ram-steps.md`.

| File | What |
|---|---|
| `fill-ram-steps-bundle.md` | the bundle to attach: 13 sections (one per file, in `BUNDLE-FILES.txt` order), 161658 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `5625e8f27fe1c325550231c6482c72611db0fa2f03ab638b97c848256813423c`
- **Built by** `mkbundle-mixed.py`: the Lean files from `25040f435bba85ad563d5c1f1ceb42744aefc3eb`, everything else from the
  campaign commit `54aaf9c0522b33dfa47b7d36c09697eb4a4953e7`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `13 segments, 0 problems`.
- **Export:** only the 13 listed paths, from the same two commits.
- **Delivery:** `fill-ram-steps.zip` (REPORT.md, the delivered `Extended.lean`, the patch against the base, check logs), with any `fill-ram-steps-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-steps/` on this exchange branch (pull --rebase, no force); the maintainer lands it by PR into `complexity/ram-simulation` after #370 merges.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
