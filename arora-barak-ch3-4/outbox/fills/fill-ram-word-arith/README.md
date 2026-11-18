# fill-ram-word-arith

RAM fill, tier 2 job A (Codex): prove the 9 admissions of `Build/WordArith.lean` (word arithmetic rows and `bvBits_injective`). One of five tier 2 jobs that run in parallel on the same base, each proved modulo the others' statements. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` (with its tier 2 addendum) and `fill-ram-word-arith.md`.

| File | What |
|---|---|
| `fill-ram-word-arith-bundle.md` | the bundle to attach: 19 sections (one per file, in `BUNDLE-FILES.txt` order), 627993 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `daa96cb0c44083eb9e61a911a4b80791a643f78718b006d9e762d02824366baf`
- **Built by** `mkbundle-mixed.py`: the Lean files from `cb44316a22c258628bf571da8c84b72c347ee493`, everything else from the
  campaign commit `cb44316a22c258628bf571da8c84b72c347ee493`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `19 segments, 0 problems`.
- **Export:** only the 19 listed paths, from the same two commits.
- **Delivery:** `fill-ram-word-arith.zip` (REPORT.md, the delivered owned files and any new files, the patch against the base, check logs), with any `fill-ram-word-arith-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-word-arith/` on this exchange branch (pull --rebase, no force); the maintainer lands it by PR into `complexity/ram-simulation`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
