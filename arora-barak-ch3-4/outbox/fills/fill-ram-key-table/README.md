# fill-ram-key-table

RAM fill, tier 2 job B (Codex): prove the 2 rows of `Build/KeyTable.lean` (keyed lookup and assignment). One of five tier 2 jobs that run in parallel on the same base, each proved modulo the others' statements. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` (with its tier 2 addendum) and `fill-ram-key-table.md`.

| File | What |
|---|---|
| `fill-ram-key-table-bundle.md` | the bundle to attach: 19 sections (one per file, in `BUNDLE-FILES.txt` order), 934790 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `14de9a4a1ba6ca97c0508bacb0fbef22843cf29341c63a59fd34b5844abef26f`
- **Built by** `mkbundle-mixed.py`: the Lean files from `cb44316a22c258628bf571da8c84b72c347ee493`, everything else from the
  campaign commit `cb44316a22c258628bf571da8c84b72c347ee493`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `19 segments, 0 problems`.
- **Export:** only the 19 listed paths, from the same two commits.
- **Delivery:** `fill-ram-key-table.zip` (REPORT.md, the delivered owned files and any new files, the patch against the base, check logs), with any `fill-ram-key-table-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-key-table/` on this exchange branch (pull --rebase, no force); the maintainer lands it by PR into `complexity/ram-simulation`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
