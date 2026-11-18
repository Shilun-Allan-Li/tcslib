# fill-ram-run

RAM fill, tier 2 job E (Codex): prove `WordRAM.exists_simulation` and `WordRAM.exists_ndSimulation` (`RAMSimulation/Simulation.lean`, with new `Sim/Run*` files). One of five tier 2 jobs that run in parallel on the same base, each proved modulo the others' statements. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` (with its tier 2 addendum) and `fill-ram-run.md`.

| File | What |
|---|---|
| `fill-ram-run-bundle.md` | the bundle to attach: 25 sections (one per file, in `BUNDLE-FILES.txt` order), 639572 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `ef30f5b89e0ae78a44b28e888a4a5a7f68f9e3fef18c1ca73fda78576ade7e32`
- **Built by** `mkbundle-mixed.py`: the Lean files from `cb44316a22c258628bf571da8c84b72c347ee493`, everything else from the
  campaign commit `cb44316a22c258628bf571da8c84b72c347ee493`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `25 segments, 0 problems`.
- **Export:** only the 25 listed paths, from the same two commits.
- **Delivery:** `fill-ram-run.zip` (REPORT.md, the delivered owned files and any new files, the patch against the base, check logs), with any `fill-ram-run-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-run/` on this exchange branch (pull --rebase, no force); the maintainer lands it by PR into `complexity/ram-simulation`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
