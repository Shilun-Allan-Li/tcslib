# r4-design

Claude cloud worker: read-only design and sizing pass for closeout wave R4 (the SAT/Hardness duplication families). Read the first bundle section, `campaign/closeout/r4-design-request/brief.md`. This is not a fill: push `r4-design.md` to `arora-barak-ch3-4/inbox/r4-design/` on this exchange branch, after `git pull --rebase` and without force, and summarize it in your final reply.

| File | What |
|---|---|
| `r4-design-bundle.md` | the bundle: 15 sections (one per file, in `BUNDLE-FILES.txt` order), 1335325 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `maintainer-inventory-R4.json` | optional cross-check: the maintainer's grep-based inventory of the R4 families at the same tree (members, use sites, sizes). Unaudited: verify anything you rely on against the bundled sources; disagreements are worth reporting. |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `d8da8a458f3d32819b89ed13e131cc44fc1d20c60a92db3528fe7d18b3c6877a`
- **Built by** `mkbundle-mixed.py`: the Lean files from `68cba664c2fcb4e33b4845b385feea3f456d0105`, everything else from the
  campaign commit `4211cada2629964a495dc64a0f72ce83dddf1f23`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `15 segments, 0 problems`.
- **Delivery:** `r4-design.md` pushed to `arora-barak-ch3-4/inbox/r4-design/` by the worker, summarized in its final reply; recorded under `campaign/closeout/r4-design-request/delivery/`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
