# fill-ram-tmproc

RAM bridge fill, job G (Codex): prove `Light.exists_tmProc` (`TCSlib/Programs/Light/TMProc.lean`, PR #382): a Light procedure that runs any finite binary Turing machine on a bit string in memory, in time linear in its running time. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` (with its tier 2 addendum) and `fill-ram-tmproc.md`.

| File | What |
|---|---|
| `fill-ram-tmproc-bundle.md` | the bundle to attach: 20 sections (one per file, in `BUNDLE-FILES.txt` order), 270445 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `1c4387c89fa8ec76770c2200050077eea0598c6a1e765ac0d266c0092d90ee57`
- **Built by** `mkbundle-mixed.py`: the Lean files from `0de483083650950569a96b0a3da4fb3f2103e997`, everything else from the
  campaign commit `3fc27517af938fec0b3e0f53f85766a5e81f82e6`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `20 segments, 0 problems`.
- **Export:** only the 20 listed paths, from the same two commits.
- **Delivery:** `fill-ram-tmproc.zip` (REPORT.md, the delivered owned file, the patch against the base, check logs), with any `fill-ram-tmproc-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-ram-tmproc/` on this exchange branch (pull --rebase, no force); the maintainer lands it by PR into `complexity/ram-simulation`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
