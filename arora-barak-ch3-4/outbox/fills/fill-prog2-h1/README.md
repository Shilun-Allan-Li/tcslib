# fill-prog2-h1

PROG-2 fill H1 (Codex): add input, output and coins to the Light language core in place. `Light.Stmt` gains `inBit`, `emit`, `coin` and `half`; `Light.Exec` gains the output and coin indices; a new `Light/IO.lean` holds the stream-aware logic (`EndsIO`, `MeetsIO`, determinism, lifting of I/O-free code). The signatures are frozen by gate 167's mirror; the compiler's four new cases stay as disclosed admissions until H2. Read the first two bundle sections, `campaign/items/ram-tm/briefs/COMMON.md` and `fill-prog2-h1.md`.

| File | What |
|---|---|
| `fill-prog2-h1-bundle.md` | the bundle to attach: 46 sections (one per file, in `BUNDLE-FILES.txt` order), 686002 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `85264595a5ec372a3f83937cf5a428bbd47ddd0540a678911588b5d06c77197d`
- **Built by** `mkbundle-mixed.py`: the Lean files from `3bc2d5f34c0a9c9d67ff89dd1e2e0bd68e3805b7`, everything else from the
  campaign commit `3bc2d5f34c0a9c9d67ff89dd1e2e0bd68e3805b7`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `46 segments, 0 problems`.
- **Delivery:** `fill-prog2-h1.zip` (REPORT.md, the delivered owned files, the patch against the base, check logs), with any `fill-prog2-h1-checkpoint-N.zip`, pushed to `arora-barak-ch3-4/inbox/fill-prog2-h1/` on this exchange branch (pull --rebase, no force); the maintainer lands it as a PR into `complexity/ram-simulation`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
