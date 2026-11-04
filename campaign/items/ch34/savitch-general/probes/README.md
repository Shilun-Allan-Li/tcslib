# Probes of the deepening design (2026-11-04)

Elaborated with `tools/leanelab.sh` in a worktree at `origin/complexity/arora-barak-ch3-4`
(`ccee2258`, Lean of `711f5444`) against `oleans-leqc3`.

| Probe | Output | Result |
|---|---|---|
| `EmbedProbe.lean.txt` | `EmbedProbe.out` (empty) | 0 diagnostics: `Ins.embed`, `Ext`, `astep_embed`, `preS_embed`, `AHalt.embed` proved; the fit example embeds `outerU_run` with decider `2` rerouted to `4` |
| `NoValProbe.lean.txt` | `NoValProbe.out` | 0 errors: `A_noVal` proved by `cases` on the table (4 linter warnings: the `first` fallbacks never run) |

The probes unfold `astep`, `arun`, `PreS` and `AHalt` freely. They are records, not library
code. The landed lemmas sit beside those definitions (design §1).
