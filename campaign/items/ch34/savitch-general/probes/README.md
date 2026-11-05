# Probes of the deepening design (2026-11-04)

Elaborated with `tools/leanelab.sh` in a worktree at `origin/complexity/arora-barak-ch3-4`
(`ccee2258`, Lean of `711f5444`) against `oleans-leqc3`.

| Probe | Output | Result |
|---|---|---|
| `EmbedProbe.lean.txt` | `EmbedProbe.out` (empty) | 0 diagnostics: `Ins.embed`, `Ext`, `astep_embed`, `preS_embed`, `AHalt.embed` proved; the fit example embeds `outerU_run` with decider `2` rerouted to `4` |
| `NoValProbe.lean.txt` | `NoValProbe.out` | 0 errors: `A_noVal` proved by `cases` on the table (4 linter warnings: the `first` fallbacks never run) |

The probes unfold `astep`, `arun`, `PreS` and `AHalt` freely. They are records, not library
code. The landed lemmas sit beside those definitions (design §1).

## The pre-ship on the merged tree (2026-11-05)

Elaborated with `leanelab.sh` in the records worktree at the campaign tip, against `oleans-led4`
(the campaign's Lean after #188 and #189; #190 changed nothing these probes import).

| Probe | Output | Result |
|---|---|---|
| `DeepenRoute-merged.lean.txt` | `DeepenRoute-merged.out` | §8's route probe, unchanged: its four `sorry` warnings |
| `WindowRoute.lean.txt` | `WindowRoute.out` | `noEdge_of_lt` and `mem_iff_reach_of_noEdge` (without `hcb`) proved from published lemmas and six API stand-ins; two `sorry` warnings, the two non-equation stand-ins |
| `window-seal/` | `*.out` | the route sealed over 24 definitions: the same two warnings. Controls: sealed 0 of 48 pass; unsealed 46 of 48 (the two recursive definitions' delta goals fail, as expected) |
| `WindowApi.lean.txt` | `WindowApi.out` (empty) | 0 diagnostics: `Cfg.InWindow.apply_of_lt`, `walkLe_zero_iff`, `walkLe_succ_iff` and `reach_of_reflTransGen` (sealed over `WalkLe` and `Reach`) |
