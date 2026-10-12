# Regenerating `TCSlib/Programs/` from [AFM26]

`TCSlib/Programs/` (all but `Compat.lean` and the facades) is generated from
anthropics/formal-math, folder `3sum-apsp`, commit `e1a4e6508154ea59f030480661590a9fe3018011`.
Every change to the upstream text is made by these scripts and listed in each file's header. That
way the port can be regenerated, and audited by reading the diff
(`audits/evidence/programs-vendor/upstream-to-vendored.diff`).

| Script | What it does |
|---|---|
| `topo.py <upstream root> <module>...` | prints the upstream modules of the roots' import closure, in dependency order |
| `fixes.py` | the per-module proof repairs for Lean/Mathlib v4.25.0, each with its reason; each applies exactly once |
| `vendor.py <upstream root> fixes.py <worktree> <module>...` | writes the vendored files. It removes the module-system syntax, swaps `with_unfolding_none` for `with_reducible`, applies the repairs, renames the namespaces, remaps the imports, adds the vendoring header, the `## References` section and the standard options, and trims `EndStatement.lean` to the word RAM |
| `facades.py <worktree>` | writes `TCSlib/Programs.lean` and the topic facades |
| `shipcheck.py <worktree> <vendor map> <out>` | concatenates the shipped files into one file for a read-only elaboration with a `sorryAx`/axiom census |
| `closurecheck.py <worktree> <module> <out>` | concatenates exactly one module's import closure, importing only what that closure imports, so a read-only elaboration sees the environment of a real build (the shipcheck's union of imports can mask a missing import; the first replay found one) |
| `evidence.py <upstream root> <worktree> <vendor map> <upstream module list> <evidence dir>` | writes the per-file diff against upstream and the file map |

The roots are `ThreeSumApsp.Lang.Compiler.WholeProgram`, `ThreeSumApsp.Lang.Tactics`,
`ThreeSumApsp.Lang.Regions`, and every module of `ThreeSumApsp/Lang/Lib/` except `Sieve`. The
sieve needs `Nat.primesLE`, which our Mathlib pin lacks; see `backlog.md`. The scripts read
only their arguments, use the Python standard library only, and start no process.
