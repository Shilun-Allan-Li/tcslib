# B5a, the uniform simulator: the pre-ship on the tree after #169 (maintainer, 2026-10-27)

Tree: #169's merged head `9d0af8cb` (the campaign tip after #168 with A+ merged in); the olean
snapshot is `oleans-laplusm`, #169's replay. Once #169 merges with no other Lean change, the
campaign's tree equals this one, so these figures are the issue base's. **#169 merged
(2026-10-27, `94296486`), with the TCSlib tree equal to `9d0af8cb`'s (checked).** Re-check the
equality at issue if any later Lean lands. The draft is the rewrite against the interpreter startup
(`../../b5a-fill-unisim.DRAFT.md`, 2026-10-27), with **the two imports** of region (a)
(`Nondeterministic`, `Build/InterpreterStartup`), whose closure contains the earlier six. Lean ran
through `tools/leanelab.sh` against `oleans-laplusm`, one elaboration at a time, in a worktree at
`9d0af8cb` (`wt-b5aps`, no tracked change). Each `.out` is raw with paths stripped; its last line
gives the exit status, the time and the peak memory. The probes are `../preship-a524c36f/`'s and
`../preship-junction/`'s with the six import lines replaced by the two; the import probe is
extended (below).

| Check | Result | File |
|---|---|---|
| Owned file, base | `CodeSimulator` (8,666 lines; 12 public, 185 private; blob `733a9a46`, unchanged): exactly the stub's sorry warning (8654); 24.7 s, 2.50 GB | `elab-CodeSimulator-base.out` |
| Owned file, overlay | the two imports after line 15: exactly the stub's warning (8656); 18.8 s, 2.46 GB | `CodeSimulatorOverlay.*` |
| Imports | no cycle (neither import's closure contains `CodeSimulator`); with every module downstream of `CodeSimulator` they import together with no clash: 0 diagnostics | `ImportClashProbe.*` |
| Order list | **120 modules** on the overlay, 41 Mathlib roots: the base's set, in the overlay's topological order (the startup's module and its closure before `CodeSimulator`) | `order.txt`, `roots.txt` |
| Base sorries | **26 declarations in 12 modules**, the same on the overlay; since `a524c36f`, #165 proved `ZoneRebalance`'s two and #168 `UniversalK`'s two | `base-sorries.txt` |
| Import probe | **199 checks of 199 names**, 0 errors, 0 warnings: `a524c36f`'s 157, `Turing.exists_interpreterStartup`, and the junction probe's source-level names not already there (12 TCSlib, 29 core and Mathlib). 29 axiom prints (27 within the standard three, 2 with none) | `B5aUSImportProbe.*` |
| Route probe | `b5a_install`, `b5a_locality`, `b5a_accepts_take`, `b5a_verdict`, `b5a_table_le`, sealed over 12: 0 diagnostics; 5 prints within the standard three | `B5aUSRouteProbe.*` |
| Junction probe | the overlay with the verdict and junction blocks before `end MachineFormat` (sealed over 4 and 20): only the target's sorry warning (8656); `b5a_window_verdict`, `b5a_bank`, `b5a_junction`, `b5a_tail`, `b5a_start`, `b5a_run` within the standard three; 21.4 s, 2.44 GB | `B5aJunctionProbe.*` |
| Seal controls | `B5aUSSealControl` (18 goals, the route and verdict probes' seals) and `B5aJunctionSealControl` (20, the junction's): unsealed all close; sealed all 18 and all 20 fail, each at its own goal (lines 103–173 and 107–183) | `B5aUSSealControl.*`, `B5aJunctionSealControl.*` |
| Lint | `TuringMachine`: 0 FAIL, 68 WARN over 84 files (`CodeSimulator`'s are its size and check 8: `MachineFormat.toFinTM`, `codeSkipTableK`, `oneTapeMachineFormat`). `Diagonalization`: 0 FAIL, 2 WARN over 5 files | `lint-*.txt` |
| Screen base | ⟨pending⟩ | `screen-base.*`, `screen-population.txt` |

**Dropped from `a524c36f`'s set:** the start probe and its 9 controls (the junction probe's
`b5a_start` replaces them: the restart's initial configuration as the startup's blank start), and
the home probes (the junction probe is in-module; the fill's home is unchanged, the blank line
before `end StepBlockClients`).
