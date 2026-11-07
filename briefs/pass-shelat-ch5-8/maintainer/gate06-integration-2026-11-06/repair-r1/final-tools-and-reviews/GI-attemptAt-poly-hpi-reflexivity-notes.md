# GI attemptAt_poly: residual dependent equality

**Unapplied, unchecked one-block follow-up.** Only the existing `hπ` proof inside `GIZK.attemptAt_poly` is changed: append `rfl` after the existing public-reader simplification. No new tactic block, owner reader, hypothesis, algorithm, admission, declaration header or other proof text changes.

Source: `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean` in the explicit Gate06 worktree `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.

- Input snapshot and current source SHA-256: `52814b1b7d7d0a1ce7e2e23965d02faadb019a2c7c65478e25c0695079281ea7`.
- Proposed complete source SHA-256: `d5f0e128d5530c8c1ec36c71142f9f167139d6287b0eea8b9d83795d24065920`.
- Separate patch SHA-256: `c3f79555a3b7b30ba1ed89057b2aff0dd189f6dd79e9a79bc4984766c0bebb15`.

The input is the main-records R2 diagnostic archive's `diagnostic-evidence/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R3_Simulator/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R3_Simulator.original.source.txt`, verified byte-identical to current Gate06 source before proposal generation. It already includes the earlier attemptAt public-reader proposal; this follow-up does not apply directly to the old frozen e9 source.

Observed log: that directory's `native/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R3_Simulator.log`, SHA-256 `b26144ebfcb02afb84b6ffc36217dcf0367bdeb0cb95bf4b196e674daf8dc642`.

The remaining changed-proof diagnostic is the `hπ` block beginning at original source 312 / probe 362. After public `instanceVertexCount_eq`, `samplePerm_eq` and `decGraph_fst` equations, log lines 1113–1132 print the same explicit permutation-sampling expression on the two sides of the residual equality. The implicit dependent arguments are not printed. Appending `rfl` asks Lean's definitional equality checker to close that residual equality after the public equations have exposed the imported interfaces. It adds no explicit foreign unfolding; the seal remains installed.

Identical pretty-printed sides alone do not establish definitional equality of hidden arguments. This minimal reflexivity step is a proposal for root's native isolation/check, not a claim the cause or success has been proved. If it fails, inspect that same residual goal with explicit/fully printed arguments under the unchanged seal before adding a broader proof. No broader simp set or weakened statement is proposed.

The other four diagnostic declarations (`decGraphAt_padSq`, the local `decGraph_eq_of_sqrt`, `sim_poly`, `exists_simulator`) remain unchanged and are not declared passing. The diagnostic label is explicitly old-collector/nonfinal coverage; this note makes no final collector or module-pass claim. The mathematical sketch stays accurate. Static checks show the tactic-block and admission counts unchanged.

No library edits, native tools, Lean/cache/build commands, apps or Git mutations occurred. Only the separate ignored patch and notes were saved. Final native runner preparation continues separately.

**Not yet clear to merge — the residual reflexivity step is unapplied and requires root's serial sealed check.**
