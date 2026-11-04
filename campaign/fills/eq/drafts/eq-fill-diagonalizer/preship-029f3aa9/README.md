# E-D's pre-ship at #176's merged head (maintainer, 2026-11-04)

Worktree `wt-edps` at `029f3aa92970159c40f5d12e7fdc47c03c6cd61a` (#176, `lean/eq-cont1-landing`,
with the campaign merged in; its Lean is the campaign's tree after #176 merges), against
`oleans-lscp3`, the snapshot of the campaign after #175, whose modules are the file's upstream.
The probes import `NTimeDiagonalizer`, whose `.olean` there is the campaign's (E-Q's first landing);
every name they read from it is unchanged by #176. They are re-run against `oleans-leqc2` (#176's
replay) at the issue. Lean through `tools/leanelab.sh`, one at a time.

| Step | File | Result |
|---|---|---|
| overlay | `NTimeDiagonalizerOverlay.lean.txt` (the three imports after `Build/WordTests`) | exit 0; one warning, `exists_diagonalizer`'s sorry (line 5409 = 5406 + 3); 14.4 s, 2.37 GB |
| import | `EDImportProbe.lean.txt` | 59 checks, exit 0, 0 errors, 0 warnings |
| route | `EDRouteProbe.lean.txt` (sealed over 11 definitions, four `@[simp]` erased) | exit 0; 12 lemmas: 8 on `[propext, Classical.choice, Quot.sound]`, 4 on `[propext, Quot.sound]` |
| controls | `EDSealControl_unsealed/_sealed.lean.txt` (17: 11 `rfl`, 2 `eqn`, 4 `simp`) | unsealed 15 pass (the recursive `ladder` and `NDTM.runWith` delta goals fail, their `eqn` controls pass); sealed 17 fail |
| dup | `EDDupProbe.lean.txt` (9 `exact?`) | closes 2: `length_bits_le_self`, `counterValue_bits`; 7 errors by design (exit 1) |
| order | `fillinputs.py` at the local overlay commit `dcd8cb87` | 84 modules, 34 roots, 19 sorried declarations in 9 modules |
| lint | `lint-base-Diagonalization.txt`, `style-lint-base.txt` | `Diagonalization` 0 FAIL, 3 WARN over 5 files; `style_lint` on the file: its size only |
| screen | `screen-population.txt` (38 files), at the overlay commit `dcd8cb87`, clean | 2,241 declarations, 2,439 pairs, 858,015 characters; `NTimeDiagonalizer` in 133 pairs; 1,651 s, 3.27 GB (`../screen-base.txt`) |
