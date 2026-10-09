# RB3 retrofit report

Base: `5588628cbbddea9546f616907364b608e15557fd`.
Working branch: `fill/retrofit-rb3`, branched directly from
`complexity/arora-barak-ch3-4`; never rebased, pushed, or submitted as a PR.
The brief's issue commit is `ff012d28ca3131452161669e1d7efe389b75ba2e`;
`Hardness.lean` is byte-identical between that commit and the recorded base.

## Scope and import change

Only `TCSlib/Complexity/CookLevin/Hardness.lean` is modified in Git.
The five public theorems, including their docstrings and complete proof
bodies, are frozen byte-for-byte. Remaining private signatures and
non-exempt docstrings are also frozen.

**Sanctioned import change (Task 3):**
`import TCSlib.Complexity.TuringMachine.Build.Seam`.
This makes Hardness the first proof consumer of the §12 seam layer outside
`Build/`, as commissioned. No other import is changed.

## Task 1

Done: 6/6 deletions, with no unexpectedly live referencer and no escalation.
Commit: `b347d72c5aa3c791896e7f3d6b93f478bc692c46`.

The six prescribed deletion targets are `clRefClockTM`, `clRefClockCfg`,
`clCount_first`, `clRefCountTM`, `clRefCount_first`, and `clReadFields`.
Their own docstrings are deleted with them. The permitted replacement
`clCount_width` docstring is:

```lean
/-- A counter below `2^w` occupies at most `w` bits. Together with the
counter runtime bound, this charges one administrative increment by two
binary scans plus two transitions, with no unary-position representation. -/
```

## Task 2

Done: all three swaps and all 13 use sites verified; no escalation.
Commit: `5ec0ac6449f85a93d99e2b3ed196f4384c0c6893`.

`clCompute_comp` is deleted. Its two callers directly use
`FinTM.bufferedCompTM_computesInTime`, `output_length_le`, and runtime
monotonicity, preserving the existing time bounds.

`clBuffer_append_bit` is deleted; `clCopy_write` uses
`(FinTM.bufferTape_append record b).symm`.

`clA5_pt_unaryLength` is deleted; all ten uses become
`(clNative_fill true).comp ...`.

| Removed helper | Caller | Base use line | Final use line |
|---|---|---:|---:|
| `clBuffer_append_bit` | `clCopy_write` | 1757 | 1636 |
| `clCompute_comp` | `clQueryCode_machine` | 5160 | 4984 |
| `clCompute_comp` | `clNative_image` | 5314 | 5145 |
| `clA5_pt_unaryLength` | `clA5Drop_native` | 7012 | 6833 |
| `clA5_pt_unaryLength` | `clA5Field_native` | 7080 | 6901 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native` (header field) | 7191 | 7012 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native` (header tail) | 7192 | 7013 |
| `clA5_pt_unaryLength` | `clA5Next_native` | 7208 | 7029 |
| `clA5_pt_unaryLength` | `clA5Sizes_native` (header field) | 7749 | 7570 |
| `clA5_pt_unaryLength` | `clA5Sizes_native` (header tail) | 7750 | 7571 |
| `clA5_pt_unaryLength` | `clA5Cursor_native` | 8112 | 7933 |
| `clA5_pt_unaryLength` | `clA5Indices_native` | 8134 | 7955 |
| `clA5_pt_unaryLength` | `clA5Fragment_native` | 8211 | 8032 |

## Task 3

Done: the general-configuration seam citation elaborates directly; no escalation.
Commit: `9f58177bf2c75e5adfc8d5e7cbcee3179b361622`.

The new `clFreshTM` definition is:

```lean
private def clFreshTM : FinTM Bool where
  k := 2
  State := (Fin 3) ⊕ clReadTM.State
  tm := seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)
```

`clFresh_run` obtains the reset's first-return cut from `clWipe_first`,
then directly cites `seamCompTM_run_ofCfg` with `clRead_run` at the empty
target. The phase-two configuration is definitionally the reset's returned
configuration with only its control state replaced. The exact composite
duration is `a + 1 + (3 * w.length + 3)`, bounded by
`2 * old.length + 3 * w.length + 6` using the existing bound on `a`.
The citation in the proof is:

```lean
  exact seamCompTM_run_ofCfg clWipeTM.tm (2 : Fin 3) clReadTM.tm (.inl none)
    he rfl hf (clRead_run x p pre w tail [] (by simp))
```

The displaced stream head and all other configuration fields cross the
seam intact. No new glue declarations are needed. `clFresh_idle` and
`clFresh_first` remain byte-identical.

## Duplication and size

Duplication ledger: **new copies: none**.
New private declarations: **none**.
This is a deletion/citation retrofit; inherited unrelated duplication remains
outside the owned task list.

Before: 8,904 lines, 553 private declarations, five public declarations.
After: 8,725 lines, 544 private declarations, five public declarations.
Net reduction: 179 lines and nine private declarations.
The remaining size warning is covered by the recorded retrofit/12.2c program
in `backlog.md` §2, `AroraBarakChapters3-4Plan.md` §4d, and
`machine-library-design.md` §12. No uncommissioned file split was attempted.

## Verification and environment

Lean 4.25.0, release commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`;
mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
No `lake build` command was run.

The container needed a process-executable-path compatibility shim to locate
the Lean installation (`environment/self_exe.c`, outside the repository).
The required `lake exe cache get` was attempted; its native compiler exited
135. The same pinned cache downloader succeeded through
`lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`, restricted
to the 32 external imports needed by the complete bootstrap closure (969
cached modules). `TAR_OPTIONS=--no-same-owner` handles archive ownership in
this container. These are environment adjustments, not Lean-source changes.

The initial bootstrap process ended during Hardness without a completion
status or fresh olean. It was not counted as a pass. The first 50 successful
checks were retained, and the sweep resumed at module 51 with `lean -j 1`;
subsequent retrofit checks use a bounded two-worker setting (`lean -j 2`). The
combined bootstrap log records only completed checks plus the resumed run.

An uncommitted Task 2 attempt reported one `omega` elaboration failure:
the inferred polynomial runtime still contained a beta-redex. Adding
`dsimp only` before that arithmetic step resolves it; the exact replacement
proof also passes an isolated Lean check. The failed attempt is retained in
`logs/task2-attempt1.log` and was never committed. Every committed state
passes the full zero-error, zero-sorry gate.

The prescribed 65-module order list omits six dependencies now imported by
its facades. To complete the fresh bootstrap, the unchanged `Build/Embed`,
`Build/Seam`, `Build/Catalog`, and `NDCodes` modules are checked before the
TuringMachine facade, and unchanged `QBF` and `QBFEncoding` before the
Formulas facade. Task 3's `Build.Seam` is therefore fresh before use.

All 65 listed modules and the six omitted dependencies passed with fresh
oleans. The bootstrap's only admission warnings are four inherited
out-of-scope admissions: one each in `CounterProgRun`, `NDCodes`, `QBF`,
and `QBFEncoding`; none is in Hardness's import closure. Hardness itself
passed at baseline, immediately before each of the three commits, and in
the final ordered Hardness → CookLevin-facade sweep. Each of those successful
gates has zero errors and zero sorry warnings. Each compiler check removed the old olean
first. After each commit, the committed source, worktree source, and fresh
olean were hash-compared against the pre-commit checked state; the post-commit
logs attest that the commit changed none of those checked bytes. The last
post-commit state is additionally compiled afresh in the final sweep.

The five public axiom prints are byte-identical to the baseline and are
within the permitted axiom triple. The final source-scope verifier passes:
exactly nine deletions, no new declarations, exactly the authorized changed
blocks, frozen public blocks and retained private signatures/docstrings,
and only the sanctioned import addition. Style lint: **0 FAIL, 1 WARN**
(the recorded file-size warning).

Final sweep tail:

```text
PASS Hardness: exit 0, fresh olean, zero errors, zero sorry warnings.
PASS CookLevin facade: exit 0, fresh olean, zero errors, zero sorry warnings.
```

Final axiom prints:

```text
'Complexity.NPHard.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Commit gates:

| Task | Commit | Before | After |
|---|---|---|---|
| 1 | `b347d72c5aa3c791896e7f3d6b93f478bc692c46` | `logs/task1-precommit.log`: PASS | `logs/task1-postcommit.log`: PASS |
| 2 | `5ec0ac6449f85a93d99e2b3ed196f4384c0c6893` | `logs/task2-precommit.log`: PASS | `logs/task2-postcommit.log`: PASS |
| 3 | `9f58177bf2c75e5adfc8d5e7cbcee3179b361622` | `logs/task3-precommit.log`: PASS | `logs/task3-postcommit.log`: PASS |


## Delivery

The archive contains this report, the full modified source at its repository
path, the three-commit format-patch series, an incremental Git bundle against
the recorded base, verification logs, and `SHA256SUMS` covering every other
payload file. Apply patches in filename order from the recorded base.
