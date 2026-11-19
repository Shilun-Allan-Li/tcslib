# fill-prog2-h1 — complete

Base: `3bc2d5f34c0a9c9d67ff89dd1e2e0bd68e3805b7` on `complexity/ram-simulation`.
Local implementation head: `b9f239f7546e5ae691aace860a9b87b1676a49c7` (`codex/fill-prog2-h1`), not pushed.
Input bundle SHA-256: `85264595a5ec372a3f83937cf5a428bbd47ddd0540a678911588b5d06c77197d`, checked before reading its first two sections and again before packaging.

All H1 targets are implemented and proved. The only unfinished code is the explicitly authorized compiler frontier for H2: 12 sites in three constants. The compiler still returns `List Instr`.

## Landing and statement freeze

The complete 79-row landing table is [evidence/LANDING.md](evidence/LANDING.md), with the mirror name, in-place name, home and comparison for every target. All 79 elaborated signatures match the renamed mirror (`FrozenStatements.log`, exit 0). The 78 ordinary source headers match after renaming, namespace qualification and whitespace normalization; the limits record keeps the base's three fields and adds exactly `input : List Bool`, in place of the mirror's `extends Limits` wrapper. All 16 remaining frozen definition bodies/equation tables match; theorems have independently checked proofs. `evidence/frozen-signatures.diff` is empty.

`Light/IO.lean` is the 491-line home of the stream logic, silent-code lifting, relocation, stream truncation and permanent checks; `Light/IO/Exec.lean` holds determinism, trace lengths and inversions. `Compiler/WholeProgram` imports `IO`, exporting it through the existing Light facade without editing a non-owned facade. No H2 acceptance definitions, extended instruction types or deliverables were added.

## Forced changes

* `Syntax`: `Stmt` gains `inBit`, `emit`, `coin`, `half`; `Limits` gains `input`; `Exec` gains the output and coin indices, threads them through old rules and adds the four new rules. `inBitVal` and its reader are the frozen definitions.
* `Logic`: `Exec.append` gains both indices. `Ends` keeps its public type and hides `σ' o r c` instead of `σ' c`. Existing rule proofs thread these witnesses; their statements remain unchanged. The new reader is `ends_iff`.
* `Assigns`: the four new defining arms, plus the two indices in `Exec.loc_eq_of_notMem_assigns`. Existing keeping rules only change witness lines.
* `RunsStayInLimits`: both execution lemmas gain the indices; `Exec.bounded` also gains the frozen hypothesis `(1 : ℤ) ≤ lim.word`. Its new cases bound the two bit values and integer halving.
* `Renumber`: four unchanged-statement arms in `Stmt.shift`, indices and four cases in `Exec.shift`; `Ends.shift` only changes witnesses. `Program.behind` is unchanged.
* `Rules`: `Ends.of_blockSafe` gains four impossible cases (the existing default `BlockSafe` arm is false). Sequence/branch/skip inversions thread extra witnesses. No rule statement changes.
* `Calls`: this base already has `meets_iff` from job G, with implicit arguments. H1 explicitly requires the mirror's reader, so it is reconciled to the frozen explicit-argument signature, with identical proposition and `Iff.rfl` proof. `Meets` itself is unchanged. The sole consumer adjustment is the witness-reader line in `TMProc` (`meets_iff ..`); no TMProc statement changes.
* `Compiler/StatementCode`: final frozen size/width arms and four proved width readers; the four `compileStmt` arms and the corresponding four length cases are admitted. Existing code and code type stay in place.
* `Compiler/Simulation`: the two private execution hypotheses gain traces; `sim_seq`, `sim_whileTrue` and `sim` receive the word-bound hypothesis needed by `Exec.bounded`. Only `sim`'s four new cases are admitted.
* `Compiler/WholeProgram.compileProgram_correct`: traces in the execution hypothesis and the forced word-bound hypothesis; the existing proof passes these to boundedness and simulation. It has no admission site of its own.

The static inventory is `evidence/changed-statements.json` (it also counts equation-style bodies as source statements). All other existing signatures are unchanged. No edits were needed in Frames, Regions, Lib or RAMSimulation. Out-of-scope generated blueprint metadata in the working checkout is excluded from both commit and delivery.

## Admission sites and walks

| Site | Authorized new case |
|---|---|
| `TCSlib/Programs/Light/Compiler/Simulation.lean:498` | `| inBit hs => sorry` |
| `TCSlib/Programs/Light/Compiler/Simulation.lean:499` | `| emit hs => sorry` |
| `TCSlib/Programs/Light/Compiler/Simulation.lean:500` | `| coin b => sorry` |
| `TCSlib/Programs/Light/Compiler/Simulation.lean:501` | `| half hs => sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:237` | `| .inBit _ _, _ => by sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:238` | `| .emit _, _ => by sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:239` | `| .coin _, _ => by sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:240` | `| .half _ _, _ => by sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:308` | `| inBit x e => sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:309` | `| emit e => sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:310` | `| coin x => sorry` |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean:311` | `| half x e => sorry` |

The direct-admission walk checks **both types and values** for every axiom root, using the existing gate-163 traversal. There are 79 roots: the 62 frozen theorem targets, 13 additional pure readers, `Light.exists_tmProc`, and three compiler checks.

* All 76 non-compiler walks are empty, including `EndsIO.ofEnds`, `MeetsIO.ofMeets`, `Exec.det`, `EndsIO.take_iff`, `EndsIO.callLast` and `Light.exists_tmProc`.
* `length_compileStmt`: `{compileStmt, length_compileStmt}`.
* `sim` and `compileProgram_correct`: `{compileStmt, length_compileStmt, sim}`.

Every axiom print is in `evidence/logs/Axioms.log`. Non-compiler roots use only `propext`, `Classical.choice`, `Quot.sound` (or subsets); only the three compiler roots also use `sorryAx`. No new axiom or admission is present elsewhere.

## New helpers, readers and reuse

The five new private declarations are `rest_prefix` (drop the consumed prefix, using `List.IsPrefix.drop`), `trace_length` (one induction bounds the sum of both trace lengths), `of_empty` (transport existing `Ends` rules for runs with empty traces), `map_run` (share stream-preserving rule transport with a fixed overhead), and `shift_facts` (one induction proves both relocation facts). Existing local helper `abs_update_le` is reused unchanged.

Before adding these, the import closure was searched for prefix/drop/take equations, execution-length bounds, trace transports and relocation readers. Reused facts include `List.IsPrefix.drop`, `List.prefix_append`, `List.prefix_append_right_inj`, `List.prefix_take_iff`, the existing `Ends.skip/set/store/whileDone/mono`, `Program.getElem?_behind_right`, `Expr.abs_val_le`, `bounded_callFrame`, and the existing procedure/routine proofs. No new host or machine is constructed.

The additional public surface consists only of 13 pure home-file readers: `State.bounded_iff` in Syntax, the 11 `Stmt.shift_*` equations and `Program.behind_eq` in Renumber. All are `rfl`/`Iff.rfl`. No new simp attribute is added beyond the frozen/existing `Stmt.assigns` declaration.

Other-file definitions read by IO are consumed through `ends_iff`/the existing Ends rules, `meets_iff`, `inBitVal_eq`, `State.bounded_iff`, the `Stmt.shift_*` equations and the existing program lookup/relocation lemma. `Exec` is an inductive relation, inspected through its rules. Expression values and safety remain opaque parameters in IO. Core/Mathlib lemmas supply list and arithmetic operations; none of their definitions is named in a simp/rw/unfold argument.

Both IO source files re-elaborate with the imported Light definitions marked locally irreducible and their inherited simp attributes removed (exit 0). Six reader controls pass: delta/Iff.rfl succeeds unsealed, fails sealed, and the published reader still succeeds. See the `Seal_*`, `SealControls` and `UnsealedControls` probes/logs.

## Checks and copy screen

* All **74** modules in the dependency-ordered plan pass: 39 modules in the Syntax downstream closure (including both new IO modules), plus 35 prerequisites. Their final source/dependency/olean hashes and passing logs are in `evidence/build-manifest.csv`; no missing prerequisite or copied TCSlib olean is used.
* Final library checks have zero errors. The only sorry warnings are the authorized compiler constants. Existing upstream notation docstring warnings remain.
* Cache probe, 79 frozen type comparisons, 79 axiom prints/walks, both sealed module copies and all reader controls: exit 0.
* Patch check/application against the base, byte comparison of all 13 resulting files and `git diff --check`: exit 0.
* Final copy screen: **31 pairs**, versus **29** at the base; all 31 are individually reviewed in `evidence/COPY_REVIEW.md`. The two additional threshold crossings are the existing `Ends.seq`/`Ends.whileStep` witness templates after adding the required traces. No final pair involves a new IO proof. The shared length, transport and relocation arguments are factored into the five private helpers above.

## Size

| File | Base lines | Delivered lines |
|---|---:|---:|
| `TCSlib/Programs/Light/Assigns.lean` | 85 | 97 |
| `TCSlib/Programs/Light/Calls.lean` | 157 | 158 |
| `TCSlib/Programs/Light/Compiler/Simulation.lean` | 497 | 504 |
| `TCSlib/Programs/Light/Compiler/StatementCode.lean` | 382 | 416 |
| `TCSlib/Programs/Light/Compiler/WholeProgram.lean` | 283 | 287 |
| `TCSlib/Programs/Light/IO.lean` | 0 | 491 |
| `TCSlib/Programs/Light/IO/Exec.lean` | 0 | 170 |
| `TCSlib/Programs/Light/Logic.lean` | 302 | 315 |
| `TCSlib/Programs/Light/Renumber.lean` | 92 | 151 |
| `TCSlib/Programs/Light/Rules.lean` | 410 | 416 |
| `TCSlib/Programs/Light/RunsStayInLimits.lean` | 115 | 145 |
| `TCSlib/Programs/Light/Syntax.lean` | 269 | 307 |
| `TCSlib/Programs/Light/TMProc.lean` | 2172 | 2172 |

Every core/compiler/new IO file stays below 600 lines. TMProc was already 2172 lines at the base and remains 2172; its one allowed witness-reader change does not add lines or refactor the inherited file.

## Environment and reproduction

macOS/APFS host; 12 CPUs, 18 GiB physical memory, `memory_pressure` reported 55% available (about 9.9 GiB), and 65.3 GiB free disk at preflight. These exceed the addendum's 4 GiB memory/12 GiB initial disk floors. The Linux-only `/proc`, cgroup and GNU df requests are recorded with their macOS equivalents. The sandbox read override was needed for `sysctl`/machine-wide `ps` and managed-worktree writes. No runtime shim, `lake build`, Lake update, unfiltered cache fetch, external web source or sub-agent was used.

The pre-existing Mathlib package tree is symlinked at its exact manifest pins (allowed alternative in the addendum); every present package matched, and four documentation packages are ABSENT. No package/dependency tree was copied. The installed Lean 4.25.0 toolchain was selected explicitly. The cache probe ran after the initial bootstrap rather than before it; all planned Mathlib imports and the final cache probe passed. No cache download was necessary.

All TCSlib modules were bootstrapped into this job's fresh private `/tmp/fill-prog2-h1/oleans`. Checks use the repository's `leanelab-o.sh`/`leanelab.sh`, `lean -j4` under nice, one job-owned Lean process at a time, after a machine-wide process count. Recorded Lean slot waits total **0 seconds**. Copy screens ran one at a time. Logs were written in place from the start. Intermediate failed elaborations were corrected; the manifest selects final passing checks. The build scripts, probes, manifests, original verified bundle and final logs are shipped, without compiled products.

`evidence/tools/check.py` and `probe.py` record the exact host paths and environment. For another host, repoint their worktree/scratch roots, link a manifest-matched package tree, then run `check.py final all` followed by the shipped probes (rename `.lean.txt` back to `.lean`). Probe-only expected-signature axioms are confined to the scratch frozen-type checker and never used by library proofs.

## Diff stat

```text
 TCSlib/Programs/Light/Assigns.lean                |  20 +-
 TCSlib/Programs/Light/Calls.lean                  |  17 +-
 TCSlib/Programs/Light/Compiler/Simulation.lean    |  25 +-
 TCSlib/Programs/Light/Compiler/StatementCode.lean |  34 ++
 TCSlib/Programs/Light/Compiler/WholeProgram.lean  |  12 +-
 TCSlib/Programs/Light/IO.lean                     | 491 ++++++++++++++++++++++
 TCSlib/Programs/Light/IO/Exec.lean                | 170 ++++++++
 TCSlib/Programs/Light/Logic.lean                  |  75 ++--
 TCSlib/Programs/Light/Renumber.lean               |  67 ++-
 TCSlib/Programs/Light/Rules.lean                  |  22 +-
 TCSlib/Programs/Light/RunsStayInLimits.lean       |  38 +-
 TCSlib/Programs/Light/Syntax.lean                 |  78 +++-
 TCSlib/Programs/Light/TMProc.lean                 |   2 +-
 13 files changed, 958 insertions(+), 93 deletions(-)
```

Only the delivery zip is published to `arora-barak-ch3-4/inbox/fill-prog2-h1/` on the exchange branch, with pull --rebase and no force. No checkpoint archives were produced; no implementation branch or PR is pushed.
