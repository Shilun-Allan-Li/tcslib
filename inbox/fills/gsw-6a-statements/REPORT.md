# gsw-6a-statements · checkpoint 1 (O1 complete; Defs, Eval, NANDForm compiled)

Lead worker: Claude, with two sub-agents (`bp`, `fa`). This is **checkpoint 1**. The final delivery replaces it.

## Base and heads

- **Issue base:** `f6f295a6502b72bbf498bb8c64b63f847e910866`, the tip of `cryptography/pass-shelat-ch2-4` at issue. It was fetched by name into a separate clone, `/home/user/gsw6a`.
- **Records pin:** `c5eb7cf4b9f13eb2d4340493b7537b9de092d457`.
  - `briefs/lattice-gsw/phase6/plan-section.md` and `rulings.md` hash to the pack's SHA-256 values.
  - The seven files of `issued-6a-r1/` that are also in the pack are byte-equal to it.
- **Exchange pack:** read at `7031cef6ea880180f265fd5878d26a37a25b868f`. `shasum -a 256 -c` passes on `SHA256SUMS` (6 files) and `inputs/SHA256SUMS` (4 files).
- **O1 head:** `owner/o1-balanced` = `413e9aa42f6b96b4d65673c37c83819b2fb77579`, one commit, local only.
- **Statement series:** `stmt/gsw-6a`, stacked on O1. It is local and in progress, and is not part of this checkpoint's patches.

## Environment (addendum v1, Part 1)

**Preflight** (`evidence/logs/preflight.log`, `preflight-assessment.txt`)
- `nproc` 4.
- No cgroup memory limit. `MemAvailable` is 14.65 GiB, above the 4 GiB floor.
- `/dev/vda` is ext4 with 15.11 GiB free, above the 12 GiB floor.
- Pass. No E-RES condition occurred.

**Toolchain:** `elan` installed `leanprover/lean4:v4.25.0` (`evidence/logs/toolchain.log`).

**Cache**
- The archive store `~/.cache/mathlib` was absent before the first fetch (`cache-store.log`).
- One narrowed `lake exe cache get` ran on the 377 Mathlib roots of the order list (`mathlib-roots.txt`, equal to the pack's `roots.txt`).
- It attempted 3,607 files, downloaded 3,607, decompressed 3,607, and exited 0 (`cache-get.log`).
- No zero-size olean was found.

**Packages:** last line of `package-check.log`:
`RESULT: PASS: 11 present, 0 mismatched, absent: doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean`.

**Lean:** one process at a time on the host, through one `flock` (`evidence/tools/check.py`, `sweep.py`).

## O1: what changed

- The section "Simulating an unbounded gate by a balanced binary tree" moves from `TreeNCAC.lean` (lines 172–350 at the base) into the new `TCSlib/Complexity/CircuitComplexity/FormulaArith/Combinators.lean`. It covers `pairUp`, `combineFuel`, `combine` and their lemmas.
- The new facade `FormulaArith.lean` imports it. `CircuitComplexity.lean` imports the facade and adds one contents entry.
- **Promotion**
  - `combine` becomes the public `BoolCircuit.TreeCircuit.balanced`.
  - Its four lemmas become `TreeCircuit.balanced_eval`, `maxFanin_balanced_le`, `depth_balanced_le` and `size_balanced_le`, each with a formula docstring.
  - New readers `balanced_nil` and `balanced_singleton` are proved by `rfl`.
  - `pairUp`, `combineFuel` and their lemmas stay `private`.
- **TreeNCAC re-pointed.** `TreeNCAC.lean` now imports `Combinators`. `toBinary` and the proofs of `toBinary_eval`, `toBinary_maxFanin_le`, `toBinary_size_succ_le` and `toBinary_depth_le` call `balanced` and its public lemmas. Every statement of the file is unchanged.
- **The moved proofs** (`evidence/o1/byte-compare.txt`)
  - Method: the old block with the renames applied, compared against the new block.
  - Whitespace-insensitive comparison: 17 hunks, all accounted for.
    - The **three Rule 10 repairs the brief names**: old `:195`, `:199` and `:261` now read `TreeCircuit.eval` through `TreeCircuit.eval_node_true` and `eval_node_false` (TreeDAG:126/132). The `:199` repair also replaces `List.foldr_cons`/`_nil` by `List.all_cons`/`_nil` and `List.any_cons`/`_nil`, the list lemmas for those readers' `all`/`any` form.
    - **Two further Rule 10 repairs.** The new owner's whole-file seal exposed them (see below): `sumSize_pairUp` and `maxFaninL_pairUp`, nil case.
    - The five promoted docstrings.
  - The raw comparison also shows **three line re-wraps**, whitespace only. They are lines that were over 100 characters at the base (old `:211`, `:225`, `:231`), wrapped because of the 100-character rule.
- **Disclosure: two repairs beyond the brief's three.** At the base, `sumSize_pairUp | [] => le_refl 0` and `maxFaninL_pairUp | [] => Nat.zero_le _` read `TreeCircuit.sumSize []` and `maxFaninL []` as `0` by definitional unfolding.
  - With the foreign `Basic.lean` definitions sealed, both fail.
  - They now read through `TreeCircuit.sumSize_nil` and `maxFaninL_nil` (Basic, `rfl` readers): `by rw [pairUp, TreeCircuit.sumSize_nil, List.length_nil]` and `by rw [pairUp, TreeCircuit.maxFaninL_nil]; exact Nat.zero_le _`.
  - Without them, the new owner `Combinators.lean` would fail its seal. Plan section r3 §H8 item 20 requires it to pass.
  - This is a deviation from "byte-identical except three repairs", made so that the moved file passes its seal. Seyoon may prefer the three-repair form with a seal exception instead.
- **Facade options.** The facade `FormulaArith.lean` carries the three repo-standard `set_option` lines, because `style_lint` requires them.

## O1: checks

**1. Build of the closure at the O1 head** (`evidence/build/o1/`)
- The upstream prefix: modules 1–10 of `order.txt`, all rc=0, in `bootstrap.log.summary`.
- Then the O1 modules and the downstream modules in order, in `closure-o1.log.summary`, all rc=0 with 0 errors and 0 `sorry`: `Combinators`, `FormulaArith`, `TreeNCAC`, `NCAC`, `Parity`, `Hierarchy`, the facade `CircuitComplexity`, and `ComputationalModels`.
- These are run in the separate worktree `/home/user/wt-o1` at `413e9aa4`. Its own olean tree was seeded from the lead's bootstrapped TCSlib tree (TCSlib oleans only).

**Downstream.** The only modules of `order.txt` whose closure contains a changed module are TreeNCAC, NCAC, Parity, Hierarchy, the facade, `ComputationalModels` and the root (`evidence/build/downstream.txt`). The root build is part of the final.

**4. Admissions at the O1 head:** none. O1's modules and its downstream modules have 0 `sorry` warnings.

**5. Axioms** (`evidence/o1/AxiomProbe.lean`, `.log`)
- All 141 constants of `Combinators`, `FormulaArith` and `TreeNCAC` were checked, auxiliary constants included.
- They use only `propext`, `Classical.choice` and `Quot.sound`, or none. No `sorryAx`.
- `StmtDump.log` prints every constant with its full name and type.

**6. Rule 10** (`evidence/o1/rule10/`)
- **Tools.** Whole-file seals use the GSW statement phase's tools (`evidence/tools/xr/`: `mkcollect.py`, `mkseals_ab.py`, `mkseals_coe.py`, `sealsum.py`, and the archived Gate06/Gate10 instrumenter), plus `runner_lock.py`. `runner_lock.py` is `runner_full.py` with this job's package path and the host lock: `lean -DmaxErrors=0`, no `-o`.
- **Variants.** A (strict), B (`SEAL_EVAL=1`), coe-A, coe-B.

| Owner | Requested | A | B | coe-A | coe-B |
|---|---|---|---|---|---|
| `Combinators.lean` | 174 | 0 errors | 0 | 0 | 0 |
| `FormulaArith.lean` | 194 | 0 | 0 | 0 | 0 |
| `TreeNCAC.lean` | 194 | 2 errors | 2 | 2 | 2 |

- **TreeNCAC's two errors** are in the untouched private `maxDepth_map_le` and `maxFaninL_map_le`.
  - They are `| [], _ => Nat.zero_le _` reads of `maxDepth []` and `maxFaninL []`.
  - Both declarations are byte-identical to the base (frozen check below). They are pre-existing reads in a frozen file, outside O1's three named repairs, and recorded for clean-up part 2.
- **Explicit-unfold scan** (`explicit-unfold-scan.txt`)
  - `Combinators.lean`: 0 foreign unfolds.
  - `TreeNCAC.lean`: 4 pre-existing, all in lines O1 does not change.
    - `:188`: `eval_node_map`'s `TreeCircuit.eval`. This is the line-366 read the brief says stays.
    - `:228`, `:250`, `:268`: the `hlit` cases `simp [TreeCircuit.toBinary, TreeCircuit.maxFanin]`, `…size` and `…depth` in `toBinary_maxFanin_le`, `toBinary_size_succ_le` and `toBinary_depth_le`. Their bodies change only by the rename.
- **Paired controls on the new owner** (`rule10/controls/`)
  - Unsealed `rfl` read of `balanced`: passes.
  - Sealed: fails with exactly 1 error.
  - Sealed, through `balanced_nil`: passes.
  - `FormulaArith.lean` defines nothing, so it gets no pair.

**8. Frozen-file check** (`evidence/o1/headers/`)
- `frozen_check.py` compares every declaration of `TreeNCAC.lean` and `CircuitComplexity.lean` at base and O1, header and whole text.
- Result: `violations=0`.
  - Only O1's 16 documented removals (the moved block).
  - Five documented body changes: `toBinary` and its four proofs, with headers identical.
  - `CircuitComplexity.lean` has no declarations.
- Controls: one altered character (`≤`→`<` in `clog_poly_le`'s statement) gives exactly 1 violation, and one deleted reader (`TreeCircuitFamily.mem_language_iff`) gives exactly 1 violation.

**Other checks**
- **Lint** (`evidence/lint/`)
  - `campaign_style_lint.py TCSlib/Complexity --check8b`: base 25 FAIL / 390 WARN over 500 files, which is the maintainer's baseline; O1 25 / 390 over 502. The line sets are equal.
  - `style_lint.py` on O1's files: 0 findings for `Combinators.lean` and `FormulaArith.lean`. The changed `TreeNCAC.lean` and `CircuitComplexity.lean` show no findings.
- **Sizes** (`evidence/o1/sizes.txt`)
  - `Combinators.lean`: 246 lines, max width 99.
  - `FormulaArith.lean`: 23 lines, max width 97.
  - `TreeNCAC.lean`: 359 lines. Its two pre-existing lines over 100 (module docstring line 62, and the `Language.InTreeNC.inTreeAC` header at line 165) are unchanged from base lines 61 and 164.
- **Clash scan** (`evidence/o1/clash.txt`): 18 new names. 11 are moved privates (removed from TreeNCAC by the same change). There are 0 clashes and no `NAnd` or `toLayered`.
- **decls2** (`evidence/o1/decls2.tsv`): 7 ADDED (`balanced` and its 6 lemmas), 0 CHANGED, 0 REMOVED.
- **Reproduction:** `patches/o1/` with `git am` in a scratch clone, committer fields from `COMMITS.tsv`, reproduces `413e9aa42f6b96b4d65673c37c83819b2fb77579` (`evidence/o1/reproduce.txt`).

## Statement phase progress

- **Defs, Eval and NANDForm are compiled.** So are all other new modules and the facades. The closure run at the statement head is `evidence/build/final-closure/summary.txt`: 19 modules, rc=0, 0 errors.
- **`sorry` warnings equal the targets.** Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, NANDForm 6, NANDLayering 7, Combinators 26, CarrySave 7, Compare 7, ModSum 4. That is 100.
- **Probes so far:** P8 (NAND gadget) and P9 (layering) pass by kernel `decide` (`evidence/probes/`).
- **Still to come in the final:** the root build, the full checks and the delivery.

## Who wrote what

- **Lead:** O1; `NANDForm.lean`; `NANDLayering.lean`; the registrations; the evidence tools; every commit.
- **Sub-agent `bp`:** `BranchingPrograms/` and its facade.
- **Sub-agent `fa`:** `FormulaArith/{CarrySave,Compare,ModSum}`, the F1–F3 part of `Combinators.lean`, and the facade's new contents lines.
- Details are in the final report.

## Scope requests

None.

## Evidence

`evidence/SHA256SUMS` lists every evidence file. The top-level `SHA256SUMS` lists every delivered file except itself.
