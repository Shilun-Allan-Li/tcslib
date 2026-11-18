# fill-ram-classes

All nine target corollaries are proved. There is no remaining admission in the delivered
`TCSlib/Complexity/RAMSimulation/Classes.lean`. The only admitted dependencies reached by
the proofs are the two simulation theorems expressly permitted by the brief.

Base: `24aa40503e183a6de58b67dc4d3f7aea08d670b5`, fetched from
`https://github.com/Shilun-Allan-Li/tcslib`, branch `ram/fills-0-1`, PR #371.
The proof branch is local `codex/fill-ram-classes`; it was created at this exact base and
was not rebased. The final patch is against this base and changes only the owned file.

The input was pulled from `exchange/pass-shelat-ch5-8` at `0fb8ea493` (abbreviated).
The bundle SHA-256 is
`cc841a4b67c8d668753ea060c1a647013738906983c5cbd691024ac4ec228b9b`.
The input README and bundle both passed their published checksums (exit 0).
The bundled COMMON, fill brief, policy, workflow, maintainer rules, environment addendum,
and supplied Lean interfaces were read. Input receipts are in `evidence/inputs/`.

## Targets and exact admission dependencies

All names below have namespace `WordRAM`. The dependency probe recursively visits the
types and values of constants, including theorem and opaque proof values, and records
each reachable value containing a primitive `sorryAx`. It also checks that the result
is precisely the one allowed simulation admission for that target.

| Target | Status | Complete list of reachable directly admitted declarations | Constants visited |
| --- | --- | --- | ---: |
| `mem_DTIME_of_decides` | proved | `WordRAM.exists_simulation` | 3501 |
| `mem_P_of_decides` | proved | `WordRAM.exists_simulation` | 4804 |
| `mem_P_of_decides_logWord` | proved | `WordRAM.exists_simulation` | 7378 |
| `mem_SPACE_of_decides` | proved | `WordRAM.exists_simulation` | 3492 |
| `mem_LOGSPACE_of_decides` | proved | `WordRAM.exists_simulation` | 6802 |
| `computesInSpace_of_computes` | proved | `WordRAM.exists_simulation` | 6793 |
| `mem_SPACE_mul_of_decides` | proved | `WordRAM.exists_simulation` | 6517 |
| `mem_NSPACE_of_accepts` | proved | `WordRAM.exists_ndSimulation` | 3508 |
| `mem_NL_of_accepts` | proved | `WordRAM.exists_ndSimulation` | 6816 |

Each target's `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx`. The last arises only through the admission shown in the table. In particular,
the proved tier 0 halting lemmas and tier 1 word-size witnesses introduce no other admission.
See `evidence/logs/final-axioms-dependencies.log` and the accompanying scratch probe.

## Proofs and private arithmetic

The generic time and space corollaries retain the simulation's machine. They use verdict
or function output readers, enlarge the time or space bound by `(A + 1) * a`, and package
the resulting witness through the class and machine predicate readers. The nondeterministic
proof retains the simulation's uniform per-input deadline and composes its acceptance
equivalence with the hypothesis.

For the polynomial-time corollary, `HaltsWithin.touches_le` and `HaltsWithin.mono` give
bounds `C * (n + 1)^d` steps and `3 * C * (n + 1)^d` cells. The time expression without
the simulation constant is bounded by

```
(C + (C + 1) * (4 * C^2 + 3 * C + 1)) * (n + 1)^(3*d + 1).
```

The logarithmic-word specialization enlarges its linear word-size computation and given
step bound to the common bound `(a + c + C) * (n + 1)^(d + 1)`. The logarithmic space
grades use coefficient `a + F₀ * (c + 1) + c + 2`. The space-constructible specialization
uses coefficient `a + c^2 + 2*c + 2` for `S(n)^2` before absorbing the simulation constant.

Exactly four private lemmas were added under the private bound arithmetic section:

| Private lemma | Role and reuse search |
| --- | --- |
| `simulation_constant_bound` | Absorbs start-up and simulation costs into `(A + 1)`; shared by time and space bounds. Searched the imported RAM and class arithmetic; the needed scalar inequality is discharged by `nlinarith`. |
| `simulation_space_bound` | Applies the scalar inequality to `simSpace_eq` and a supplied domination inequality. Shared by SPACE, function computation, and NSPACE. No imported lemma packages this simulation expression. |
| `logarithmic_space_bound` | Absorbs the two constant allowances using `logSpace_eq` and `Nat.mul_le_mul_left`. Shared by LOGSPACE, function computation, and NL. The imported normalized-logarithm readers were reused. |
| `polynomial_time_bound` | Bounds the time overhead by a cubic word/step bound times the input allowance. Uses existing natural-number multiplication and power monotonicity facts. No imported lemma gives this RAM-specific polynomial expression. |

Relevant searches and reused facts are recorded in `evidence/logs/reuse-search.log`.
The final closure-wide search covers all 58 prerequisite TCSlib modules. Core/Mathlib
facts reused include `Nat.mul_le_mul`, `Nat.mul_le_mul_left`,
`Nat.le_mul_of_pos_left`, `Nat.le_mul_of_pos_right`, `Nat.le_self_pow`,
`Nat.pow_le_pow_left`, `Nat.pow_le_pow_right`, `Nat.one_le_pow`, `pow_mul`, and `pow_succ`.
No proof text was copied, and no public declaration, import, attribute, machine, or host
was added. Existing mathematical infrastructure is cited rather than reproved.

## External definitions and their readers

The theorem-boundary inventory follows the owned proofs and their private helpers, follows
foreign theorem types, and stops at foreign proof and definition bodies. It finds exactly
26 ordinary external definitions. Definitions that are only transported as opaque predicates
or terms are identified explicitly below.

| Definition or definitions | Published interface used, or opaque use |
| --- | --- |
| `Complexity.DTIME` | `Complexity.mem_DTIME_iff` |
| `Complexity.P` | `Complexity.mem_P_iff` |
| `Complexity.SPACE` | `Complexity.mem_SPACE_iff` |
| `Complexity.LOGSPACE` | `Complexity.LOGSPACE_eq` |
| `Complexity.NSPACE` | `Complexity.mem_NSPACE_iff` |
| `Complexity.NL` | `Complexity.NL_eq` |
| `Complexity.SpaceConstructible` | `Complexity.spaceConstructible_iff` |
| `Complexity.logSpace` | `Complexity.logSpace_eq`, `Complexity.logSpace_le_succ` |
| `WordRAM.HaltsWithin` | Opaque simulation hypothesis; uses `HaltsWithin.touches_le` and `HaltsWithin.mono` |
| `WordRAM.WordSizeComputable` | Opaque witness passed to simulation; obtained from `wordSizeComputable_logSpace` or `wordSizeComputable_of_spaceConstructible` |
| `WordRAM.outputOf` | `outputOf_false`, `outputOf_true` |
| `WordRAM.simTime` | `simTime_eq` |
| `WordRAM.simSpace` | `simSpace_eq` |
| `Turing.FinTM.ComputesFunInTime` | `Turing.FinTM.computesFunInTime_iff` |
| `Turing.FinTM.ComputesInTime` | Opaque simulation conclusion; `Turing.FinTM.ComputesInTime.mono` |
| `Turing.FinTM.DecidesInTime` | `Turing.FinTM.decidesInTime_iff` |
| `Turing.FinTM.ComputesInSpace` | `Turing.FinTM.computesInSpace_iff` |
| `Turing.FinTM.DecidesInSpace` | `Turing.FinTM.decidesInSpace_iff` |
| `Turing.FinNDTM.DecidesInSpace` | `Turing.FinNDTM.decidesInSpace_iff` |
| `Turing.FinNDTM.AcceptsWithin` | Opaque endpoint of the simulation's acceptance equivalence |
| `Turing.MultiTapeTM.indicator` | Opaque verdict, preserved from hypothesis to simulation output |
| `Turing.MultiTapeTM.initCfg`, `Turing.MultiTapeTM.spaceUsed` | Opaque terms in the simulation's space inequality |
| `Turing.NDTM.HaltsWithin` | Opaque halting conclusion supplied by `exists_ndSimulation` |
| `Turing.NDTM.initCfg`, `Turing.NDTM.spaceUsedWith` | Opaque terms in the simulation's branch-space inequality |

There is no unfolding of these definitions in the delivered proofs. All explicit `rw` and
`simp only` arguments are published equations or arithmetic lemmas. The scratch sealed copy
sets all 26 definitions locally irreducible and removes the active simp attributes on
`Turing.MultiTapeTM.initCfg` and `Turing.NDTM.initCfg`. It elaborates without errors or warnings.
Separate native and sealed controls check definitional equality with each definition's body:
all 26 reduce natively and all 26 fail to reduce under the seal. The sealed controls also
verify that none has an active simp unfolding attribute.

## Verification

| Check | Result |
| --- | --- |
| Input checksums | exit 0, both files OK |
| Dependency package pins | 0 mismatches for all packages present; four documentation packages absent |
| Fresh prerequisite bootstrap | all 58 modules exit 0, fresh nonempty oleans |
| Final owned file | exit 0; no errors or warnings |
| `TCSlib/Complexity/RAMSimulation.lean` facade | exit 0; no errors or warnings |
| All nine axiom prints and dependency walks | exit 0; only the permitted admissions |
| Definition boundary inventory | exit 0; 26 external definitions |
| Sealed owned file | exit 0; no errors or warnings |
| Native definition controls | exit 0; all 26 reduce |
| Sealed definition controls | exit 0; all 26 blocked and simp attributes absent |
| Statement freeze | all nine statement byte strings identical; imports/options/header identical |
| Public declaration inventory | 9 before, 9 after; none added or removed |
| Forbidden admission tokens in source | 0 |
| `git diff --check` for the owned file | exit 0 |
| Patch application against base | exit 0; reproduces the delivered file byte-for-byte |

The facade is the only importer of Classes under `TCSlib/`, matching the brief's downstream
scope. The scratch sources are shipped as `.lean.txt` so they cannot enter a library build.
`evidence/final-checks.json` records the final exit codes; individual final and bootstrap
logs contain wall times and maximum resident set sizes. The check-results history also
retains development runs; early elaboration and scratch-probe issues were corrected before
the successful final checks listed here.

The final file is 360 lines. The source patch has this exact scope:

```
 TCSlib/Complexity/RAMSimulation/Classes.lean | 238 +++++++++++++++++++++++----
 1 file changed, 203 insertions(+), 35 deletions(-)
```

Existing target statements and the non-sketch portions of their docstrings were preserved.
All target proof sketches were updated. The module docstring's obsolete audit/pending
parenthetical was removed after proving the final admission.

## Environment and waits

This run used the local macOS host, so native `sysctl`, `vm_stat`, `memory_pressure`,
`df -k`, `mount`, and `/usr/bin/time -l` were recorded instead of Linux cgroup/proc tools
and GNU `time -v`. Preflight found 12 CPUs, 18 GiB physical RAM, 63% reported free memory,
and approximately 122.8 GiB available disk on APFS. Maximum recorded Lean RSS was
2,275,278,848 bytes (about 2.12 GiB). There were no resource failures and no Lean-capacity waits.

The worktree's `.lake/packages` is a symlink to the populated cache at
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-arora-barak-ch3-4/.lake/packages`.
Every present package's URL and revision matched the base manifest. The cache had no empty
olean files; no cache fetch was needed. No other session's TCSlib oleans were reused:
the entire prerequisite closure was compiled from this base into this fill's own
`/private/tmp/fill-ram-classes/oleans` tree.

Every Lean invocation used the repository's `leanelab.sh` or `leanelab-o.sh` wrapper,
`nice -n 10`, and `-j4`. This fill started only one Lean process at a time, checked the
machine-wide count before each start, and used a slot cap of 3. The recorded counts at
every start were 0. `lake build` was never run. Administrative Git writes and process
inspection used the execution environment's approved sandbox escalation.

The managed worktree checkout on case-insensitive APFS exposes pre-existing pairs of
blueprint paths that differ only by case. Its Git status therefore includes unrelated
blueprint differences from checkout. Those files were not edited or delivered; the exact
status and collision pairs are recorded in `evidence/logs/checkout-collisions.log`.
Only the owned Lean path is included in the patch. The exchange delivery contains only
`fill-ram-classes.zip` in the authorized inbox. No checkpoint zip was needed.

## Delivery contents

The archive contains this report, the complete owned file at its library path,
`fill-ram-classes.patch`, a SHA-256 manifest, and the check logs, input receipts,
scratch verification probes, and serial check driver under `evidence/`.
The exchange branch is pulled with `--rebase` before delivery, then the archive alone
is committed and pushed without force. No source branch or pull request is published.
