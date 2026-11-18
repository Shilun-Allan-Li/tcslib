# fill-ram-bridge — final delivery

All four targets are filled. The two word-size results are closed; the two function results are
proved modulo the permitted `WordRAM.exists_simulation`. No frontier remains in the owned files.

## Base and scope

- Repository: `Shilun-Allan-Li/tcslib`.
- Read-only fetched base: `e5fe99819b8ceb11f43894964630a594eb61ff0a` (`ram/bridge-statements`, PR #379).
- Local proof branch: `codex/fill-ram-bridge`; head: `269d7dfb7d309e97f1f00ed3d4b62239229f59db`. Its only parent is the base;
  the proof branch was never rebased or pushed.
- Input bundle SHA-256: `7d780c7b4e76b1b965bbbe46b61e143b72efcf6bcbaa976476daabc7b1f74481`.
  The README and bundle both passed the supplied SHA256SUMS. The verified inputs are included.
- Only the four target bodies and their proof-sketch paragraphs changed, across the two owned
  files. Every existing statement is byte-identical, including whitespace. The ordered declaration
  inventory is unchanged: WordSize 17 (6 public / 11 private), Classes 15 (11 public / 4 private).
- No imports, public declarations, private declarations, readers, simp attributes, hosts, axioms
  or admissions were added. Neither owned file has a remaining admission or a pending-proofs module label.

## Targets and admission walks

| Target | Result | Reachable direct admissions |
|---|---|---|
| `WordRAM.wordSizeComputable_of_timeConstructible` | Proved | none |
| `WordRAM.wordSizeComputable_poly` | Proved | none |
| `WordRAM.polyTimeComputable_of_computes` | Proved modulo simulation | `WordRAM.exists_simulation` |
| `WordRAM.polyTimeComputable_progOut` | Proved modulo simulation | `WordRAM.exists_simulation` |

The first proof takes the time-constructibility witness and bounds its visited work cells with
`Turing.MultiTapeTM.spaceUsed_le_mul_succ`, using coefficient `(M.k + 1) * (c + 1)` for both
bounds. The second applies `Complexity.timeConstructible_poly` and multiplies the coefficient by
`C + 1` via one local pointwise inequality, reused for both bounds.

The function proof uses simulation in function mode, enlarges steps and footprint through
`HaltsWithin.touches_le` and `HaltsWithin.mono`, and cites the existing
`polynomial_time_bound` and `simulation_constant_bound`. The final polynomial has degree
`3*d + 1`. The last proof cites it and rewrites each halting output using `progOut_eq`.

`evidence/logs/axioms.log` includes the literal prints and a recursive walk of both types and
values, adapted from the base's gate-163 AdmissionWalk. The complete admitted-constant lists are
exactly those in the table; no admitted RecordTable declaration is reached. The closed targets
print `[propext, Classical.choice, Quot.sound]`; the function targets additionally print `sorryAx`.

## Reuse and definition boundaries

No new private declaration was needed. Before drafting, the import closure and existing proofs
were searched for the time/space estimate, polynomial arithmetic, monotonicity, function packaging
and halting-output uniqueness. The public facts cited are the ones already named in the brief;
existing private `polynomial_time_bound` and `simulation_constant_bound` are reused. There is no
copied proved helper or newly re-derived machine routine. Power normalization cites Mathlib's
`pow_mul` and `pow_succ`; positivity and multiplication inequalities cite the existing Nat lemmas.

The elaborated boundary walk identifies the following 12 other-file ordinary definitions. The
list includes definitions occurring only in types, rather than read by the proof.

| Other-file definition | Published access or use |
|---|---|
| `Complexity.TimeConstructible` | `timeConstructible_iff`; target 2 cites `timeConstructible_poly` |
| `Complexity.PolyTimeComputable` | `polyTimeComputable_iff` |
| `Turing.FinTM.ComputesFunInTime` | `computesFunInTime_iff` |
| `Turing.FinTM.ComputesInTime` | time witness retained; `ComputesInTime.mono` enlarges deadlines |
| `Turing.MultiTapeTM.spaceUsed` | `spaceUsed_le_mul_succ` in target 1; otherwise only in a discarded simulation clause |
| `Turing.MultiTapeTM.initCfg` | passed unchanged to `spaceUsed_le_mul_succ`; otherwise type-only |
| `WordRAM.HaltsWithin` | `HaltsWithin.touches_le`, `HaltsWithin.mono`; target 4 rewrites its output argument |
| `WordRAM.WordSizeComputable` | same-file definition may reduce in WordSize; passed unchanged in Classes |
| `WordRAM.outputOf` | `outputOf_true` |
| `WordRAM.simTime` | `simTime_eq` |
| `WordRAM.simSpace` | only the discarded second simulation clause; no reading |
| `WordRAM.progOut` | `progOut_eq` |

All explicit `simp`/`rw` arguments in the changed proofs are published theorems, or the local
coefficient `a`. There is no other-file, Core or Mathlib definition in a tactic unfolding list.
The missing-readers rule was read; no missing reader was needed or added.

Each target passed in its own scratch section with every ordinary foreign definition from its
elaborated boundary marked locally irreducible and any simp unfolding disabled. Guards confirmed
all 22 per-target seals active (4 + 4 + 10 + 4). For all 12 distinct heads, independent delta and
equation-goal definitional-equality controls succeeded unsealed and failed sealed. See the four
seal logs, controls logs and `boundaries.json`. Probe sources are included as `.lean.txt`.

## Verification

All checks ran through the supplied `devtools/seyoon/leanelab-o.sh` or `leanelab.sh` wrappers,
with `nice -n 10`, `lean -j4`, and `TCSLIB_LEAN_SLOTS=3`. No `lake build` or Lake command ran.
The olean output was this fill's initially empty `evidence/oleans`; no existing TCSlib oleans
were copied or reused. Each compiling check removed the old output and required exit 0, no
error diagnostics, and a fresh nonempty olean. Scratch probes used the plain wrapper.

| Final check | Exit | Outcome |
|---|---:|---|
| Mathlib-root cache probe | 0 | passed |
| Fresh import closure | 0 for the final check of every module | all 78 modules checked |
| WordSize (`bootstrap-048-WordSize.log`) | 0 | zero errors / admission warnings |
| Classes (`classes-check-3.log`) | 0 | zero errors / admission warnings |
| RAMSimulation facade (`downstream-facade.log`) | 0 | zero errors |
| Axiom prints and dependency walks | 0 | exactly the allowed axioms/admissions |
| Elaborated boundary inventory | 0 | four targets inventoried |
| Four sealed target checks | 0 each | passed |
| Unsealed / sealed controls | 0 each | expected true / false results |
| Statement freeze | 0 | byte-identical statements; no declaration drift |
| Style lint | 0 | 0 FAIL, 0 WARN |
| `git diff --check` | 0 | passed |
| Patch application and source comparison | 0 | base + patch reproduces src/ exactly |
| Git bundle verification | 0 | passed |

The WordSize downstream closure consists of Simulation, Classes and the RAMSimulation facade;
the other direct importer of Classes is that facade. They all passed. The global `TCSlib` root
is outside the prescribed facade check and, as the standing rules require, was not built.
Initial Classes checks exposed a missing explicit function argument and an overly expansive
power rewrite; both were fixed. Those two failed development logs are retained. All final
checks refer to the delivered source hashes. `checks.tsv` gives start/end times, exit codes
and fresh-output success for every run; each Lean log includes maximum resident memory.
Maximum measured RSS: 2360410112 bytes (2.20 GiB).

## Environment and waits

- Native macOS arm64, APFS, 12 CPUs and 19,327,352,832 bytes physical memory. The initial
  preflight recorded 117,403,127,808 bytes free disk and native `memory_pressure` free 49%,
  estimated 9,470,402,887 bytes headroom, above both resource floors.
- macOS has no cgroup, `/proc/meminfo`, GNU `df -B1`/`df -T` or `nproc`; native `sysctl`,
  `vm_stat`, `memory_pressure`, `df -kP` (1024-byte units converted to bytes), and mount output
  are recorded instead. The preliminary `stat -f %T` output was not a filesystem-type reading;
  mount output supplies the APFS identification. No shim was needed.
- Installed pinned Lean 4.25.0 was used. The allowed package symlink points to
  `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-arora-barak-ch3-4/.lake/packages`.
  `package-pins.log` ends `PASS: all 11 present packages match manifest URL and revision.`
  Four unused documentation packages are recorded ABSENT. The 42 Mathlib roots and the
  closure probe passed; zero empty oleans were found. No cache fetch ran, so no archive-store
  reuse or downloads are attributed to this session.
- Exactly one Lean check of this fill ran at a time. Machine-wide process counts were checked
  before every launch; the maximum other-Lean count then was 1. The same shared slot
  locks were capped at three. Explicit waits for the machine-wide limit: 0; no process
  deviation was observed. All checks wrote their final log paths from the start.
- The macOS checkout exposes 30 pre-existing case-insensitive blueprint path collisions.
  Their unrelated working-tree differences were preserved and excluded from the commit and
  payload; see `checkout-notes.log`. The two source files are unaffected.

## Patch and delivery

The payload includes `src/`, `changes.patch`, a signed-off format-patch series with signing
metadata in `patches/COMMITS.tsv`, `proofs.bundle`, all check logs and probes, and a top-level
SHA256SUMS covering every delivered file except itself. No compiled outputs are included.
No separate checkpoint archive was created. The final ZIP is delivered only to
`arora-barak-ch3-4/inbox/fill-ram-bridge/` on `exchange/pass-shelat-ch5-8`, using a separate
delivery checkout, `git pull --rebase` immediately before push, and no force push or PR.

Committed diff against the base:

```text
 TCSlib/Complexity/RAMSimulation/Classes.lean  | 37 ++++++++++++++++++++++++---
 TCSlib/Complexity/RAMSimulation/WordSize.lean | 31 +++++++++++++++++++---
 2 files changed, 61 insertions(+), 7 deletions(-)
```

Final file sizes: WordSize 968 lines; Classes 428 lines. No maintainer split is needed for a
1,500-line file. Integration still requires the maintainer's normal gate and campaign PR.
