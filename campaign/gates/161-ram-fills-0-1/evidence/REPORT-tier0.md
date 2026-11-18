# Extended word RAM: completed tier 0 fill

**Complete: all 18 admissions are proved.** The owned module elaborates without errors or warnings, all target axiom audits pass, and the complete 92-module verification closure passes. There is no remaining frontier, E-STATEMENT, E-READER, or E-HOST obstruction.

## Provenance and scope

- Base: `25040f435bba85ad563d5c1f1ceb42744aefc3eb`, fetched read-only from the repository, the pinned head of PR #370 (`ram/readers`).
- Local proof branch: `codex/fill-ram-steps`; proof commit: `344aa3c55baa55f9bf7335bd3882da20da0322a6`. The proof branch was never rebased or pushed.
- Owned file: `TCSlib/Programs/WordRAM/Extended.lean`, 698 lines. Only its 18 target proof bodies, their proof sketches, its module docstring, and nine private theorem helpers were changed or added. Every existing public statement is byte-identical to the base. All non-target declarations, imports, and target docstring text before the proof sketches are unchanged.
- Input: the exchange README and bundle both passed `SHA256SUMS`. Bundle SHA-256: `5625e8f27fe1c325550231c6482c72611db0fa2f03ab638b97c848256813423c`.
- Source SHA-256: `d3ec1044125698074418705e0347508cde9957cb72773ea1980bb302f93d1acc`.
- Patch SHA-256: `ab4dc9569b7455523f6e8c49a4ef6fe12044821bbb44de8e68306d9bb212fbe1`.
- Delivery route: final zip and the already delivered checkpoint zip, solely in `arora-barak-ch3-4/inbox/fill-ram-steps/` on `exchange/pass-shelat-ch5-8`, with pull --rebase and no force. No PR is opened.

## Target status

All names below are in `WordRAM`. Every row is proved and has no `sorryAx` dependency.

| Target | Status |
|---|---|
| `XSteps.trans` | Proved |
| `xstep_map_base` | Proved |
| `XSteps.of_steps` | Proved |
| `XSteps.of_steps_proj` | Proved |
| `XInstr.card_touches_le` | Proved |
| `StepsIn.toSteps` | Proved |
| `Steps.exists_stepsIn` | Proved |
| `StepsIn.mono` | Proved |
| `StepsIn.trans` | Proved |
| `StepsIn.agreeOutside` | Proved |
| `stepsIn_straight` | Proved |
| `XStepsIn.toXSteps` | Proved |
| `XSteps.exists_xStepsIn` | Proved |
| `XStepsIn.of_stepsIn_proj` | Proved |
| `HaltsWithin.mono` | Proved |
| `HaltsWithin.touches_le` | Proved |
| `HaltsWithin.unique` | Proved |
| `HaltsWithin.coin_irrel` | Proved |

`final-axioms.log` prints each target's axioms; `final-axioms-summary.log` checks that each set is a subset of `{propext, Classical.choice, Quot.sound}`. None contains `sorryAx`, so the required list of reachable admitted declarations is empty for every target and no admitted-dependency walk is needed.

## Private helpers, searches, and reuse

The helpers are all theorem proofs about supplied relations or the existing machines; they introduce no new machine or runner definition. The published surface remains 34 declarations.

| New private theorem | Role and facts searched or reused |
|---|---|
| `mapped_fetch` | Shares the mapped-fetch equation between the two conservativity routes. The brief names `List.getD_map`, but that theorem is outside the frozen import closure. The imported `List.getD_eq_getElem?_getD`, `List.getElem?_map`, and `Option.getD_map` prove the required equation directly. No import was added. |
| `xstep_base_fetch` | One instruction comparison shared by all base/projection lifting proofs. `step_def` and `effect_def` expose the vendored transitions. `Function.update_apply` identifies the memory functions. The one literal uses the permitted reducible `wd` abbreviation and core BitVec conversion. The analogous vendored `step_straight` and `wd_one` are private; their proofs were not introduced as separate copies. |
| `projected_fetch` | A non-verdict projected step fetches a base instruction. Uses `mapped_fetch` on the owned projection and `step_reject` to exclude every replacement arm. No such mixed-program fact exists in the three-module TCSlib import closure. |
| `lift_run` | Shares a single induction for step-preserving configuration maps. Used by the two conservativity run lemmas, both footprint-forgetting lemmas, projection with footprints, and coin-stream transport. The closure has base `Steps` calculus, but no map theorem between these run relations. |
| `footprint_mono` | Shares footprint enlargement for relations given by their zero/successor equations. Reused by the public base monotonicity target and the common finite-footprint construction. The imported run calculus has no footprint notion. |
| `exists_footprint` | Shares the finite union construction between base and extended runs, using `Finset.card_union_le` and `footprint_mono`. Instruction cardinal bounds cite `Finset.card_le_three` and `Finset.card_le_two`, rather than redoing insertion counts. |
| `step_agreeOutside` | Frames a base step, including stores, by `AgreeOutside.refl` and `AgreeOutside.update`; `step_def` and the owned `baseTouches` identify the target. The published `agreeOutside_effects` applies to code without stores, so it does not give this contract. |
| `xSteps_verdict_unique` | Synchronizes two extended runs and excludes stepping past a verdict. The imported `exec` results describe base programs and memories, not extended configurations with input, output, and coins; no applicable extended-run uniqueness result exists in the closure. |
| `xstep_coin_irrel` | Coin-free single-step invariance. `Option.getD_eq_iff` and `List.mem_of_getElem?` show that a fetched coin would be a program member; the default instruction is a base reject. The remaining instruction cases ignore the stream. |

The candidate searches and inspection covered `WordRAM/Basic`, `WordRAM/Steps`, `Programs/Util/Basic`, and the relevant core/Mathlib list, option, function-update, and finite-set API. `import-closure-search.log` records the TCSlib candidate enumeration. Searches found and the proofs cite `steps_straight`, `CodeAt.head/left/tail`, `Steps.zero_iff/succ_iff`, `effects_nil/cons`, and the `AgreeOutside` API. In particular, the straight-line footprint theorem specializes the existing `steps_straight` to a singleton head instead of re-proving its transition calculation. `XSteps.trans` uses the analogous induction to `Steps.trans`; the latter cannot directly apply to the different configuration and run relation.

## Other-file definitions and their readers

| Definition | How the proof consumes it |
|---|---|
| `WordRAM.step` | `step_def`, plus `step_reject` for projected replacement instructions. |
| `WordRAM.effect` | `effect_def`. |
| `WordRAM.Steps` | `Steps.zero_iff`, `Steps.succ_iff`, and `steps_straight`. |
| `WordRAM.CodeAt` | Only `CodeAt.left`, `CodeAt.tail`, and `CodeAt.head`. |
| `WordRAM.Straight` | Carried as a supplied hypothesis and passed to `steps_straight`; its body is never read. |
| `WordRAM.effects` | `effects_nil` and `effects_cons`. |
| `WordRAM.AgreeOutside` | `AgreeOutside.refl`, `AgreeOutside.update`, and `AgreeOutside.trans`. |
| `WordRAM.wd` | A reducible abbreviation; never supplied to `simp`, `rw`, or `unfold`. |
| `WordRAM.Cfg` | Structure constructors and fields, as permitted by the brief. |

`final-reader-scan.log` records the tactic-argument inspection. All named core/Mathlib arguments to `simp` or `rw` are equations or lemmas; same-file definitions may be unfolded. The extra sealed definitions `exec`, `loadWords`, `InRange`, and `WritesIn` are not read by the proofs. No generated definition equations or other-file definition bodies are used.

## Final checks and exit codes

| Check | Result and evidence |
|---|---|
| Owned module | Exit 0, no errors, no warnings, no admissions: `final-owned.log`. Its olean is nonempty and newer than the invocation: `final-owned-freshness.log`. |
| Axioms, all 18 targets | Exit 0; only the three standard axioms, zero `sorryAx`: `final-axioms.log` and `final-axioms-summary.log`. |
| Sealed complete proof file | Exit 0, no errors or warnings: `final-seal.log`. Eleven other-file TCSlib definitions are made locally irreducible; the two imported effects simp attributes are removed. |
| Seal controls | Both invocations exit 0: `final-unsealed-controls.log` and `final-sealed-controls.log`. Eleven definitional goals succeed unsealed and are rejected under the seals via `fail_if_success`; the published reader API controls still succeed sealed. The control file has harmless unused-variable warnings from the rejected probes. |
| Statement/public-surface audit | Exit 0: `final-freeze.log`. Exact statement bytes preserved for all 34 existing declarations; all non-target declarations unchanged; no public additions, removed declarations, import changes, or new simp attributes. |
| Bootstrap and downstream sweep | Exit 0 for all 92 modules. `final-module-summary.tsv` points to every invocation log and records nonempty oleans. Each of the 88 remaining dependency/importer compilations deletes stale output first and requires fresh nonempty output. |
| Patch replay | Exit 0 for both `git apply --check` and actual apply to a fresh copy of the pinned base; the result equals the delivered file byte-for-byte: `final-patch-replay.log`. |
| Whitespace check | `git diff --check -- TCSlib/Programs/WordRAM/Extended.lean`: exit 0. |

The five downstream modules all elaborate with zero errors and fresh nonempty oleans:

- `TCSlib/Complexity/RAMSimulation/Simulation`
- `TCSlib/Complexity/RAMSimulation/Classes`
- `TCSlib/Complexity/RAMSimulation`
- `TCSlib/Programs/WordRAM`
- `TCSlib/Programs`

The closure also verifies `RAMSimulation/WordSize` and the prerequisites of all these consumers. `evidence/full-order.txt`, `evidence/import-order.txt`, and `evidence/downstream-order.txt` record the complete orders. The repository-root `TCSlib.lean` is excluded as required by the campaign replay rules. Existing admissions in unrelated dependency modules are visible in their logs; none is reached by any of the 18 delivered theorems.

Patch stat against the pinned base, touching only the owned file:

```text
 TCSlib/Programs/WordRAM/Extended.lean | 468 ++++++++++++++++++++++++++++------
 1 file changed, 384 insertions(+), 84 deletions(-)
```

## Environment, deviations, and waits

Native macOS/APFS host, 12 logical CPUs, 19,327,352,832 bytes RAM (18 GiB). Initial free disk was 129,487,683,584 bytes (120.6 GiB) on the worktree and scratch filesystem. Native reclaimable-memory estimate `(free + inactive + speculative) * page size` was `7,349,698,560` bytes (6.845 GiB), above the 4 GiB floor; `memory_pressure` reported 75% system-wide memory free. Raw readings are in `preflight.log`. Linux cgroup, `/proc`, `nproc`, `df -B1`, and `/usr/bin/time -v` observations were replaced with `sysctl`, `vm_stat`, `memory_pressure`, `df -k`, APFS mount readings, and `/usr/bin/time -l`.

The existing Lean 4.25.0 toolchain and the permitted symlink to the populated main checkout's `.lake/packages` were used. `package-pins.log` ends: **PASS: every present package matches manifest URL and revision.** Documentation packages were absent. No package tree was copied or changed, and no cache download occurred. The successful import bootstrap served as the cache/import probe; a separate Mathlib-only probe and zero-size cache scan were not run before it. These are recorded environment-workflow deviations, not unverified imports: the final full closure successfully loads all required cached modules.

Only one Lean process of this fill ran at a time, through the campaign `leanelab.sh` / `leanelab-o.sh` wrappers, under `nice -n 10`, `lean -j4`, with `TCSLIB_LEAN_SLOTS=3`. The driver counted machine-wide Lean processes before each start. No other Lean process was observed at those checks and there were **zero waits**. Maximum recorded RSS was 2,281,226,240 bytes (2.125 GiB). No `lake build`, timeout, toolchain shim, or dependency fetch was used. The brief's specific campaign verification route was followed instead of the general AGENTS InfoView workflow.

Sandbox elevation was needed for process inspection, Git metadata, exchange transport, and isolated-worktree writes before that directory became the workspace. No approval rejection occurred. Creating the managed checkout also left 30 unrelated generated dataset diffs; they were never edited or staged by this proof work and are excluded from the proof commit and delivery patch.

The relocation checkpoint `fill-ram-steps-checkpoint-1.zip` was pushed at exchange commit `ded29f67f16a2d79ac7645c1b5e763cbdb1796d0`, with 14 proved targets and four explicitly open targets. Its final successor is this complete delivery. Development iteration logs remain in scratch and the checkpoint; this final zip contains the final checks, bootstrap/replay logs, probes, and drivers. Probe source files in the evidence are named `.lean.txt` for campaign hygiene.
