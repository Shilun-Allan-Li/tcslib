# Chapter 2 — Epoch 1, Batch B

Six of six targets filled and kernel-checked. The final fresh sweep passes all
53 campaign modules with zero error diagnostics. Only the two owned source
files differ from the base. No filled target depends on `sorryAx`.

**Axiom expectation discrepancy:** the brief expects exactly
`[propext, Classical.choice, Quot.sound]` for every target. The actual kernel
prints give that triple for `DTIME_subset_NTIME` and the strict subset
`[propext, Quot.sound]` for the other five targets. Thus the literal exact-list
expectation is not met for those five; every dependency is nevertheless one
of the permitted standard axioms. The exact prints are included below and
in `logs/axioms.log`. No extraneous dependency was inserted to inflate a footprint.

## Provenance and branch

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Base: `7494522e8826be6b54675307668435afc59c005d`.
- Working/delivery branch: `complexity/arora-barak-ch1`, following the user's
  subsequent branch instruction in this conversation. This supersedes the
  brief's suggested `fill/ch2-e1-B` branch name.
- Final commit: `a680e6f20170c41609741dde2b24bf652cbb417c`.
- Six local commits, in the required fill order; author: Codex.
- Toolchain: Lean 4.25.0, release commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, unchanged pinned dependency.
- Delivery: ZIP; no PR, push, or other remote repository mutation.

## Targets, in fill order

| # | Target | Local commit | Proof versus the audited sketch |
|---|---|---|---|
| 1 | `Turing.MultiTapeTM.toNDTM_runWith` | `514c7fcd` | Induction on the choice word, generalizing the configuration. The step functions coincide definitionally. The unprimed `runFrom_succ_eq_step` peels the first step, exactly matching `runWith_cons`; no orientation flip or word reversal was needed. |
| 2 | `Turing.NDTM.HaltsWithin.mono` | `467835dc` | The prefix has exactly the old budget's length. All-branch halting applies to it; append factoring and absorption equate the whole run with the halted prefix run. |
| 3 | `Turing.FinNDTM.AcceptsWithin.mono` | `8cc3520a` | Pad with false bits to the larger exact length. Absorption preserves both the halted state and the output exactly equal to `[true]`. |
| 4 | `Complexity.NTIME.mono` | `881f222d` | Reuse the machine and multiplier. Transfer halting and forward acceptance by targets 2–3; backward acceptance uses all-branch halting of the shorter prefix and equality of the entire configurations. |
| 5 | `Complexity.DTIME_subset_NTIME` | `ca486710` | Embed the deterministic machine. `computesInTime_iff` and target 1 give halting on every branch. The indicator gives `[true]` for members and `[false]` for nonmembers. |
| 6 | `Complexity.NTIME_eq_empty_of_exists_zero` | `a680e6f2` | Apply all-branch halting to an input of the vanishing length and the empty choice word. This forces `some` of the initial state to equal `none`, a contradiction. |

All six source edits compiled on their first proof-check attempt. Each was
followed by the owned module's check and every subsequent module in the order
list before the next target was edited. No machine construction was added.

## Scope, declarations, and escalations

- Modified sources, supplied in full at their repository-relative paths:
  - `TCSlib/Complexity/TuringMachine/Nondeterministic.lean`
  - `TCSlib/Complexity/ClassNP/NTIME.lean`
- New public declarations: **none**. New private declarations: **none**.
- Removed, renamed, or reordered declarations: **none**.
- Requested shared lemmas: **none**.
- Mathematical escalations / unprovable targets: **none**.
- Verification expectation escalation: the five smaller axiom footprints
  described above. All actual dependencies are recorded without claiming
  six literal matches to the expected triple.
- All definitions, signatures, imports, options, attributions, and docstrings
  are byte-identical to the base. No sketch appendices or other prose edits.
- Automated scope checking matches each complete modified file against its
  base with only the designated `sorry` bodies replaced. It also checks that
  the replacements introduce no declarations or admissions. See
  `logs/scope-freeze.log`.
- The diff is exactly two files, 69 inserted and six removed lines.
  All out-of-scope source files and admissions are unchanged.
- Owned-file policy lint: zero FAIL and zero WARN. `git diff --check` passes.

## Verification

Every listed check uses the unchanged `scripts/lean_check_tree.sh` and the
53-entry `scripts/ab_ch1_module_order.txt`; the script requires successful
Lean exit, no error diagnostics, and a freshly produced olean. The final
sweep starts from a new empty olean tree, separate from the bootstrap/stage
tree. The subsequent axiom prints import that final tree.

| Log | Modules passed | Error lines | Admission warnings in that sweep |
|---|---:|---:|---:|
| `bootstrap.log` | 53/53 | 0 | 59 |
| `stage-01-toNDTM_runWith.log` | 22/22 | 0 | 58 |
| `stage-02-HaltsWithin-mono.log` | 22/22 | 0 | 57 |
| `stage-03-AcceptsWithin-mono.log` | 13/13 | 0 | 30 |
| `stage-04-NTIME-mono.log` | 13/13 | 0 | 29 |
| `stage-05-DTIME_subset_NTIME.log` | 13/13 | 0 | 28 |
| `stage-06-NTIME-empty.log` | 13/13 | 0 | 27 |
| `final-sweep.log` | 53/53 | 0 | 53 |

The reduction from 59 baseline to 53 final admission warnings is exactly the
six commissioned fills. Neither owned file has a remaining admission warning.
Existing warnings in unrelated modules remain in the unfiltered logs.

Final sweep tail:

```text
CHECK 51/53 TCSlib/Complexity/Formulas
PASS TCSlib/Complexity/Formulas
CHECK 52/53 TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
CHECK 53/53 TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
SWEEP PASSED: 53/53 modules
UTC end: 2026-10-02T20:09:03.794835+00:00
```

Exact axiom prints:

| Target | Axioms |
|---|---|
| `Turing.MultiTapeTM.toNDTM_runWith` | `propext, Quot.sound` |
| `Turing.NDTM.HaltsWithin.mono` | `propext, Quot.sound` |
| `Turing.FinNDTM.AcceptsWithin.mono` | `propext, Quot.sound` |
| `Complexity.NTIME.mono` | `propext, Quot.sound` |
| `Complexity.DTIME_subset_NTIME` | `propext, Classical.choice, Quot.sound` |
| `Complexity.NTIME_eq_empty_of_exists_zero` | `propext, Quot.sound` |

```text
'Turing.MultiTapeTM.toNDTM_runWith' depends on axioms: [propext, Quot.sound]
'Turing.NDTM.HaltsWithin.mono' depends on axioms: [propext, Quot.sound]
'Turing.FinNDTM.AcceptsWithin.mono' depends on axioms: [propext, Quot.sound]
'Complexity.NTIME.mono' depends on axioms: [propext, Quot.sound]
'Complexity.DTIME_subset_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NTIME_eq_empty_of_exists_zero' depends on axioms: [propext, Quot.sound]
```

Environment setup used `lake exe cache get`, then narrowed the slow full
cache download to the 25 Mathlib import roots needed by the entire campaign
(912 cached modules; successful completion in `logs/cache-get-targeted.log`).
The bundled standard-library import comes with Lean. No `lake build` was run.
The process sandbox could not locate the Lean executable, so automatic review
approved running compiler checks outside that sandbox. No proof-check attempt
failed; the initial runtime-launch failures occurred before any source edit.

## Delivery and integration

The archive root contains this report, both full modified sources, the six
ordered patches under `patches/`, `fill-ch2-e1-B.bundle`, verification logs,
the axiom-print input, a copy of the module order, and `SHA256SUMS`.

The Git bundle names `refs/heads/complexity/arora-barak-ch1` at the final
commit and requires the exact base commit above. `git bundle verify` succeeds.
Applying all six patches sequentially to a temporary index initialized at
the base reproduces the final Git tree exactly:
`ac5b9c7ce57b59e8f17d61abe7f6b5f694aaac56`.
See `logs/bundle-verify.log` and `logs/patch-replay.log`.

From the extracted archive, verify `sha256sum -c SHA256SUMS`. Integrate the
ordered patch series with `git am -3` in a checkout containing the base,
following the campaign's maintainer integration protocol. `SHA256SUMS`
covers every other archive file; it excludes itself.
