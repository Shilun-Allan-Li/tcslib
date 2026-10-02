# Chapter 2, epoch 1, batch A — completed

All eight assigned proofs are filled. The final direct-Lean sweep passed all
53 modules with zero `error:` diagnostics. The chapter's admitted-declaration
count decreased from 59 to 51. The only admitted dependency of any filled
target is the brief-authorized `Complexity.P_subset_NP`, used by the two
collapse corollaries.

## Provenance

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Base branch: `complexity/arora-barak-ch1`
- Pinned base: `7494522e8826be6b54675307668435afc59c005d`
- Work branch: `fill/ch2-e1-A`
- Delivered commit: `b362f85838b131571cf5af9476c052bd2dc23fc7`
- Delivered tree: `c49f7dd691cb2b0cfa8457018dea10460d61e5d5`
- Binding brief: `briefs/ch2-epoch1-batchA.md` at the pinned base.
- Lean: `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Agent: Codex, single agent; no delegation.

Only these two tracked files changed:

- `TCSlib/Complexity/ClassNP/PolyTime.lean`
- `TCSlib/Complexity/ClassNP/Reductions.lean`

## Targets filled, in the prescribed order

All names below are in namespace `Complexity`.

| # | Target | Proof and relation to the sketch |
|---|---|---|
| 1 | `polyTimeComputable_id` | Uses the Chapter-1 identity machine with degree 1; converts its budget pointwise through `ComputesInTime.mono`. |
| 2 | `PolyTimeComputable.output_length_le` | Keeps the computing machine's own coefficient and degree; identifies its completed output at the budget using `computesInTime_iff`, then applies `MultiTapeTM.output_length_le`. |
| 3 | `PolyTimeComputable.comp` | Proves monotonicity of the second explicit polynomial, invokes `computesFunInTime_comp`, and applies the private budget lemma with degree `max c (c * c')`. No positivity of either degree is assumed. |
| 4 | `PolyTimeReducible.refl` | Uses the identity result and reflexive membership equivalences. |
| 5 | `PolyTimeReducible.trans` | Composes the reduction functions with target 3 and chains the two membership equivalences. |
| 6 | `mem_P_of_polyTimeReducible` | Obtains the target decider with `mem_P_iff`, views it as a total singleton-indicator function, and uses target 3 to perform the timed composition. The reduction equivalence identifies the resulting indicator. `succ_pow_le` supplies the final bound for `mem_P_of_dtime_le`. |
| 7 | `P_eq_NP_of_NPHard_mem_P` | Uses the unchanged `P_subset_NP` in one direction and target 6 in the other. |
| 8 | `NPComplete.mem_P_iff` | Applies target 7 to the hardness half; the reverse direction rewrites the membership half along the class equality. |

Target 6 factors the sketch's timed-composition and intermediate-output analysis
through the newly proved target 3 instead of duplicating the machine-level
argument. Target 3 invokes exactly `FinTM.computesFunInTime_comp`, whose proved
implementation uses the one-symbol-per-step output-length bound. No untimed
composition theorem is used. The target-6 proof-sketch docstring has an appended
paragraph recording this factoring and the final polynomial normalization;
its original statement, sketch text, and attribution are preserved.

## New declarations

Exactly one new declaration, private: `Complexity.comp_time_bound`, in
`PolyTime.lean`. It states the following inequality for arbitrary natural
parameters, including zero coefficients and degrees:

```lean
private lemma comp_time_bound (a C c C' c' n : ℕ) :
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
      a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c')
```

Its docstring gives both the claim and a proof sketch. The bound is specific
to this file's polynomial-composition normalization. There are no new public
declarations and no removals. The scratch verification files are outside the
repository patch and are not additions to its theorem surface.

## Requested shared lemmas

None.

## Escalations

None.

## Statement freeze and scope

`logs/statement-freeze.log` records a nesting-aware comment-stripped comparison
against the pinned base. All 15 existing declaration signatures and the ordered
declaration sequence are unchanged after excluding the new private helper.
The declaration multisets also agree. Imports, option headers, and all AB09
attributions are unchanged. The checker is supplied as
`verification/check_freeze.py`; run it with the repository path as its argument.

Both `HALT_NPHard` and `HALT_not_mem_NP`, including their docstrings and proof
bodies, are byte-identical to the base. Every tracked file outside the two
owned files is unchanged. No out-of-scope admission was filled or removed.

The owned-file policy lint reports **0 FAIL, 0 WARN**; `git diff --check` passes.

## Verification

The dependency setup used `lake exe cache get`; the slow whole-Mathlib fetch
was stopped and completed with the cache tool's supported module arguments
covering every external import of the 53-module sweep. The pinned toolchain
and dependency revisions were not changed. Campaign checking used only the
direct-Lean script, never a `lake build` campaign build.

The bootstrap checked all 53 modules at the unchanged base: zero errors,
59 admitted-declaration warnings. Each proof edit was followed by its owned
file check. After completing `PolyTime.lean`, the intervening `NP`, `CoNP`, and
`EXP` modules were refreshed before filling `Reductions.lean`.

The final sweep checked the committed result in the exact order in
`scripts/ab_ch1_module_order.txt`, invoking
`bash scripts/lean_check_tree.sh "$m"` once per module and stopping on any
failure. Every invocation exited 0 and produced a fresh `.olean`. This covers
every downstream module. The raw log is `logs/final-sweep.log`; the exact
order list is also included in `verification/`.

- Final sweep: **53/53 pass; zero errors; 51 admitted declarations**.
- `PolyTime.lean`: zero admitted declarations.
- `Reductions.lean`: only the two unchanged HALT admissions.
- All other remaining admissions are outside this batch.
- Existing linter warnings in unchanged modules are retained in the raw logs.

Final sweep tail:

```text
RESULT 49/53 exit=0 seconds=1.920
CHECK 50/53 TCSlib/Complexity/Uncomputability
RESULT 50/53 exit=0 seconds=1.713
CHECK 51/53 TCSlib/Complexity/Formulas
RESULT 51/53 exit=0 seconds=1.376
CHECK 52/53 TCSlib/Complexity/CookLevin
RESULT 52/53 exit=0 seconds=1.611
CHECK 53/53 TCSlib/Complexity/ClassNP
RESULT 53/53 exit=0 seconds=1.445
PASS: 53/53 modules; seconds=197.738
UTC end: 2026-10-02T20:09:12.875060+00:00
```

## Axiom checks

`verification/Axioms.lean` was run against the final fresh olean tree.
`logs/axioms.log` contains all eight `#print axioms` results, an additional
print for `P_subset_NP`, and checked traversal of the kernel environment's
transitive dependencies.

After rerunning the full sweep with the pinned Lean on `PATH`, reproduce these
checks with `bash verification/run_axioms.sh /path/to/tcslib` from the unpacked
archive.

| Targets | Exact axiom set | Declarations directly using `sorryAx` in the transitive dependency closure |
|---|---|---|
| Targets 1–6 | `propext`, `Classical.choice`, `Quot.sound` | None |
| `P_eq_NP_of_NPHard_mem_P` | `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` | Only `Complexity.P_subset_NP` |
| `NPComplete.mem_P_iff` | `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` | Only `Complexity.P_subset_NP` |

The traversal checks both declaration types and values, with opaque values
included, and errors if any other directly admitted declaration is found.
Thus the two authorized occurrences are independently checked rather than
inferred only from the top-level axiom lists.

## Delivery and integration

The archive root contains this report, both full modified source files at
their repository-relative paths, one `git format-patch` patch under `patches/`,
the branch bundle, verification inputs, raw logs, and `SHA256SUMS`.

The bundle is **incremental** and requires base commit
`7494522e8826be6b54675307668435afc59c005d`; its advertised branch is
`refs/heads/fill/ch2-e1-A` at the delivered commit. `git bundle verify` passes.
The patch applies cleanly to an index initialized from the pinned base and
reproduces the delivered tree exactly (`logs/patch-replay.log`).

From an unpacked archive, verify `sha256sum -c SHA256SUMS`. Every payload file
is covered except `SHA256SUMS` itself. The intended integration is `git am -3`
of the single patch, preserving its Codex authorship, into the maintainer's
campaign branch. No remote branch was pushed and no PR was created.

## Completion checklist

- [x] Eight targets filled in order and individually checked.
- [x] All new declarations listed; no new public declarations.
- [x] Requested shared lemmas and escalations recorded.
- [x] Full 53-module final sweep and axiom-print log included.
- [x] Both authorized `sorryAx` dependencies checked to have only the permitted root.
- [x] Diff restricted to the two owned files; existing statements frozen.
- [x] Full source files, patch series, verified bundle, report, logs, and checksums supplied.
