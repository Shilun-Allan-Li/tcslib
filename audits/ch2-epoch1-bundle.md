# External audit pack — Chapter 2 fill campaign, Epoch 1

Audits the integrated epoch-1 state on `complexity/arora-barak-ch1`: nine
agent commits (`07cf205a` … `b5ff4c75`) on base `7494522e`, plus the
maintainer integration commit carrying this pack. **First fill epoch of the
Chapter-2 campaign** (`workflow.md` §4; partition:
`AroraBarakChapter2Plan.md` §4): four parallel batches filled **27 of the 59
audited-true admissions** — the polynomial-time calculus (1A, 8), the
nondeterministic run calculus (1B, 6), complementation and the easy
inclusions (1C, 6), and the formula mathematics (1D, 7). The statement
layer was audited across the four closed phase gates; **this round audits
proofs and their new private helpers**, not statements. Gate closes on zero
blockers/majors. Record findings in `audits/ch2-epoch1-findings.md`.

## Maintainer-side integration attestations (verify or challenge)

1. **Checksums and provenance.** All four archives' `SHA256SUMS` verified
   in full (26/26, 26/26, 22/22, 18/18). Every batch pinned base
   `7494522e`; patch replay reproduced each delivered tree per the agents'
   own logs, and `git am -3` applied all nine commits cleanly here,
   authorship preserved (author: Codex).
2. **Statement freeze, independently audited.** Across the entire
   integration diff (`7494522e..b5ff4c75`), the deleted lines are **exactly
   the 27 `sorry` lines plus one docstring closing line** — the disclosed,
   rule-2-sanctioned sketch appendix on `mem_P_of_polyTimeReducible`
   (append-only; the hunk is reproduced in the integration record). No
   other pre-existing line changed.
3. **Declaration drift: none public.** Ordered public declaration lists
   per owned file are identical to base; zero removals; additions are
   exactly the **19 private helpers** the reports declare (1A: 1 —
   `comp_time_bound`; 1D: 18, itemized with contracts in its report;
   1B/1C: none). The appendix-cited `succ_pow_le` pre-exists
   (`ClassP/ModelInvariance.lean`, phase 1).
4. **Elaboration.** Full fresh-olean 53-module sweep at the integrated
   tree (`scripts/ab_ch1_module_order.txt`, Lean 4.25.0 / mathlib
   `029db123ddaa`): zero `error:` lines, exactly **32 admission warnings**
   (59 − 27). Log: `audits/logs/ch2-e1-sweep-53mod.log`.
5. **Axiom prints.** All 27 filled targets at the integrated tree
   (`audits/logs/ch2-e1-axioms.log`): **zero `sorryAx`** — the two
   brief-sanctioned `sorryAx` carriers of batch 1A are clean after
   integration, since 1C's `P_subset_NP` fill closes their one admitted
   dependency. Footprints: 16 targets `[propext, Classical.choice,
   Quot.sound]`, 10 targets `[propext, Quot.sound]`, and
   `Std.Sat.CNF.evalDNF_dual` axiom-free.
6. **Policy.** Style lint: 0 FAIL / 0 WARN on `ClassNP/` and `Formulas/`;
   `TuringMachine/` keeps its six pre-existing Chapter-1 size WARNs,
   unchanged. All docstrings and attributions intact.

## Maintainer dispositions taken this epoch (review requested)

* **D1 — axiom-footprint subsets accepted.** The briefs said to expect
  "exactly" the standard triple; batches 1B (five targets) and 1D (six)
  escalated honestly that their proofs use *proper subsets* of it. Subsets
  are accepted a fortiori — the brief wording was the defect, and the E2
  briefs will read "at most the standard triple; `sorryAx` never, except
  where sanctioned".
* **D2 — branch-name deviation noted, cosmetic.** Batches B/C/D worked
  under the campaign branch's own name rather than the brief's
  `fill/ch2-e1-X`; integration is by patch series, so nothing turns on it.
* **D3 — shared-lemma request deferred.** 1D requests promoting its
  generic `foldr_max_le_of_forall` to a shared list utility; the private
  copies compile standalone, so promotion is deferred to a later serial
  merge and tracked in `backlog.md` §2.

## What is under audit

Per batch: the proofs of the 27 targets and the 19 private helpers, against
the audited statements (frozen; re-verified above) and the audited sketches
(the in-file routes plus each brief's amplifications — the briefs are in
`briefs/ch2-epoch1-batch{A,B,C,D}.md`, committed at the base). Priorities:

1. **1A's `comp_time_bound`** — the one place the composition exponent
   arithmetic (`max c (c·c')`, phase-1 finding 7) lives; blind-rederive the
   inequality, including zero coefficients and degrees.
2. **1D's parser round trip** — the fuel-≥ strengthenings
   (`parseClause_serializeClause`, `parseClauses_serialize`) and the
   additive consumed-prefix accounting in the `numVars` bounds; check the
   fuel-adequacy side conditions actually discharge at the instantiation.
3. **1B's truncation direction** in `NTIME.mono` — the backward
   acceptance transfer is the one place the sketch's prefix argument could
   have been weakened; confirm the proved form preserves
   output-exactly-`[true]`.
4. **1C's `compl_mem_P`** — timed composition only (finding 4); confirm
   no untimed route slipped in, and that the budget absorption matches the
   explicit-polynomial discipline.
5. **Helper hygiene** — the 19 privates: contracts match their docstrings;
   nothing deserves public status without flagging; no helper restates an
   audited statement in disguise.
6. The four agent reports (attached verbatim) — challenge any attestation
   of theirs that the maintainer layer above did not independently cover.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch2-epoch1-findings.md`; this pack is immutable once sent.

## ===== audits/ch2-epoch1-agent-reports/batchA.md =====

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

## ===== audits/ch2-epoch1-agent-reports/batchB.md =====

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

## ===== audits/ch2-epoch1-agent-reports/batchC.md =====

# Chapter 2, Epoch 1, Batch C

**Complete: all six targets filled and verified in the prescribed order.**

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Base: `7494522e8826be6b54675307668435afc59c005d`.
- Final commit: `c585da049fbd1fa18883034f0397cbe9bfcf921b`.
- Work performed on `complexity/arora-barak-ch1`, as requested in the follow-up.
  The delivery alias `fill/ch2-e1-C` points to the same final commit; the working
  branch remains `complexity/arora-barak-ch1`.

## Targets versus the frozen sketches

| Target | Completed proof |
|---|---|
| `P_subset_NP` | Uses coefficient and degree zero and the original language as verifier; length zero forces the empty certificate, reducing the equivalence to identity. |
| `compl_mem_P` | Reads the decider pointwise as a singleton-indicator function, applies the fixed Boolean postprocessor through **timed** composition, and absorbs its explicit budget using `mem_P_of_dtime_le`. |
| `mem_coNP_iff_forall` | Negates the certificate quantifier and complements the verifier in both directions, preserving the same coefficient and degree. |
| `P_subset_NP_inter_coNP` | Combines the empty-certificate inclusion with complementation of the original polynomial-time language. |
| `NP_eq_coNP_of_P_eq_NP` | Proves both set inclusions by rewriting the assumed class equality and using complement closure; the reverse direction complements twice. |
| `P_subset_EXP` | Uses `Nat.lt_two_pow_self`, `DTIME.mono`, and absorption of the factor two into the existing time constant. |

## Declarations, requests, and scope

- New public declarations: **none**. New private declarations: **none**.
- Removed declarations: **none**. Requested shared lemmas: **none**.
- Campaign escalations: **none**. Sketch appendices: **none**.
- The diff touches exactly `ClassNP/NP.lean`, `ClassNP/CoNP.lean`, and
  `ClassNP/EXP.lean`: 73 inserted lines and six removed `sorry` lines.
- Restoring only the six target proof bodies reproduces each entire original
  file byte-for-byte. Thus all signatures, definitions, imports, option headers,
  docstrings, attributions, and other proofs are unchanged.
- The owned files retain exactly the three out-of-scope admissions:
  `mem_NP_iff_exists_length_le`, `NP_subset_EXP`, and `EXP_subset_NEXP`.
  Every other batch's sources are untouched.

## Verification

- Lean **4.25.0**, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**; tracked dependency source is clean.
- Dependency setup used `lake exe cache get`, restricted after a slow full-cache
  attempt to all 25 direct Mathlib imports of the prescribed order list
  (912 transitive cached modules). The official compiler ran natively because
  the sandbox launcher failed to locate the application. No compiler or
  verification-script modifications were made; `lake build` was never invoked.
- Initial bootstrap: **53 successful module checks, zero `error:` lines,
  59 admission warnings**.
- Each target edit was checked with `scripts/lean_check_tree.sh`, followed by
  every later module in the prescribed order. Successful logs are included.
- Final sweep at the final commit: **53 successful checks, 53 fresh nonempty
  `.olean` files, zero `error:` lines**, using a previously nonexistent output
  directory. Exactly **53 admission warnings** remain: the original 59 minus
  these six targets, all outside this batch.
- All six axiom prints below came from that final output tree and contain
  exactly the required standard triple, with no `sorryAx`.
- Owned-file style lint: **zero FAIL, zero WARN**. `git diff --check` passes.
- The incremental git bundle verifies against the stated base. Replaying the
  format-patch series on the base's three files reproduces the committed and
  packaged sources byte-for-byte.

Final sweep tail:

```text
BEGIN TCSlib/Complexity/ClassP
PASS TCSlib/Complexity/ClassP
BEGIN TCSlib/Complexity/Uncomputability
PASS TCSlib/Complexity/Uncomputability
BEGIN TCSlib/Complexity/Formulas
PASS TCSlib/Complexity/Formulas
BEGIN TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
BEGIN TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
SWEEP COMPLETE: 53 modules
```

Complete axiom-print log:

```text
'Complexity.P_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.compl_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_coNP_iff_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_NP_inter_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NP_eq_coNP_of_P_eq_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_EXP' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Archive contents

`REPORT.md`; the three full sources under their repository-relative paths;
`patches/` containing the one-commit `git format-patch` series;
`fill-ch2-e1-C.bundle`; `logs/` containing the bootstrap, successful per-target
checks, final sweep, axiom prints, scope/style checks, and patch/bundle checks;
`verification/` containing the axiom-print input, 53-module order, and pins;
and `SHA256SUMS` covering every other archive member.

The bundle is incremental and requires the base commit listed above. The patch
series is ready for the campaign's `git am -3` integration. After extraction,
`sha256sum -c SHA256SUMS` verifies all packaged files.

## ===== audits/ch2-epoch1-agent-reports/batchD.md =====

# Chapter 2, epoch 1, batch D

All seven assigned proofs are filled. Only the three owned Lean files changed.
The audited public signatures, definitions, declaration order, and existing
comments are preserved. One verification-policy exception is escalated below:
six targets use a proper subset of the brief's exact expected axiom triple.

## Revision and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Base: `7494522e8826be6b54675307668435afc59c005d`.
- Result: `aebe3d9b6f81b93767c168746e2f0aa53d8acb46`.
- Working and bundle branch: `complexity/arora-barak-ch1`, following the user's
  subsequent explicit instruction. This supersedes the brief's requested
  `fill/ch2-e1-D` working-branch name.
- Delivery: ZIP only; no PR or remote push. One format-patch commit and an
  incremental git bundle against the stated base are included.
- Toolchain: Lean 4.25.0; Mathlib commit
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Execution: one agent, no delegation. No `lake build` invocation.

The source diff consists of:

1. `TCSlib/Complexity/Formulas/CNF.lean`
2. `TCSlib/Complexity/Formulas/CNFEncoding.lean`
3. `TCSlib/Complexity/Formulas/DNF.lean`

## Targets versus the prescribed sketches

| Target | Completion and proof route |
|---|---|
| `Complexity.eval_congr_of_lt_numVars` | Filled. An occurring variable contributes its successor to the flattened list; membership bounds that successor by the maximum fold. Apply core's evaluation congruence. |
| `Complexity.exists_cnf_boolFun` | Filled. List one excluding clause for each falsifying assignment from the filtered finite universe. Prove the excluding-clause equivalence, then separately prove the variable, clause-count, width, and evaluation conjuncts. No positive-arity assumption is used. |
| `Std.Sat.CNF.parse_serialize` | Filled. Prove the specified unary-run identity, suffix-carrying literal round trip, clause round trip, and formula round trip; instantiate the last at the empty suffix. Both recursive round trips quantify over **every fuel at least the serialized fragment length**, exactly as required. |
| `Std.Sat.CNF.decode_serialize` | Filled. Apply the parser round trip and reduce `Option.getD` on `some`. |
| `Std.Sat.CNF.numVars_decode_le` | Filled. Prove exact literal consumption and suffix-aware bounds for successful clause/formula parsing; bound the maximum fold termwise. Failed parses and nonempty final remainders reduce to the empty fallback. |
| `Std.Sat.CNF.evalDNF_dual` | Filled. Induct on literals to prove the clause identity, checking the two Boolean values of each assignment and polarity; then induct on clauses and apply Boolean De Morgan. |
| `Std.Sat.CNF.dnfTautology_dual_iff` | Filled. Rewrite the pointwise identity, Boolean negation, and negated existential. |

There is **no deviation from the required fuel-strengthening form**. For the
variable-bound proof, the consumed-prefix inequality is written additively:
each variable contribution plus the final remainder length is at most the
input length. The accompanying remainder bound makes this equivalent to
bounding the contribution by input length minus remainder length. This avoids
truncated-subtraction bookkeeping without changing the sketch's content.

Original docstrings and attribution text were retained verbatim. New helper
docstrings describe their contracts; the longer inductions have proof sketches.
No existing sketch appendix was changed or added.

## Every new declaration

All 18 additions are private: 16 theorems and two definitions. There are no new
public declarations, renamed declarations, or removals.

### `CNF.lean`, namespace `Complexity`

| Line | Name | Contract |
|---|---|---|
| 112 | `le_foldr_max_of_mem` | A natural-number list member is at most the list's maximum fold with initial value zero. |
| 146 | `foldr_max_le_of_forall` | A common upper bound for all list members bounds that maximum fold. |
| 155 | `falsifyingClause` | Definition: the `List.ofFn` clause containing each finite variable with polarity opposite to the given assignment. |
| 160 | `falsifyingClause_eval_false` | That clause evaluates false exactly when the total assignment restricts to the given finite assignment. |
| 177 | `falsifyingCNF` | Noncomputable definition: map the excluding-clause construction over the list of all falsifying assignments. |
| 181 | `falsifyingCNF_numVars` | The constructed formula's variable measure is at most its arity. |
| 193 | `falsifyingCNF_length` | The constructed formula has at most two to the arity clauses. |
| 202 | `falsifyingCNF_width` | Every constructed clause has width at most the arity; the proof uses its exact length. |
| 213 | `falsifyingCNF_eval` | Evaluation of the constructed formula agrees with the given function on the restricted assignment. |

### `CNFEncoding.lean`, namespace `Std.Sat.CNF`

| Line | Name | Contract |
|---|---|---|
| 169 | `takeTrues_replicate` | Reading a run of `k + 1` true bits followed by false returns exactly that count and preserves the false-prefixed suffix. |
| 179 | `parseLit_serializeLit` | A serialized literal followed by any suffix parses to that literal and suffix. |
| 191 | `parseClause_serializeClause` | A serialized clause followed by any suffix parses correctly with any fuel at least its serialized length. |
| 223 | `parseClauses_serialize` | The corresponding suffix-carrying formula round trip, again with any fuel at least its serialized length. |
| 280 | `takeTrues_length` | The counted run length plus returned remainder length equals the input length. |
| 293 | `parseLit_length` | Successful literal parsing consumes exactly its variable index plus three bits. |
| 312 | `parseClause_bounds` | On success, remainder length is at most input length; every returned variable index plus one, plus remainder length, is at most input length. |
| 373 | `parseClauses_bounds` | The same remainder and variable bounds for every literal in every returned clause. |
| 431 | `numVars_le_of_literal_bounds` | A common upper bound for all variable-index successors bounds `numVars`. |

`DNF.lean` adds no declarations. Its clause induction is a local `have` inside
the existing target. Local `have` bindings elsewhere are likewise not new
environment declarations.

## Requested shared lemmas

For a future serial merge, consider promoting the generic maximum-fold upper
bound `foldr_max_le_of_forall` to a shared list utility. This batch keeps its
private copy in `CNF.lean` and a local copy inside
`CNFEncoding.numVars_le_of_literal_bounds`. No shared-file modification is
needed to compile or integrate this batch.

## Verification

The final fresh-tree sweep completed successfully at result commit
`aebe3d9b6f81b93767c168746e2f0aa53d8acb46`: **53/53 modules passed,
zero `error:` lines, and 52 expected out-of-scope admission warnings**.
The axiom prints below were run against that same fresh output tree.

The patch was replayed in a clean local checkout of the base. Its resulting
Git tree exactly matches the result commit, and all three packaged source
files match that replay byte-for-byte. Bundle verification passed. The
original working tree is clean. Full evidence is in `verification/`.

The admission inventory decreases from 59 to 52, exactly the seven assigned
targets. Every remaining admission is outside the owned files. The source
freeze script also checks the ordered public declaration list, its multiset,
unchanged definition bodies, preservation of original block comments, and the
absence of admissions or new unsafe/axiom mechanisms in the owned files.

Scoped style lint reports **0 FAIL, 0 WARN**. Its displayed private-declaration
count omits the `private noncomputable def` because of its matcher order; the
dedicated source inventory correctly records all 18 additions.

The initial cache setup was narrowed to the campaign's direct Mathlib imports
and their dependency closure. A shared-cache temporary-file conflict was
resolved by using a private cache directory; the final cache operation
completed successfully. Bootstrap and final verification use the repository's
`lean_check_tree.sh`, which removes each old output and checks exit status,
error diagnostics, and the existence of a fresh output. The final sweep uses
a separate initially absent output tree.

### Actual axiom footprints

```text
'Complexity.eval_congr_of_lt_numVars' depends on axioms: [propext, Quot.sound]
'Complexity.exists_cnf_boolFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Std.Sat.CNF.parse_serialize' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.decode_serialize' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.numVars_decode_le' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.evalDNF_dual' does not depend on any axioms
'Std.Sat.CNF.dnfTautology_dual_iff' depends on axioms: [propext, Quot.sound]
```

### Final sweep tail

```text
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
PASS TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
PASS TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
PASS TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
MODULES_PASSED 53
END_UTC 2026-10-02T20:16:52Z
```

## Escalations

**E1 — exact axiom-list wording.** The brief says to expect exactly
`[propext, Classical.choice, Quot.sound]` for every target. Only
`exists_cnf_boolFun` needs all three. Five targets need only `propext` and
`Quot.sound`; `evalDNF_dual` is axiom-free. Thus all seven use **only** the
permitted standard axioms, and none uses `sorryAx`, but six do not meet the
literal exact-list expectation. The raw output is preserved. Maintainer
disposition requested: accept subsets of the standard triple for this gate.
No proof was padded with unused axiom dependencies to manufacture the list.

There are no mathematical or statement-freeze escalations. The working-branch
change above follows the user's direct instruction and requires no additional
permission.

## Contents and integration

- Full modified sources appear at their repository-relative paths.
- `patches/0001-Fill-Chapter-2-epoch-1-batch-D-formula-proofs.patch` is the
  complete one-commit series against the pinned base.
- `fill-ch2-e1-D.bundle` contains the result branch and requires the pinned base.
- `verification/` contains the final sweep, axiom output and print source,
  frozen module order, style/freeze checks, environment record, and delivery
  verification evidence.
- `SHA256SUMS` covers every other archive member.

From the extracted archive, run `sha256sum -c SHA256SUMS`. In a clean integration
checkout containing the pinned base, use `git bundle verify` on the bundle
and `git am -3` on the patch. The supplied sources must match the resulting
files. Run `verification/final_sweep.sh` from that repository root after cache
setup; it intentionally requires an absent final-output directory.

## ===== TCSlib/Complexity/ClassNP/PolyTime.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time computable functions

The function class `FP` underlying every Karp reduction of [AB09, ch. 2]: a function
`f : {0,1}* → {0,1}*` is polynomial-time computable when some machine of this
development computes it within a bound `C · (n + 1)^c`. This module fixes the
polynomial normal form (`Complexity.PolyBound`), the class
(`Complexity.PolyTimeComputable`), and the closure calculus that the chapter's
reductions assemble with — identity, composition, and the output-length bound.

## Design

* **Normal form `C · (n + 1)^c`.** Chapter 1's `P` uses `n^c + 1`; for *function*
  bounds the `(n + 1)^c` shape is closed under the compositions the calculus
  performs and is a monotone majorant by construction (both forms bound the same
  class, by `Complexity.succ_pow_le` and its converse direction). The choice is a
  recorded phase-1 design question.
* **Closure lemmas are need-driven.** Only the combinators the mandatory core
  consumes are stated here; concatenation, constant prefixing, and unary padding
  arrive with the phases that first use them (plan §2), never speculatively.

## Main definitions

* `Complexity.PolyBound` — `p` is bounded by `C · (n + 1)^c`.
* `Complexity.PolyTimeComputable` — `f` is computed by some machine within a
  polynomial bound ([AB09]'s implicit class FP).

## Main results

* `Complexity.polyTimeComputable_id` — the identity is polynomial-time computable.
* `Complexity.PolyTimeComputable.output_length_le` — a polynomial-time computable
  function has polynomially bounded output length.
* `Complexity.PolyTimeComputable.comp` — closure under composition
  [AB09, proof of Theorem 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7 and Theorem 2.8.)
-/

namespace Complexity

open Turing

/-- The bound `p : ℕ → ℕ` is *polynomially bounded*: `p n ≤ C · (n + 1)^c` for some
constants `C, c`. A **numerical helper only**: the *majorant* `C (n+1)^c` is
monotone, but `p` itself need be neither monotone nor computable — which is
exactly why this predicate never appears in a class definition (phase-1 audit,
finding 1: an abstract length function can smuggle undecidable information
through length arithmetic). Class definitions use explicit formulas instead. -/
def PolyBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * (n + 1) ^ c

/-- A function on binary strings is *polynomial-time computable* when some finite
binary-alphabet machine computes it within `C · (n + 1)^c` steps on inputs of
length `n` — the function class FP implicit throughout [AB09, ch. 2]. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c

/-- The identity function is polynomial-time computable.

**Proof sketch.** `Turing.FinTM.computesFunInTime_id` supplies a machine computing
`id` within a linear bound; enlarge the bound into the `C · (n + 1)^c` normal form
pointwise via `Turing.FinTM.ComputesInTime.mono` (there is no
`ComputesFunInTime`-level monotonicity lemma — phase-1 audit, finding 9). -/
theorem polyTimeComputable_id : PolyTimeComputable id := by
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_id
  refine ⟨M, C, 1, fun x => (hM x).mono ?_⟩
  simp only [Nat.pow_one]
  exact Nat.le_refl _

/-- A polynomial-time computable function has polynomially bounded output length:
`|f x| ≤ C · (|x| + 1)^c` for some constants `C, c` uniform over all inputs.

**Proof sketch.** A machine emits at most one symbol per step
(`Turing.MultiTapeTM.output_length_le`), so the completed output of a computation
within `t` steps has length at most `t`; instantiate `t` at the machine's own
polynomial budget on each input. -/
theorem PolyTimeComputable.output_length_le {f : List Bool → List Bool}
    (h : PolyTimeComputable f) :
    ∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c := by
  obtain ⟨M, C, c, hM⟩ := h
  refine ⟨C, c, fun x => ?_⟩
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
  simpa only [hout] using M.tm.output_length_le x (C * (x.length + 1) ^ c)

/-- The timed-composition budget is bounded by a polynomial of degree
`max c (c * c')`, uniformly in all natural coefficients, degrees, and lengths.

**Proof sketch.** Since `(n+1)^c ≥ 1`, the inner argument is at most
`(C+1)(n+1)^c`. Raising to `c'` gives the second term degree `c*c'`.
Enlarge both degrees to their maximum, absorb the constant term using
`(n+1)^(max c (c*c')) ≥ 1`, and distribute the common power. -/
private lemma comp_time_bound (a C c C' c' n : ℕ) :
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
      a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have hone : 1 ≤ (n + 1) ^ c := Nat.one_le_pow c (n + 1) hpos
  have hfirst : (n + 1) ^ c ≤ (n + 1) ^ max c (c * c') :=
    Nat.pow_le_pow_right hpos (Nat.le_max_left _ _)
  have hsecond : (C * (n + 1) ^ c + 1) ^ c' ≤
      (C + 1) ^ c' * (n + 1) ^ max c (c * c') := by
    calc
      (C * (n + 1) ^ c + 1) ^ c' ≤ ((C + 1) * (n + 1) ^ c) ^ c' :=
        Nat.pow_le_pow_left (by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add_left hone _) c'
      _ = (C + 1) ^ c' * (n + 1) ^ (c * c') := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ (C + 1) ^ c' * (n + 1) ^ max c (c * c') :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (Nat.le_max_right _ _))
  calc
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
        a * (C * (n + 1) ^ max c (c * c') +
          C' * ((C + 1) ^ c' * (n + 1) ^ max c (c * c')) +
          (n + 1) ^ max c (c * c')) :=
      Nat.mul_le_mul_left a (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left C hfirst) (Nat.mul_le_mul_left C' hsecond))
        (Nat.one_le_pow _ _ hpos))
    _ = a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.one_mul]

/-- Polynomial-time computable functions are closed under composition
[AB09, proof of Theorem 2.8: polynomials compose].

**Proof sketch.** Let `Mf` compute `f` within `C · (n + 1)^c` and `Mg` compute `g`
within `C' · (n + 1)^c'`. `Turing.FinTM.computesFunInTime_comp` composes the
machines with a factor-`2` overhead, running `Mg` on the intermediate output
`f x`, whose length is at most `C · (n + 1)^c` because a machine emits at most one
symbol per step (`Turing.MultiTapeTM.output_length_le`). The total budget
`2 · (C (n+1)^c + C' (C (n+1)^c + 1)^{c'} + 1)` is again of the form
`C'' · (n + 1)^{c''}` with `c'' = max c (c · c')` — the `max` covers `c' = 0`,
where the first machine's term still grows as `(n+1)^c` (phase-1 audit,
finding 7); since `(n+1)^c ≥ 1`, the whole budget is absorbed as
`a (C + C'(C+1)^{c'} + 1) (n+1)^{max c (c·c')}`. This is Theorem 2.8's
polynomial-composition observation. -/
theorem PolyTimeComputable.comp {f g : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hf : PolyTimeComputable f) :
    PolyTimeComputable (g ∘ f) := by
  obtain ⟨Mf, C, c, hf⟩ := hf
  obtain ⟨Mg, C', c', hg⟩ := hg
  have hmono : Monotone (fun n : ℕ => C' * (n + 1) ^ c') := by
    intro m n hmn
    exact Nat.mul_le_mul_left C' (Nat.pow_le_pow_left (Nat.add_le_add_right hmn 1) c')
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_comp hf hg hmono
  refine ⟨M, a * (C + C' * (C + 1) ^ c' + 1), max c (c * c'),
    fun x => (hM x).mono ?_⟩
  exact comp_time_bound a C c C' c' x.length

end Complexity

## ===== TCSlib/Complexity/ClassNP/Reductions.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Karp reductions, NP-hardness, and NP-completeness

[AB09, §2.2, Definition 2.7]: `L ≤ₚ L'` when a polynomial-time computable
function maps members to members and non-members to non-members; `L'` is
`NP`-hard when every `NP` language reduces to it, `NP`-complete when it is also
in `NP`. Theorem 2.8 packages the basic laws: transitivity, and the collapse
consequences of an `NP`-hard language landing in `P`.

The module closes with [AB09, Exercise 2.8], the chapter's bridge back to
Chapter 1: `HALT` is `NP`-hard but — being undecidable — not in `NP`, hence not
`NP`-complete.

## Main definitions

* `Complexity.PolyTimeReducible` (scoped notation `≤ₚ`) — [AB09, Definition 2.7].
* `Complexity.NPHard`, `Complexity.NPComplete` — [AB09, Definition 2.7].

## Main results

* `Complexity.PolyTimeReducible.refl`, `Complexity.PolyTimeReducible.trans` —
  [AB09, Theorem 2.8.1 and Exercise 2.9].
* `Complexity.mem_P_of_polyTimeReducible` — downward closure of `P` under `≤ₚ`
  [AB09, Figure 2.1].
* `Complexity.P_eq_NP_of_NPHard_mem_P` — [AB09, Theorem 2.8.2].
* `Complexity.NPComplete.mem_P_iff` — [AB09, Theorem 2.8.3].
* `Complexity.HALT_NPHard`, `Complexity.HALT_not_mem_NP` — [AB09, Exercise 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7, Theorem 2.8,
  pp. 42-44; Exercises 2.8-2.9.)
-/

namespace Complexity

open Turing

/-- **Polynomial-time Karp reducibility** [AB09, Definition 2.7]: `L ≤ₚ L'` when
some polynomial-time computable `f` satisfies `x ∈ L ↔ f x ∈ L'` for every
string `x`. -/
def PolyTimeReducible (L L' : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyTimeReducible

/-- Karp reducibility is reflexive [AB09, Exercise 2.9]: the identity reduces
`L` to itself.

**Proof sketch.** `Complexity.polyTimeComputable_id` with the trivial membership
equivalence. -/
theorem PolyTimeReducible.refl (L : Language Bool) : L ≤ₚ L := by
  exact ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- **Karp reducibility is transitive** [AB09, Theorem 2.8.1].

**Proof sketch.** Compose the two reduction functions with
`Complexity.PolyTimeComputable.comp` and chain the membership equivalences —
the polynomial-composition observation of [AB09]'s proof lives inside `comp`. -/
theorem PolyTimeReducible.trans {L L' L'' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ≤ₚ L'') : L ≤ₚ L'' := by
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨g, hg, hL'⟩ := h'
  exact ⟨g ∘ f, hg.comp hf, fun x => (hL x).trans (hL' (f x))⟩

/-- **`P` is closed downward under `≤ₚ`** [AB09, Figure 2.1 and the remark after
Definition 2.7]: if `L ≤ₚ L'` and `L' ∈ P` then `L ∈ P`.

**Proof sketch.** Compose the reduction machine with a polynomial-time decider of
`L'` (`Complexity.mem_P_iff`, read pointwise as computing the total
singleton-indicator function) via the **timed** total composition
`Turing.FinTM.computesFunInTime_comp` — the untimed `exists_comp_partial`
carries no time bound (phase-1 audit, finding 4). The intermediate string `f x`
has polynomially bounded length
(`Complexity.PolyTimeComputable.output_length_le`), so the decider's budget on
it is polynomial in `|x|` by monotonicity of the explicit polynomial, and the
composite decides `L` since `x ∈ L ↔ f x ∈ L'`; return through
`Complexity.mem_P_of_dtime_le`.

The implementation packages the decider as a polynomial-time computable
singleton-indicator function and applies `PolyTimeComputable.comp`, whose
proof invokes the timed interface above with its intermediate-output bound.
Finally `succ_pow_le` converts the resulting `(n+1)^d` budget to the
`n^d+1` form consumed by `mem_P_of_dtime_le`. -/
theorem mem_P_of_polyTimeReducible {L L' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ∈ P) : L ∈ P := by
  classical
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h'
  have hg : PolyTimeComputable (fun y => [MultiTapeTM.indicator (L' : Set (List Bool)) y]) :=
    ⟨M, C, c, hM⟩
  obtain ⟨S, A, d, hS⟩ := hg.comp hf
  have hdec : S.DecidesInTime L (fun n => A * (n + 1) ^ d) := by
    intro x
    have hi : MultiTapeTM.indicator (L : Set (List Bool)) x =
        MultiTapeTM.indicator (L' : Set (List Bool)) (f x) := by
      simp only [MultiTapeTM.indicator, hL x]
    simpa only [Function.comp_apply, hi] using hS x
  refine mem_P_of_dtime_le (T := fun n => A * (n + 1) ^ d)
    ⟨1, S, ?_⟩ (A * 2 ^ d) d ?_
  · intro x
    simpa only [Nat.one_mul] using hdec x
  · intro n
    calc
      A * (n + 1) ^ d ≤ A * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul_left A (succ_pow_le n d)
      _ = A * 2 ^ d * (n ^ d + 1) := (Nat.mul_assoc _ _ _).symm

/-- **`NP`-hardness** [AB09, Definition 2.7]: every `NP` language Karp-reduces to
`L`. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, L' ≤ₚ L

/-- **`NP`-completeness** [AB09, Definition 2.7]: `L` is in `NP` and `NP`-hard. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

/-- **If an `NP`-hard language is in `P`, then `P = NP`** [AB09, Theorem 2.8.2].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; conversely every
`L' ∈ NP` reduces to the `NP`-hard `L ∈ P`, so `L' ∈ P` by
`Complexity.mem_P_of_polyTimeReducible`. -/
theorem P_eq_NP_of_NPHard_mem_P {L : Language Bool}
    (hL : NPHard L) (h : L ∈ P) : P = NP := by
  apply Set.Subset.antisymm P_subset_NP
  intro L' hL'
  exact mem_P_of_polyTimeReducible (hL L' hL') h

/-- **An `NP`-complete language is in `P` iff `P = NP`** [AB09, Theorem 2.8.3].

**Proof sketch.** (⇒) is `Complexity.P_eq_NP_of_NPHard_mem_P` on the hardness
half; (⇐) rewrites `L ∈ NP` along `P = NP`. -/
theorem NPComplete.mem_P_iff {L : Language Bool} (hL : NPComplete L) :
    L ∈ P ↔ P = NP := by
  constructor
  · exact P_eq_NP_of_NPHard_mem_P hL.2
  · intro h
    rw [h]
    exact hL.1

/-- **`HALT` is `NP`-hard** [AB09, Exercise 2.8] — for **every** representation
scheme, effective or not: the reduction embeds one *fixed* code, so only
`Turing.MachineCode.decode_encode` is used (phase-1 audit, finding 11; compare
Chapter 1's Theorem 1.10/1.11 split, where only the evaluator direction needs
effectivity).

**Proof sketch** (the audit's repaired construction, finding 6 — the earlier
divergent-searcher route is unusable because
`Turing.FinTM.one_work_tape_binary` requires a *total* function). Fix `L ∈ NP`.
(1) Obtain a **total** exponential-time decider `D` of `L` from the repaired
`Complexity.NP_subset_EXP`. (2) Normal-form `D` with
`Turing.FinTM.one_work_tape_binary` (legal: `D` is total). (3) Modify the
one-work-tape machine's finite control with a register remembering the Boolean
emission — including a bit emitted on the halting transition — and replace its
halt: halt iff the remembered bit is `true`, otherwise enter a stationary
one-state live loop (such a deliberately divergent state exists: emit nothing,
move nothing, return the same live state). This control modification needs its
own run/halting lemma — a named fill obligation. The result `S` halts on `x`
iff `x ∈ L`. (4) Code `S` with `Turing.exists_codeTM` (no totality hypothesis)
and set `α := c.encode S`. The reduction maps `x ↦ Turing.pairEncode α x`: a
fixed doubled prefix of length `2|α| + 2` followed by the verbatim input,
computable by an emit-then-copy machine in `2|α| + |x| + 3` steps (a small new
machine or prefixing lemma — the audited `pairDiagTM` computes the diagonal
pair, not this fixed-prefix function). `Complexity.HALT_pairEncode_eq_true_iff`
and `Turing.MachineCode.decode_encode` turn membership of the image in `HALT`
into "`S` halts on `x`", which is `x ∈ L`. -/
theorem HALT_NPHard (c : MachineCode) :
    NPHard {s | HALT c s = true} := by
  sorry

/-- **`HALT` is not in `NP`** [AB09, Exercise 2.8] — so, despite being `NP`-hard,
it is not `NP`-complete: `NP` languages are decidable, `HALT` is not.

**Proof sketch.** If `HALT`'s language were in `NP`, it would be in `EXP` by
the repaired `Complexity.NP_subset_EXP`, so some machine would decide it — and
a decider's output is exactly `[HALT c s]` (off the pair image `HALT` is
`false` and the rejection bit matches, per the totalization convention), making
`fun s => [HALT c s]` computable
(`Complexity.Computable` via `Turing.FinTM.ComputesFunInTime.computes`),
contradicting `Complexity.HALT_not_computable`. The audit certified this chain
valid once `NP_subset_EXP` is repaired. The `Turing.EffectiveMachineCode`
hypothesis is a **proof-route restriction, not a mathematical necessity**
(round-2 audit, finding 3 — the pre-repair docstring's trivial-machine
"counterexample" violates `decode_encode` and is unlawful): this proof reuses
Chapter 1's `HALT_not_computable`, whose own proof runs the universal
evaluator and hence needs effectivity. The round-2 audit exhibited a direct
diagonalization (diagonal pairing, the searcher's control transform with the
halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator) proving `HALT`
undecidable for **every** lawful `Turing.MachineCode`; whether to add that
diagonal lemma and generalize this statement is a recorded human-review
design question (`AroraBarakChapter2Plan.md`, open design questions). Until
decided, this statement stays at the generality its cited API supports. -/
theorem HALT_not_mem_NP (c : EffectiveMachineCode) :
    {s | HALT c.toMachineCode s = true} ∉ NP := by
  sorry

end Complexity

## ===== TCSlib/Complexity/ClassNP/NTIME.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic deciding and the classes NTIME

[AB09, §2.1.2, Definition 2.5]: a language `L` is in `NTIME T` when some binary-choice
NDTM decides it within time `c · T` — on every input, **every** branch halts within the
budget, and the input is in `L` exactly when **some** branch accepts. This module fixes
the binary alphabet (as `TCSlib.Complexity.ClassP.DTIME` does for the deterministic
classes), defines acceptance, the deciding predicate, and `NTIME`, and states the
deterministic embedding `DTIME ⊆ NTIME`.

## Design and deviations from [AB09]

* **Acceptance is by output, not by a `q_accept` state**: a branch *accepts* when it has
  halted with output exactly `[true]`. [AB09] gives NDTMs a distinguished accepting
  state; our machine model (single halting state, append-only output tape)
  distinguishes outcomes by output, and the deterministic `Turing.FinTM.DecidesInTime`
  already reads `[true]`/`[false]` off the output tape — acceptance-by-output keeps the
  two layers aligned, at the price that a branch halting with output `[]`, `[false]`,
  or any string other than the singleton `[true]` is non-accepting. Nothing constrains
  the outputs of non-accepting branches. **Design question (a) for the phase-2
  audit.**
* **The totality bound quantifies over all inputs and all branches**
  ([AB09, §2.1.2] verbatim: "for every input `x` and every sequence of nondeterministic
  choices"): `Turing.FinNDTM.DecidesInTime` demands `HaltsWithin` on **every** input —
  members and non-members alike — conjoined per input with the acceptance equivalence.
  Placing the halting quantifier per input (rather than as one global conjunct) is
  presentational; demanding it on non-members is not, and is the standard reading.
  **Design question (b) for the phase-2 audit.**
* **Exact-length choice words**: both `AcceptsWithin` and `HaltsWithin` quantify over
  choice words of length exactly `t`; the equivalent bounded-length readings differ by
  quantifier shape (round-1 audit, finding 2). For **acceptance** the bounded
  existential is equivalent: some `w` with `|w| ≤ t` reaching a halted configuration
  with output `[true]` pads with `false`-bits to exact length
  (`Turing.NDTM.runWith_of_halt`). For **all-branch halting** the bounded reading is
  prefix-shaped: every word of length `t` has a halted prefix `w.take r` with `r ≤ t`
  (forward take `r = t`; backward absorb the suffix) — **not** "every word of length
  at most `t` is already halted", which fails at the empty word against the live
  initial state. Moreover, under `HaltsWithin x t` the run of any longer word `w`
  *equals* the run of `w.take t` — the whole configuration, not merely the halting
  flag — which is what the backward (truncation) directions of `Complexity.NTIME.mono`
  and the compilation sketches use.
* As with `Complexity.DTIME`, the constant `c` in `NTIME` ranges over all of `ℕ`; the
  value `c = 0` gives the unsatisfiable budget `0` (no machine is halted at time `0`)
  and contributes nothing, matching [AB09]'s `c > 0` without a positivity side
  condition.

## Main definitions

* `Turing.FinNDTM.AcceptsWithin` — some branch of length `t` halts with output
  `[true]`. [AB09, §2.1.2: "`M(x) = 1`"]
* `Turing.FinNDTM.DecidesInTime` — all-branch halting plus the acceptance
  characterization of membership. [AB09, §2.1.2]
* `Complexity.NTIME` — the class of languages decided nondeterministically in time
  `c · T`. [AB09, Definition 2.5]

## Main results

* `Turing.FinNDTM.AcceptsWithin.mono` — acceptance is monotone in the branch length.
* `Complexity.NTIME.mono` — `NTIME` is monotone in the time bound.
* `Complexity.DTIME_subset_NTIME` — deterministic time is nondeterministic time.
  [AB09, §2.1.2]
* `Complexity.NTIME_eq_empty_of_exists_zero` — a vanishing time bound gives the empty
  class, as for `DTIME`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, Definition 2.5, pp. 41-42.)
-/

namespace Turing.FinNDTM

/-- The machine `N` *accepts* `x` within `t` steps: **some** choice word of length `t`
leaves the machine halted with output exactly `[true]`. This is [AB09, §2.1.2]'s
"`M(x) = 1`" with acceptance read off the output tape in place of the `q_accept` state
(see the deviations list; design question (a)). A branch halted with any other output —
including `[]` and `[false]` — is non-accepting. -/
def AcceptsWithin (N : FinNDTM Bool) (x : List Bool) (t : ℕ) : Prop :=
  ∃ w : List Bool, w.length = t ∧
    (N.tm.runWith w (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith w (N.tm.initCfg x)).output = [true]

/-- Acceptance is monotone in the branch length: an accepting branch stays accepting
when the choice word is extended.

**Proof sketch.** Pad the accepting word `w` to `w ++ List.replicate (t' - t) false`
(length `t'` by `List.length_append` and `List.length_replicate`, since `t ≤ t'`);
`Turing.NDTM.runWith_append` factors the padded run through the halted configuration
reached by `w`, and `Turing.NDTM.runWith_of_halt` absorbs the padding, preserving both
the halted state and the output `[true]`. -/
theorem AcceptsWithin.mono {N : FinNDTM Bool} {x : List Bool} {t t' : ℕ}
    (h : N.AcceptsWithin x t) (hle : t ≤ t') : N.AcceptsWithin x t' := by
  obtain ⟨w, hw, hhalt, hout⟩ := h
  refine ⟨w ++ List.replicate (t' - t) false, ?_, ?_⟩
  · rw [List.length_append, List.length_replicate, hw, Nat.add_sub_of_le hle]
  · rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
    exact ⟨hhalt, hout⟩

/-- The machine `N` *decides* the language `L` within time `T`, nondeterministically:
on every input `x`, every branch of length `T |x|` has halted
(`Turing.NDTM.HaltsWithin` — [AB09]'s totality condition, demanded on members and
non-members alike), and `x ∈ L` exactly when some such branch accepts.
[AB09, §2.1.2 with Definition 2.5] -/
def DecidesInTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    N.tm.HaltsWithin x (T x.length) ∧ (x ∈ L ↔ N.AcceptsWithin x (T x.length))

end Turing.FinNDTM

namespace Complexity

open Turing

/-- The class of languages decidable nondeterministically in time `c · T` for some
constant `c`: a language `L` is in `NTIME T` iff some finite binary-alphabet NDTM
decides it within `c · T n` steps on inputs of length `n`, in the sense of
`Turing.FinNDTM.DecidesInTime`. [AB09, Definition 2.5] -/
def NTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.DecidesInTime L fun n => c * T n}

/-- `NTIME` is monotone in the time bound.

**Proof sketch.** The same machine works at the larger budget `c · T₂ n ≥ c · T₁ n`.
All-branch halting transfers by `Turing.NDTM.HaltsWithin.mono`. The acceptance
equivalence transfers in both directions: forward by
`Turing.FinNDTM.AcceptsWithin.mono` (pad the accepting word); backward by truncation —
given an accepting word `w` at the larger budget, its prefix `w.take (c * T₁ n)` has
halted (all-branch halting at the smaller budget), and `Turing.NDTM.runWith_append` on
`w = w.take _ ++ w.drop _` with `Turing.NDTM.runWith_of_halt` shows the full run equals
the truncated one, so the truncated word already accepts. -/
theorem NTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : NTIME T₁ ⊆ NTIME T₂ := by
  rintro L ⟨c, N, hN⟩
  refine ⟨c, N, ?_⟩
  intro x
  obtain ⟨hhalt, haccept⟩ := hN x
  have hle := Nat.mul_le_mul_left c (h x.length)
  refine ⟨hhalt.mono hle, ?_⟩
  constructor
  · intro hx
    exact (haccept.mp hx).mono hle
  · rintro ⟨w, hw, _, hout⟩
    apply haccept.mpr
    have hlen : (w.take (c * T₁ x.length)).length = c * T₁ x.length :=
      List.length_take_of_le (hle.trans_eq hw.symm)
    have hprefix := hhalt (w.take (c * T₁ x.length)) hlen
    refine ⟨w.take (c * T₁ x.length), hlen, hprefix, ?_⟩
    have hrun := NDTM.runWith_append (tm := N.tm)
      (w.take (c * T₁ x.length)) (w.drop (c * T₁ x.length)) (N.tm.initCfg x)
    rw [List.take_append_drop, NDTM.runWith_of_halt _ hprefix] at hrun
    rw [← hrun]
    exact hout

/-- **Deterministic time is nondeterministic time** [AB09, §2.1.2]: a TM is an NDTM
that ignores its choices, so `DTIME T ⊆ NTIME T`.

**Proof sketch.** Given `M` deciding `L` within `c · T n`, take
`Turing.FinTM.toFinNDTM M`. By `Turing.MultiTapeTM.toNDTM_runWith`, the run under
**any** choice word of length `t` is `M`'s deterministic run to time `t`, so: every
branch of length `c · T n` is halted because `M`'s computation has halted by then
(`Turing.FinTM.DecidesInTime` unfolded through `Turing.FinTM.computesInTime_iff`),
giving `HaltsWithin`; and some branch of that length is halted with output `[true]` iff
`M`'s output at that time is `[true]`, which by the indicator contract
(`Turing.MultiTapeTM.indicator`) holds iff `x ∈ L` — for `x ∉ L` the output is
`[false] ≠ [true]` on every branch, so no branch accepts. -/
theorem DTIME_subset_NTIME (T : ℕ → ℕ) : DTIME T ⊆ NTIME T := by
  classical
  rintro L ⟨c, M, hM⟩
  refine ⟨c, M.toFinNDTM, ?_⟩
  intro x
  obtain ⟨hhalt, hout⟩ := (M.computesInTime_iff _ _ _).mp (hM x)
  have hrun (w : List Bool) :
      M.toFinNDTM.tm.runWith w (M.toFinNDTM.tm.initCfg x) =
        M.tm.runFrom (M.tm.initCfg x) w.length :=
    M.tm.toNDTM_runWith w (M.tm.initCfg x)
  constructor
  · intro w hw
    rw [hrun, hw]
    exact hhalt
  · constructor
    · intro hx
      refine ⟨List.replicate (c * T x.length) false, List.length_replicate .., ?_, ?_⟩
      · rw [hrun, List.length_replicate]
        exact hhalt
      · rw [hrun, List.length_replicate, hout]
        simp only [MultiTapeTM.indicator, if_pos hx]
    · rintro ⟨w, hw, _, hwout⟩
      rw [hrun, hw, hout] at hwout
      by_contra hx
      simp only [MultiTapeTM.indicator, if_neg hx] at hwout
      cases hwout

/-- If the time bound vanishes at even one input length, the class is empty, exactly as
for `Complexity.DTIME_eq_empty_of_exists_zero`: the initial configuration is not
halted, so all-branch halting already fails at budget `c * 0 = 0`.

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate
`Turing.FinNDTM.DecidesInTime` at the input `List.replicate n false`
(`List.length_replicate`); its `HaltsWithin` conjunct applied to the empty choice word
(`Turing.NDTM.runWith_nil`) asserts that the initial configuration is halted,
contradicting `Turing.Cfg.init`'s state `some q₀`. -/
theorem NTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : NTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro L ⟨c, N, hN⟩
  have hhalt := (hN (List.replicate n false)).1
  simp only [List.length_replicate, hn, Nat.mul_zero] at hhalt
  have hzero : (some N.tm.q₀ : Option N.State) = none := hhalt [] rfl
  cases hzero

end Complexity

## ===== TCSlib/Complexity/TuringMachine/Nondeterministic.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic Multi-Tape Turing Machines

[AB09, §2.1.2]: a nondeterministic Turing machine (NDTM) is a standard TM with **two**
transition functions `δ₀` and `δ₁`; at every step the machine chooses which of the two to
apply. A finite run is therefore governed by a *choice word* — one bit per step — and the
run function is indexed by it. This module defines the raw machine, its choice-word
semantics in the style of the deterministic `Turing.MultiTapeTM.runFrom`, the all-branch
halting predicate that time bounds quantify over, the bundled finite layer `FinNDTM`, and
the embedding of deterministic machines. Acceptance and the class `NTIME` live one layer
up, in `TCSlib.Complexity.ClassNP.NTIME`, because they fix the binary alphabet.

## Design and deviations from [AB09]

* **Two total transition functions, `Bool`-indexed**: the single field
  `tr : Bool → …` carries [AB09]'s `δ₀` as `tr false` and `δ₁` as `tr true`. Both
  functions are total, so no configuration is ever *stuck* — every choice word of every
  length drives a complete run. (This is the load-bearing difference from a
  relational model such as cslib's `MultiTapeNTM`, surveyed and deliberately not
  ported — see the plan's decision log: with binary choice the accepting choice word
  *is* the polynomial-length certificate of [AB09, Theorem 2.6], while arbitrary
  branching relations have no canonical certificate encoding.)
* **Choice words are finite lists** (`List Bool`), consumed left to right, one bit per
  step: `runWith w cfg` is the configuration after `|w|` steps under the choices `w`.
  The alternative — infinite choice streams `ℕ → Bool` with a separate step count — is
  equivalent for every notion built here (only the first `t` bits of a stream are ever
  consulted); the list form makes the choice word a finite string that can be a
  certificate. **Design question (c) for the phase-2 audit.**
* **No `q_accept` state.** [AB09] equips NDTMs with a distinguished accepting state;
  our machines signal through their output tape, exactly as the deterministic
  development does (`Turing.FinTM.DecidesInTime` reads acceptance off the output
  `[true]`/`[false]`). Acceptance-by-output is defined in
  `TCSlib.Complexity.ClassNP.NTIME` and is **design question (a) for the phase-2
  audit**.
* **Halting is absorbing under every choice**: stepping a halted configuration is the
  identity regardless of the choice bit, mirroring the deterministic `step`. Extending
  a choice word beyond the halting time therefore never changes the reached
  configuration — the lemma `runWith_of_halt` below. This is what the exact-length
  quantifiers lean on, *directionally*: accepting witnesses pad to any larger exact
  length, and all-branch halting at a larger budget follows by splitting at the old
  one (`HaltsWithin.mono`). It does **not** make every bounded-length rewriting valid —
  "every word of length at most `t` is halted" already fails at the empty word — and
  the correct bounded readings are recorded in `TCSlib.Complexity.ClassNP.NTIME`
  (round-1 audit, finding 2).
* The model reuses the vendored configuration layer (`Turing.Cfg`, `Turing.Action`)
  unchanged: an NDTM step applies an `Action` exactly as a deterministic step does; only
  the *selection* of the action is new.

## Main definitions

* `Turing.NDTM` — the binary-choice nondeterministic machine. [AB09, §2.1.2]
* `Turing.NDTM.stepWith`, `Turing.NDTM.runWith` — one step under a choice bit; the run
  under a choice word. [AB09, §2.1.2]
* `Turing.NDTM.HaltsWithin` — every choice word of length `t` halts the machine on the
  given input; the totality condition of [AB09]'s "runs in `T(n)` time".
* `Turing.FinNDTM` — the bundled finite layer, mirroring `Turing.FinTM`.
* `Turing.MultiTapeTM.toNDTM`, `Turing.FinTM.toFinNDTM` — a deterministic machine as an
  NDTM whose two transition functions coincide.

## Main results

* `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt` — the choice-word run
  algebra (proved; pure unfoldings, the nondeterministic counterparts of the vendored
  `runFrom` lemmas).
* `Turing.NDTM.HaltsWithin.mono` — all-branch halting is monotone in the time bound.
* `Turing.MultiTapeTM.toNDTM_runWith` — the embedded deterministic machine ignores its
  choices: every choice word of length `t` reproduces `runFrom` at time `t`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, pp. 41-42.)
* cslib (https://github.com/leanprover/cslib), `MultiTape/Nondeterministic.lean` at
  commit a3747758: a relational nondeterministic model (related work, not ported — see
  `AroraBarakChapter2Plan.md`, decision log).
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A binary-choice nondeterministic multi-tape Turing machine [AB09, §2.1.2]: a
machine with **two** total transition functions, carried as the `Bool`-indexed field
`tr` — `tr false` is [AB09]'s `δ₀` and `tr true` is `δ₁`. Tapes, actions, and
configurations are exactly those of the deterministic `Turing.MultiTapeTM`; as there,
`Symbol` and `State` need not be finite at this layer (the bundled finite layer is
`Turing.FinNDTM` below). -/
structure NDTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- the two transition functions, indexed by the nondeterministic choice: `tr false`
  is `δ₀`, `tr true` is `δ₁`; each maps the state, input symbol, and work-head symbols
  to an action, exactly as the deterministic transition function does -/
  tr (choice : Bool) (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace NDTM

variable {input : List Symbol} {tm : NDTM k Symbol State}

/-- One step under the choice bit `b`: apply the action selected by transition function
`tr b`, or stay put when already halted. Halting is absorbing under **every** choice —
the halted branch does not consult `b` — mirroring `Turing.MultiTapeTM.step`. -/
def stepWith (b : Bool) (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tm.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration corresponding to an input string — identical to the
deterministic initialization (blank work tapes, input head on the first symbol). -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

/-- The configuration reached from `cfg` by running under the choice word `w`, one
choice bit per step, consumed left to right: `|w|` steps in total. This is the
nondeterministic counterpart of `Turing.MultiTapeTM.runFrom`; a "branch" of the
computation tree of [AB09, §2.1.2] is the run under one choice word. -/
def runWith : List Bool → Cfg k Symbol State input → Cfg k Symbol State input
  | [], cfg => cfg
  | b :: w, cfg => runWith w (tm.stepWith b cfg)

/-- The empty choice word runs zero steps. -/
@[simp]
lemma runWith_nil {cfg : Cfg k Symbol State input} : tm.runWith [] cfg = cfg := rfl

/-- Consuming one choice bit is one step: the run under `b :: w` is the run under `w`
from the configuration one `stepWith b` ahead. -/
lemma runWith_cons {b : Bool} {w : List Bool} {cfg : Cfg k Symbol State input} :
    tm.runWith (b :: w) cfg = tm.runWith w (tm.stepWith b cfg) := rfl

/-- Running under `w ++ w'` is running under `w`, then under `w'` from the reached
configuration — the counterpart of `Turing.MultiTapeTM.runFrom_add`. -/
lemma runWith_append (w w' : List Bool) (cfg : Cfg k Symbol State input) :
    tm.runWith (w ++ w') cfg = tm.runWith w' (tm.runWith w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [List.cons_append, runWith_cons, runWith_cons, ih]

/-- Stepping a halted configuration is the identity, under either choice. -/
@[simp]
lemma stepWith_of_halt {b : Bool} {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.stepWith b cfg = cfg := by
  unfold stepWith
  rw [h]

/-- Running from a halted configuration stays there, under **every** choice word — the
counterpart of `Turing.MultiTapeTM.runFrom_of_halt`. Extending a choice word beyond the
halting time therefore never changes the reached configuration. -/
@[simp]
lemma runWith_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none)
    {w : List Bool} : tm.runWith w cfg = cfg := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, stepWith_of_halt h]; exact ih

/-- The machine halts on `input` within `t` steps **along every branch**: after any `t`
nondeterministic choices the configuration is halted. This is the totality condition in
[AB09]'s "runs in `T(n)` time" (§2.1.2: *every* sequence of choices reaches the halting
state within the bound), rendered over choice words of length exactly `t`; by
`Turing.NDTM.runWith_of_halt` the exact-length quantifier already covers all longer
words, and `Turing.NDTM.HaltsWithin.mono` makes this precise. -/
def HaltsWithin (tm : NDTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ w : List Bool, w.length = t → (tm.runWith w (tm.initCfg input)).state = none

/-- All-branch halting is monotone in the time bound.

**Proof sketch.** Given `w` with `|w| = t' ≥ t`, split `w = w.take t ++ w.drop t`
(`List.take_append_drop`) with `|w.take t| = t` (`List.length_take`, since `t ≤ t'`).
By the hypothesis the run under `w.take t` is halted; `Turing.NDTM.runWith_append`
factors the run under `w` through it, and `Turing.NDTM.runWith_of_halt` absorbs the
remaining choices, so the state at `w` equals the halted state at `w.take t`. -/
theorem HaltsWithin.mono {tm : NDTM k Symbol State} {input : List Symbol} {t t' : ℕ}
    (h : tm.HaltsWithin input t) (hle : t ≤ t') : tm.HaltsWithin input t' := by
  intro w hw
  have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
  have hhalt := h (w.take t) hlen
  have hrun := runWith_append (tm := tm) (w.take t) (w.drop t) (tm.initCfg input)
  rw [List.take_append_drop, runWith_of_halt _ hhalt] at hrun
  rw [hrun]
  exact hhalt

end NDTM

/-- A nondeterministic machine bundled with a finite state type, mirroring
`Turing.FinTM`: the instances are data (`Fintype`/`DecidableEq`, not `Finite`) for the
same reason as there — a machine that is to be encoded as a string must enumerate its
transition tables. All headline nondeterministic-complexity definitions
(`Turing.FinNDTM.DecidesInTime`, `Complexity.NTIME`) are stated over this layer. -/
structure FinNDTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying nondeterministic machine -/
  tm : NDTM k Symbol State

attribute [instance] FinNDTM.fintypeState FinNDTM.decEqState

/-- A deterministic machine as a nondeterministic one whose two transition functions
coincide: both choices apply the deterministic transition. This is the embedding behind
`DTIME ⊆ NTIME` ([AB09, §2.1.2]: a TM is an NDTM that ignores its choices). -/
def MultiTapeTM.toNDTM (tm : MultiTapeTM k Symbol State) : NDTM k Symbol State :=
  ⟨tm.q₀, fun _ => tm.tr⟩

/-- The embedded deterministic machine starts where the original does. -/
@[simp]
lemma MultiTapeTM.toNDTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNDTM.initCfg input = tm.initCfg input := rfl

/-- The embedded deterministic machine ignores its choices: running `toNDTM` under any
choice word `w` is running the original machine for `|w|` steps.

**Proof sketch.** Induction on `w` generalizing the configuration. For one step,
`Turing.NDTM.stepWith` on `toNDTM` and `Turing.MultiTapeTM.step` are the same match on
the state — halted branches are both the identity, and on a live state both apply the
action `tm.tr q …` since `toNDTM.tr b = tm.tr` for either `b`. The cons case is then
`Turing.NDTM.runWith_cons` against `Turing.MultiTapeTM.runFrom_succ_eq_step` (the step
count on the right is `|w| + 1`, `List.length_cons`). -/
theorem MultiTapeTM.toNDTM_runWith (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.runWith w cfg = tm.runFrom cfg w.length := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih =>
    rw [NDTM.runWith_cons, List.length_cons, runFrom_succ_eq_step]
    exact ih (tm.step cfg)

/-- A bundled deterministic machine as a bundled nondeterministic one — the `FinTM`
layer of `Turing.MultiTapeTM.toNDTM`, with the same tapes and state type. -/
def FinTM.toFinNDTM {Symbol : Type} (M : FinTM Symbol) : FinNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toNDTM⟩

end Turing

## ===== TCSlib/Complexity/ClassNP/CoNP.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class coNP

[AB09, §2.6.1]: `coNP` is the class of complements of `NP` languages
(Definition 2.19), equivalently the class of languages whose membership is
certified by *every* polynomial-length certificate (Definition 2.20); the
equivalence is [AB09, Exercise 2.24]. This module also records the closure of
`P` under complement that the equivalence rides on, and the two standard
containment facts `P ⊆ NP ∩ coNP` and `P = NP → NP = coNP`.

## Design

* The complement-form Definition 2.19 is primary (it is one line); the
  ∀-certificate form is the characterization theorem, matching [AB09]'s own
  pedagogical ordering in reverse.
* `Complexity.compl_mem_P` is a statement *about the Chapter-1 class `P`* that
  Chapter 1 never needed; it is a new addition beyond the audited Chapter-1
  surface, placed here (its first consumer) and flagged for the phase-1 audit.

## Main definitions

* `Complexity.coNP` — the class coNP. [AB09, Definition 2.19]

## Main results

* `Complexity.compl_mem_P` — `P` is closed under complement.
* `Complexity.mem_coNP_iff_forall` — the ∀-certificate characterization
  [AB09, Definition 2.20 and Exercise 2.24].
* `Complexity.P_subset_NP_inter_coNP` — [AB09, Exercise 2.23].
* `Complexity.NP_eq_coNP_of_P_eq_NP` — [AB09, Exercise 2.25].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Definitions 2.19-2.20, pp. 55-56;
  Exercises 2.23-2.25.)
-/

namespace Complexity

/-- **The class coNP** [AB09, Definition 2.19]: the complements of `NP` languages. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

/-- **`P` is closed under complement**: if `L` is decidable in polynomial time then
so is its complement.

**Proof sketch.** Obtain a decider of `L` from `Complexity.mem_P_iff`, read it
pointwise as computing the total singleton-indicator function (the decider's
output is exactly `[indicator L x]`), and postcompose with the Boolean-negation
postprocessor `Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]`
(`w ↦ if w = [true] then [false] else [true]`) via the **timed** total
composition `Turing.FinTM.computesFunInTime_comp` — the untimed
`exists_comp_partial` carries no time bound (phase-1 audit, finding 4). The
composite computes the complement's indicator within a budget polynomial by the
composition ledger and the monotonicity of the explicit polynomial; return
through `Complexity.mem_P_of_dtime_le`. Buffered composition keeps the
intermediate bit off the real output. This is a new statement about the
Chapter-1 class, flagged for audit (plan §6) and certified by the phase-1
round (finding 10). -/
theorem compl_mem_P {L : Language Bool} (h : L ∈ P) : Lᶜ ∈ P := by
  classical
  obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp h
  obtain ⟨N, a, hN⟩ := Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]
  have hfun : M.ComputesFunInTime (fun x => [Turing.MultiTapeTM.indicator L x])
      (fun n => C * (n + 1) ^ d) := fun x => hM x
  -- Buffer the decider's singleton output and apply the timed Boolean postprocessor.
  obtain ⟨M', b, hcomp⟩ := Turing.FinTM.computesFunInTime_comp
    hfun hN
    (fun _ _ hle => Nat.mul_le_mul_left a (Nat.add_le_add_right hle 1))
  have hdec : M'.DecidesInTime Lᶜ
      (fun n => b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1)) := by
    intro x
    by_cases hx : x ∈ L
    · have hxc : x ∉ (Lᶜ : Language Bool) := fun hnot => hnot hx
      simpa [Function.comp_apply, Turing.MultiTapeTM.indicator, hx, hxc] using hcomp x
    · have hxc : x ∈ (Lᶜ : Language Bool) := hx
      simpa [Function.comp_apply, Turing.MultiTapeTM.indicator, hx, hxc] using hcomp x
  -- Absorb the linear postprocessor and composition overhead into the same degree.
  refine mem_P_of_dtime_le
    (T := fun n => b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1))
    ⟨1, M', by simpa only [one_mul] using hdec⟩
    (b * (C + a * (C + 1) + 1) * 2 ^ d) d ?_
  intro n
  have hpow : 1 ≤ (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos n)
  have hsum : C * (n + 1) ^ d + 1 ≤ (C + 1) * (n + 1) ^ d := by
    calc C * (n + 1) ^ d + 1 ≤ C * (n + 1) ^ d + (n + 1) ^ d :=
        Nat.add_le_add_left hpow _
      _ = (C + 1) * (n + 1) ^ d := by ring
  calc b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1)
      ≤ b * (C * (n + 1) ^ d + a * ((C + 1) * (n + 1) ^ d) + (n + 1) ^ d) :=
        Nat.mul_le_mul_left b
          (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left a hsum) _) hpow)
    _ = b * (C + a * (C + 1) + 1) * (n + 1) ^ d := by ring
    _ ≤ b * (C + a * (C + 1) + 1) * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul_left _ (succ_pow_le n d)
    _ = b * (C + a * (C + 1) + 1) * 2 ^ d * (n ^ d + 1) := by ring

/-- **The ∀-certificate characterization of coNP** [AB09, Definition 2.20,
equivalence per Exercise 2.24]: `L ∈ coNP` iff there are a certificate
coefficient `C`, degree `c`, and a verifier `V ∈ P` with
`x ∈ L ↔ ∀ u, |u| = C(|x|+1)^c → x ++ u ∈ V` — the same explicit length
formula as `Complexity.NP` (phase-1 audit repair, finding 1).

**Proof sketch.** Negate the exact-length existential in `NP`'s membership
equivalence for `Lᶜ`: `x ∈ L ↔ ¬(∃ u, |u| = C(|x|+1)^c ∧ x ++ u ∈ V₀)
↔ ∀ u, |u| = C(|x|+1)^c → x ++ u ∈ V₀ᶜ`, and `V₀ᶜ ∈ P` by
`Complexity.compl_mem_P`; both directions instantiate the same `C, c`,
complementing the verifier. Purely logical — no certificate-length computation
is needed (audit finding table). -/
theorem mem_coNP_iff_forall {L : Language Bool} :
    L ∈ coNP ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∀ u : List Bool, u.length = C * (x.length + 1) ^ c → x ++ u ∈ V := by
  classical
  constructor
  · rintro ⟨C, c, V, hV, hmem⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    have hx : x ∉ L ↔ ∃ u : List Bool,
        u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V := hmem x
    change x ∈ L ↔ ∀ u : List Bool,
      u.length = C * (x.length + 1) ^ c → x ++ u ∉ V
    simpa only [not_not, not_exists, not_and] using not_congr hx
  · rintro ⟨C, c, V, hV, hmem⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    change x ∉ L ↔ ∃ u : List Bool,
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∉ V
    simpa only [not_forall, exists_prop] using not_congr (hmem x)

/-- **`P ⊆ NP ∩ coNP`** [AB09, Exercise 2.23].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; for the `coNP` half,
`L ∈ P` gives `Lᶜ ∈ P ⊆ NP` by `Complexity.compl_mem_P`, i.e. `L ∈ coNP`. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP ∩ coNP := by
  intro L hL
  exact ⟨P_subset_NP hL, P_subset_NP (compl_mem_P hL)⟩

/-- **If `P = NP` then `NP = coNP`** [AB09, Exercise 2.25].

**Proof sketch.** Under `P = NP`: `L ∈ NP → L ∈ P → Lᶜ ∈ P → Lᶜ ∈ NP → L ∈ coNP`
by `Complexity.compl_mem_P`, and symmetrically `L ∈ coNP → Lᶜ ∈ NP = P → L ∈ P =
NP` by closing under complement once more. -/
theorem NP_eq_coNP_of_P_eq_NP (h : P = NP) : NP = coNP := by
  apply Set.Subset.antisymm
  · intro L hL
    change Lᶜ ∈ NP
    rw [← h] at hL ⊢
    exact compl_mem_P hL
  · intro L hL
    change Lᶜ ∈ NP at hL
    rw [← h] at hL ⊢
    simpa only [compl_compl] using compl_mem_P hL

end Complexity

## ===== TCSlib/Complexity/ClassNP/NP.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class NP

[AB09, §2.1, Definition 2.1]: a language `L` is in `NP` when membership has
polynomial-length certificates verifiable in polynomial time — `x ∈ L` iff some
certificate `u` of the prescribed polynomial length makes the verifier accept.

## Design and deviations from [AB09]

* **The certificate length is an explicit polynomial formula**, exactly
  `C · (|x| + 1)^c` bits: the definition quantifies over the *coefficient and
  degree*, not over an abstract length function. This is the phase-1 audit's
  repair (findings 1-2, Argument A): a length function constrained only by a
  numerical bound can itself smuggle undecidable information through length
  arithmetic — certificate *content* never enters — putting every
  length-determined language in the class. An explicit formula is computable,
  monotone, and information-free by construction. The numerical helper
  `Complexity.PolyBound` survives for bound bookkeeping only; it never appears
  in a class definition.
* **The verifier is a language, not a machine.** We render "polynomial-time TM
  `M` with `M(x, u) = 1`" as membership of the concatenation `x ++ u` in a
  verifier language `V ∈ P` — reusing the audited Chapter-1 class. The phase-1
  audit certified this abstraction sound (finding 10): `V ∈ P` supplies one
  uniform total decider, and for a fixed length formula, `V`'s values off the
  constrained strings change no membership statement.
* **Pairing is concatenation in the exact-length form** ([AB09], footnote 4):
  the definition never splits `x ++ u` — the membership equivalence quantifies
  over `x` and `u` separately, and with the explicit formula, any consumer
  that must recover the split can (`n + n·formula` arithmetic is computable
  and `n ↦ n + C(n+1)^c` is strictly increasing). The **bounded-length**
  variant ([AB09, Exercise 2.1]) is different: with `∃ u, |u| ≤ …` and plain
  concatenation, the empty certificate forces `V ⊆ L`, which collapses every
  prefix-free language to its verifier (audit finding 2, Argument B) — so the
  bounded form below pairs its inputs with the audited self-delimiting
  `Turing.pairEncode` instead.
* **Certificates have length exactly `C(|x|+1)^c`** (Definition 2.1 verbatim,
  with the formula for [AB09]'s "polynomial `p`").

## Main definitions

* `Complexity.NP` — the class NP. [AB09, Definition 2.1]

## Main results

* `Complexity.P_subset_NP` — `P ⊆ NP` (empty certificates). [AB09, §2.1]
* `Complexity.mem_NP_iff_exists_length_le` — bounded-length *paired*
  certificates define the same class. [AB09, Exercise 2.1, repaired per the
  phase-1 audit]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1, Definition 2.1, pp. 39-41;
  Exercise 2.1.)
-/

namespace Complexity

open Turing

/-- **The class NP** [AB09, Definition 2.1]: `L ∈ NP` iff there are a certificate
coefficient `C`, degree `c`, and a polynomial-time-decidable verifier language
`V ∈ P` such that `x ∈ L` exactly when some certificate `u` of length exactly
`C · (|x| + 1)^c` makes the concatenation `x ++ u` a member of `V`. The
certificate length is an explicit formula in `|x|` — never an abstract
function — so it is computable and carries no information beyond `|x|`
(phase-1 audit, finding 1). -/
def NP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ NP`** [AB09, §2.1, after Definition 2.1]: a language decidable in
polynomial time is verifiable with empty certificates.

**Proof sketch.** Take `C = 0` (certificate length `0 · (n+1)^0 = 0`) and
`V = L`: the only certificate of length `0` is `[]`, and `x ++ [] = x`, so the
membership equivalence is the identity. The audit confirmed this covers
`L = ∅`, `L = univ`, and `x = []` (finding table, question 2). -/
theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  refine ⟨0, 0, L, hL, fun x => ?_⟩
  simp only [zero_mul, List.length_eq_zero_iff, exists_eq_left, List.append_nil]

/-- **Bounded-length paired certificates define the same class**
[AB09, Exercise 2.1, repaired per the phase-1 audit]: `L ∈ NP` iff there are
`C`, `c`, and a verifier `V ∈ P` with
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V`. The bounded form pairs
`x` with `u` via the audited self-delimiting `Turing.pairEncode`: with plain
concatenation the empty certificate would force `V ⊆ L` and collapse every
prefix-free language (audit finding 2, Argument B).

**Proof sketch.** (⇒) From the exact form `(C, c, V)`, take the paired verifier
`V' := {pairEncode x u : |u| = C(|x|+1)^c ∧ x ++ u ∈ V}` with the same bound:
deciding `V'` parses the aligned pair (the `Turing.pairDecode` grammar; a
polynomial-time scan), checks the length equality against the explicit formula,
reassembles `x ++ u`, and runs `V`'s decider — each a named machine obligation
for the fill, none exotic. (⇐) From the bounded form `(C, c, V)`, take exact
length `R n = (C+1)(n+1)^c` — **admissible** for the repaired `NP`
(coefficient `C+1`, degree `c`; the round-2 audit refuted the earlier choice
`C(n+1)^c + 1`, which is not of the class's required shape — round-2
finding 1) — leaving `R n - C(n+1)^c = (n+1)^c ≥ 1` room for the marker. Pad
each certificate right-self-delimitingly to `u ++ [true] ++ false-run` of
length `R n`. The new verifier, on `y` of length `m`: search `n ≤ m` for
`n + R n = m` — strict increase of `n ↦ n + R n` gives **at most one**
solution, and none may exist (e.g. `y = []`, since `R n ≥ 1`): **reject if no
such `n` exists** (round-3 audit, finding 1); otherwise split `y = x ++ v` at
that unique `n` with
`|v| = R n ≥ 1`; reject if `v` has no `true` bit (so stripping never enters
`x`); split `v = u ++ [true] ++ false-run` at the **last** `true`; check the
*original* bound `|u| ≤ C(n+1)^c` — checkable precisely because the bound is
the explicit formula (phase-1 finding 2's residual error, fixed in round 1) —
and consult `V` on `pairEncode x u`. Every old witness pads within `R n`
(`|u| + 1 ≤ C(n+1)^c + 1 ≤ R n`); every accepted new witness strips back to
an old one (the round-2 audit's reconstruction, checked there across the
`C = 0`, `c = 0`, `x = []`, `u = []`, all-`false`, and malformed edge
cases). -/
theorem mem_NP_iff_exists_length_le {L : Language Bool} :
    L ∈ NP ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ u : List Bool, u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V := by
  sorry

end Complexity

## ===== TCSlib/Complexity/ClassNP/EXP.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# EXP and NEXP

[AB09, Claim 2.4 and §2.6.2]: the exponential-time classes. `EXP` is
`⋃ c, DTIME (2^(n^c))` verbatim from Claim 2.4. `NEXP` is defined here in the
certificate form of [AB09, Exercise 2.27] — exponential-length certificates with
a polynomial-time verifier language — mirroring `Complexity.NP`; its equivalence
with the `NTIME` form of §2.6.2 is a phase-2 obligation, once nondeterministic
machines exist.

## Design and deviations from [AB09]

* `NEXP`'s verifier is a language `V ∈ P`: "polynomial time" is measured in the
  length of the padded string `x ++ u`, which is exponential in `|x|` — this is
  the standard certificate rendering and exactly Exercise 2.27's intent.
* **The certificate length is the explicit formula `C · 2^((|x|+1)^c)`** — the
  same phase-1 audit repair as `Complexity.NP` (finding 1, Argument A: an
  abstract `ExpBound` length function admits undecidable classes). `ExpBound`
  survives as a numerical helper only.
* The chain `P ⊆ NP ⊆ EXP ⊆ NEXP` [AB09, Claim 2.4 and §2.6.2] is stated as the
  three individual inclusions below (`P ⊆ NP` lives in `ClassNP/NP.lean`).

## Main definitions

* `Complexity.EXP` — [AB09, Claim 2.4].
* `Complexity.ExpBound`, `Complexity.NEXP` — [AB09, §2.6.2, in the form of
  Exercise 2.27].

## Main results

* `Complexity.P_subset_EXP` — [AB09, Claim 2.4].
* `Complexity.NP_subset_EXP` — certificate enumeration [AB09, Claim 2.4].
* `Complexity.EXP_subset_NEXP` — [AB09, §2.6.2].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2, pp. 56-57;
  Exercise 2.27.)
-/

namespace Complexity

/-- **The class EXP** [AB09, Claim 2.4]: languages decidable in time `2^(n^c)`
for some constant `c` (up to `DTIME`'s constant-factor slack). -/
def EXP : Set (Language Bool) :=
  ⋃ c : ℕ, DTIME fun n => 2 ^ n ^ c

/-- The bound `p : ℕ → ℕ` is *exponentially bounded*: `p n ≤ C · 2^((n+1)^c)` for
some constants — the certificate-length regime of `NEXP`. -/
def ExpBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * 2 ^ (n + 1) ^ c

/-- **The class NEXP**, in the certificate form of [AB09, Exercise 2.27]:
certificates of length exactly `C · 2^((|x|+1)^c)` — an explicit formula, per
the phase-1 audit repair — with a verifier language decidable in time
polynomial in the padded string `x ++ u`. The `NTIME` form of [AB09, §2.6.2] and
its equivalence with this one are phase-2 obligations. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * 2 ^ (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ EXP`** [AB09, Claim 2.4].

**Proof sketch.** `n^c + 1 ≤ 2 · 2^(n^c)` for every `n` (as `n^c < 2^(n^c)`), so
each `DTIME (n^c + 1)` sits inside `DTIME (2 · 2^(n^c)) ⊆ EXP` by
`Complexity.DTIME.mono` and the constant-absorbing `Complexity.DTIME`
definition. -/
theorem P_subset_EXP : P ⊆ EXP := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hL
  have hbound : ∀ n : ℕ, n ^ c + 1 ≤ 2 * 2 ^ n ^ c := by
    intro n
    have hn := Nat.lt_two_pow_self (n := n ^ c)
    omega
  obtain ⟨a, M, hM⟩ := DTIME.mono hbound hc
  refine Set.mem_iUnion.mpr ⟨c, a * 2, M, fun x => ?_⟩
  simpa only [Nat.mul_assoc] using hM x

/-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.

**Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
`x` of length `n`: evaluate the explicit formula `Q n` (a polynomial-evaluation
machine — a **new obligation**; the explicit formula is what makes the width
computable at all, phase-1 audit finding 1 and question 4) and lay out a
width-`Q n` all-`false` candidate certificate; in each round, assemble
`x ++ u` on a buffer, run `MV`, accept if it accepts, else increment the
candidate as a **fixed-width** counter and repeat, rejecting on width overflow
after the `2^(Q n)`-th round. Enumeration is over certificates of exactly the
definition's length — no majorant mismatch (audit question 4). The remaining
machine obligations, named for the fill per phase-1 finding 5 and round-2
finding 2: fixed-width increment with overflow detection (the private
`counterInc` layer of `ClassP/TimeConstructible.lean` extends on overflow and
is a template, not a citable API — promotion or private re-derivation is a
fill-time decision); retention of `x` and the candidate across rounds;
**a verifier-call simulation that captures `MV`'s decision bit in finite
control, suppresses its physical emissions, and redirects its halt to the
loop controller** — the output tape is append-only, so forwarding per-round
emissions would accumulate (`[false, true]` across two rounds) and violate
`DecidesInTime`'s singleton contract; the real output stays empty until the
final answer (the capture-wrapper pattern of `Turing.universalCaptureTM` is
the in-repo precedent); reset of `MV`'s simulated state, heads, work region,
and the captured bit between rounds (a bounded region — each head moves at
most one cell per step); and a timed loop invariant covering all of the above
(the untimed `exists_cond` does not supply one; at `C = 0` the single round on
the empty certificate still executes). Budget: at most `2^(Q n)` rounds of cost polynomial in
`n + Q n + 1`, i.e. `a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree
`e`, small lengths absorbed into `DTIME`'s constant (the audit's own estimate):
`L ∈ EXP`. -/
theorem NP_subset_EXP : NP ⊆ EXP := by
  sorry

/-- **`EXP ⊆ NEXP`** [AB09, §2.6.2].

**Proof sketch.** Given `L ∈ EXP` decided in time `2^(n^c)`, take `C = 1` and
certificate length `p n = 2^((n+1)^c)` — nondecreasing in `n` (constant `2` at
`c = 0`), so that `n ↦ n + p n` is **strictly increasing** (the monotonicity
belongs to the sum, not to `p` — phase-1 audit, finding 8) — and the verifier
`V = {x ++ u : x ∈ L, |u| = p |x|}`. `V ∈ P`: on a string `y` of length `m`,
recover the unique `n` with `n + p n = m` by scanning `n ≤ m` (each evaluation
writes `2^((n+1)^c)` in binary, `(n+1)^c + 1 ≤ (m+1)^c + 1` bits — polynomial
in `m`, the audit's own check), reject if no split exists (including `m = 0`),
split off `x`, and run `L`'s decider: its `a · 2^(n^c)` budget is at most
`a · m`. Fixed-degree arithmetic and the split/copy machinery are named new
machine obligations for the fill. Certificates carry no information; padding
buys the verifier its time. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  sorry

end Complexity

## ===== TCSlib/Complexity/Formulas/CNF.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Std.Sat.CNF
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Dedup

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CNF formulas for the complexity development

[AB09, §2.3.1]: a CNF formula is an AND of ORs of literals (variables or their
negations); a `k`CNF is a CNF in which every clause has **at most** `k` literals.
This module supplies the formula layer that `SAT`, `3SAT`, and the Cook-Levin
development consume: the carrier type, satisfiability, the variable-count measure
used by certificate-length formulas, clause-width bounds, and the statement of
[AB09, Claim 2.13] (CNF universality).

## Design and deviations from [AB09]

* **The carrier is `Std.Sat.CNF ℕ`** — the Lean-core SAT type: a formula is a
  `List` of clauses, a clause a `List` of literals, a literal a pair
  `(v, b) : ℕ × Bool` satisfied by an assignment `a` exactly when `a v = b` (so
  `b = true` is the positive literal `u_v` and `b = false` its negation). This is
  the **provisional resolution of the phase-3 seeded design question** (in-house
  type vs. `Std.Sat.CNF`; see the plan's decision log): the in-house candidate
  would have been byte-for-byte this shape, core supplies the evaluation
  (`Std.Sat.CNF.eval`, an all/any nest exactly matching [AB09]'s ⋀⋁), the
  mentioned-variable machinery (`Std.Sat.CNF.Mem`, `Std.Sat.CNF.eval_congr`),
  and relabeling with `Std.Sat.CNF.eval_relabel` (the fresh-variable tool of the
  clause-splitting and tableau constructions), and the repository policy is to
  use an existing mechanism rather than invent a parallel one. The type is pinned
  by `lean-toolchain`; the risk of upstream namespace drift is accepted and
  recorded. Campaign-side additions live in the `Std.Sat.CNF` namespace when they
  are formula-level (this file and the serialization layer) and in `Complexity`
  when they are complexity-level.
* **Conventions inherited from the carrier**: the empty formula evaluates `true`
  (`Std.Sat.CNF.eval_nil`) and an empty clause evaluates `false` — [AB09]'s
  standard reading of empty conjunctions/disjunctions.
* **Assignments are total functions `ℕ → Bool`.** [AB09] assigns to the `n`
  variables of the formula; a total assignment restricted to the mentioned
  variables carries the same information, and `Complexity.eval_congr_of_lt_numVars`
  (below) is the bridge that lets a finite certificate of `numVars φ` bits
  determine the value.
* **`kCNF` is "at most `k` literals per clause"** ([AB09, §2.3.1] verbatim);
  `Std.Sat.CNF.WidthAtMost` renders it.
* **Claim 2.13's size measure**: [AB09] counts `∧`/`∨` symbols (size `ℓ·2^ℓ`).
  Our statement bounds the clause count by `2^ℓ` and every clause's width by `ℓ`,
  from which [AB09]'s connective count follows by the trivial accounting
  (`#∧ = clauses − 1`, `#∨ = Σ (width − 1)` on nonempty data); the two
  renderings carry the same content and ours is the form the consumers use.

## Main definitions

* `Std.Sat.CNF.Satisfiable` — some assignment evaluates to `true`.
  [AB09, §2.3.1]
* `Std.Sat.CNF.numVars` — one plus the largest mentioned variable index (`0` for
  formulas mentioning nothing); the measure certificate-length formulas use.
* `Std.Sat.CNF.WidthAtMost` — every clause has at most `k` literals ([AB09]'s
  `k`CNF, §2.3.1).

## Main results

* `Complexity.eval_congr_of_lt_numVars` — evaluation depends only on the first
  `numVars` assignment bits.
* `Complexity.exists_cnf_boolFun` — CNF universality. [AB09, Claim 2.13]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1, pp. 44-45; Claim 2.13, p. 46.)
-/

namespace Std.Sat.CNF

/-- The formula `φ` is *satisfiable*: some assignment makes it evaluate `true`
[AB09, §2.3.1]. (Core's `Std.Sat.CNF.Sat` fixes the assignment and
`Std.Sat.CNF.Unsat` is the universal negative; this is the existential the
language `SAT` quantifies.) -/
def Satisfiable {α : Type} (φ : CNF α) : Prop :=
  ∃ a : α → Bool, φ.eval a = true

/-- One plus the largest variable index mentioned in `φ`, and `0` when `φ`
mentions no variable (in particular on the empty formula and on empty clauses).
Every mentioned variable of `φ` is `< φ.numVars`, so an assignment certificate
of `numVars` bits determines the evaluation
(`Complexity.eval_congr_of_lt_numVars`); this is the measure the explicit
certificate-length formulas of `SAT ∈ NP` are budgeted against. -/
def numVars (φ : CNF ℕ) : ℕ :=
  (φ.flatMap fun C => C.map fun ℓ => ℓ.1 + 1).foldr max 0

/-- Every clause of `φ` has at most `k` literals — [AB09, §2.3.1]'s `k`CNF
("a CNF formula in which all clauses contain at most `k` literals"). The empty
formula qualifies vacuously for every `k`. -/
def WidthAtMost {α : Type} (φ : CNF α) (k : ℕ) : Prop :=
  ∀ C ∈ φ, C.length ≤ k

end Std.Sat.CNF

namespace Complexity

open Std.Sat (CNF)

/-- Every member of a list of natural numbers is bounded by its maximum fold. -/
private theorem le_foldr_max_of_mem {n : ℕ} {s : List ℕ} (h : n ∈ s) :
    n ≤ s.foldr max 0 := by
  induction s with
  | nil => cases h
  | cons m s ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Evaluation reads only the first `numVars` assignment values: assignments that
agree below `φ.numVars` evaluate `φ` identically. This is the bridge from finite
assignment certificates to total assignments.

**Proof sketch.** Every variable `v` mentioned in `φ` (`Std.Sat.CNF.Mem v φ`)
contributes `v + 1` to the `foldr max` defining `Std.Sat.CNF.numVars`, so
`v < φ.numVars` (a list-membership-to-fold bound, by induction on the flattened
list); then `Std.Sat.CNF.eval_congr` applies, its agreement hypothesis
discharged by the assumed agreement below `numVars`. -/
theorem eval_congr_of_lt_numVars {φ : CNF ℕ} {a b : ℕ → Bool}
    (h : ∀ v < φ.numVars, a v = b v) : φ.eval a = φ.eval b := by
  apply Std.Sat.CNF.eval_congr a b φ
  intro v hv
  apply h v
  apply Nat.lt_of_succ_le
  apply le_foldr_max_of_mem
  obtain ⟨C, hC, hv⟩ := hv
  apply List.mem_flatMap.mpr
  refine ⟨C, hC, ?_⟩
  rcases hv with hv | hv
  · exact List.mem_map.mpr ⟨(v, false), hv, rfl⟩
  · exact List.mem_map.mpr ⟨(v, true), hv, rfl⟩

/-- A termwise upper bound bounds the maximum fold, including the empty list. -/
private theorem foldr_max_le_of_forall {s : List ℕ} {n : ℕ}
    (h : ∀ k ∈ s, k ≤ n) : s.foldr max 0 ≤ n := by
  induction s with
  | nil => exact Nat.zero_le _
  | cons k s ih =>
      exact Nat.max_le.mpr
        ⟨h k (List.mem_cons_self), ih (fun j hj => h j (List.mem_cons_of_mem k hj))⟩

/-- The clause excluding precisely the assignment `v`, as in [AB09, Claim 2.13]. -/
private def falsifyingClause {ℓ : ℕ} (v : Fin ℓ → Bool) : CNF.Clause ℕ :=
  List.ofFn fun i => (i.val, !(v i))

/-- The excluding clause is false exactly on the assignment it excludes.
This is the pointwise step of [AB09, Claim 2.13]. -/
private theorem falsifyingClause_eval_false {ℓ : ℕ} (v : Fin ℓ → Bool)
    (a : ℕ → Bool) :
    (falsifyingClause v).eval a = false ↔ (fun i : Fin ℓ => a i.val) = v := by
  simp only [falsifyingClause, CNF.Clause.eval, List.any_eq_false]
  constructor
  · intro h
    funext i
    have hi := h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    cases ha : a i.val <;> cases hv : v i <;> simp_all
  · intro h p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    have hi := congrFun h i
    change ¬(a i.val == !(v i)) = true
    rw [hi]
    cases v i <;> decide

/-- The conjunction of all falsifying-assignment clauses in [AB09, Claim 2.13]. -/
private noncomputable def falsifyingCNF {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) : CNF ℕ :=
  ((Finset.univ.filter fun v => f v = false).toList).map falsifyingClause

/-- The truth-table construction uses only the prescribed variables. -/
private theorem falsifyingCNF_numVars {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) :
    (falsifyingCNF f).numVars ≤ ℓ := by
  unfold CNF.numVars falsifyingCNF
  apply foldr_max_le_of_forall
  intro k hk
  obtain ⟨C, hC, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hC
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact i.isLt

/-- There is at most one clause per assignment in the truth-table construction. -/
private theorem falsifyingCNF_length {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) :
    (falsifyingCNF f).length ≤ 2 ^ ℓ := by
  classical
  simpa only [falsifyingCNF, List.length_map, Finset.length_toList,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin ℓ → Bool))
      (fun v => f v = false))

/-- Every truth-table clause has exactly one literal per prescribed variable. -/
private theorem falsifyingCNF_width {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) :
    (falsifyingCNF f).WidthAtMost ℓ := by
  intro C hC
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hC
  exact (List.length_ofFn (f := fun i : Fin ℓ => (i.val, !(v i)))).le

/-- The truth-table CNF computes the original Boolean function.

**Proof sketch.** Its conjunction is false iff one of its clauses is false.
That clause excludes exactly the restricted assignment, so it is present iff
the original function is false there. Equality follows by Boolean cases. -/
private theorem falsifyingCNF_eval {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool)
    (a : ℕ → Bool) : (falsifyingCNF f).eval a = f (fun i => a i.val) := by
  classical
  have hfalse : (falsifyingCNF f).eval a = false ↔ f (fun i => a i.val) = false := by
    simp only [CNF.eval, List.all_eq_false, ← Bool.eq_false_iff]
    constructor
    · rintro ⟨C, hC, hCa⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hC
      have hvf := (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
      rw [(falsifyingClause_eval_false v a).mp hCa]
      exact hvf
    · intro ha
      refine ⟨falsifyingClause (fun i : Fin ℓ => a i.val), ?_,
        (falsifyingClause_eval_false _ a).mpr rfl⟩
      exact List.mem_map.mpr ⟨_, Finset.mem_toList.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩), rfl⟩
  cases hc : (falsifyingCNF f).eval a <;>
    cases hf : f (fun i => a i.val) <;> simp_all

/-- **CNF universality** [AB09, Claim 2.13]: every Boolean function
`f : {0,1}^ℓ → {0,1}` is computed by an `ℓ`-variable CNF formula with at most
`2^ℓ` clauses of width at most `ℓ` ([AB09]'s size measure `ℓ·2^ℓ` follows by
counting connectives — see the deviations list). The formula mentions only
variables `< ℓ`, so its evaluation at a total assignment is `f` of the
assignment's restriction.

**Proof sketch.** [AB09]'s construction. For each `v : Fin ℓ → Bool` with
`f v = false`, the clause `C_v = [(i, !(v i)) : i < ℓ]` evaluates to `false`
exactly at the assignments restricting to `v` (a literal `(i, !(v i))` is
satisfied iff `a i ≠ v i`, so `C_v.eval a = false` iff `a` agrees with `v` below
`ℓ`). Take `φ` to be the list of `C_v` over the (finitely many, at most `2^ℓ`)
falsifying `v`, e.g. via `Finset.univ.filter (fun v => f v = false)` on the
`Fintype` of `Fin ℓ → Bool`. Then `φ.eval a = false` iff some `C_v` fails at `a`
iff `f` of `a`'s restriction is `false`. Bounds: clause count at most
`2^ℓ = Fintype.card (Fin ℓ → Bool)`, width exactly `ℓ`, mentioned variables
`< ℓ` so `numVars ≤ ℓ`. Edge cases: at `ℓ = 0` the function is a constant on
the empty vector — `φ = []` (evaluating `true`) or `φ = [[]]` (one empty
clause, evaluating `false`, width `0 ≤ ℓ`), both within the `2^0 = 1` clause
bound. -/
theorem exists_cnf_boolFun (ℓ : ℕ) (f : (Fin ℓ → Bool) → Bool) :
    ∃ φ : CNF ℕ, φ.numVars ≤ ℓ ∧ φ.length ≤ 2 ^ ℓ ∧ φ.WidthAtMost ℓ ∧
      ∀ a : ℕ → Bool, φ.eval a = f fun i => a i.val := by
  exact ⟨falsifyingCNF f, falsifyingCNF_numVars f, falsifyingCNF_length f,
    falsifyingCNF_width f, falsifyingCNF_eval f⟩

end Complexity

## ===== TCSlib/Complexity/Formulas/CNFEncoding.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary serialization of CNF formulas

The languages `SAT` and `3SAT` are sets of **binary strings** ([AB09, §2.3.1]),
so formulas need a serialization, a parser, and — per [AB09, footnote 3] — a
totalization mapping non-well-formed strings to "some fixed formula". This module
supplies all three, together with the statements that tie them together: the
parse/serialize round trip and the variable-count bound that certificate-length
formulas rely on.

## Design and deviations from [AB09]

* **[AB09] fixes no concrete scheme** (footnote 3 explicitly waves the issue);
  any polynomially bounded, machine-parsable scheme is faithful. Ours is chosen
  for **parser-machine simplicity** and is the phase-3 serialization design
  question's provisional answer (see the plan's decision log):
  - a **literal** `(v, b)` is `v + 1` `true`s, then `false`, then the bit `b` —
    variable indices in **unary**, so the parsing machine counts a run instead
    of doing binary arithmetic;
  - a **clause** is its literals concatenated, then `false` (a clause-start
    position reading `false` means the clause is over — unambiguous, since
    every literal starts with `true`);
  - a **formula** is each clause prefixed by `true`, concatenated, then `false`
    (a formula-level position reading `true` announces another clause, `false`
    ends the formula).
  The grammar is LL(1): at every position the next bit alone determines the
  production. The empty formula is `[false]`; the empty clause is
  `[true, false]`.
* **Unary indices cost only a polynomial factor**: a literal on variable `v`
  occupies `v + 3` bits, so a serialized formula has length at least the sum of
  its `v + 1`-runs — which is what makes `numVars_decode_le` (below) true with
  the plain bound `|x|` — and at most polynomially more than any binary-index
  scheme on the formulas the campaign produces (the Cook-Levin tableau formula
  has polynomially many variables, so its unary serialization stays
  polynomial). Every downstream consumer is polynomial-time, so the choice is
  immaterial to every stated class-membership or hardness result.
* **The parser is fuel-indexed**: `parseClause`/`parseClauses` recurse on an
  explicit fuel argument (structural recursion, no termination proof
  obligations), and `parse` supplies fuel `x.length` — adequate because every
  production consumes at least one input bit before recursing, which is part of
  the round-trip statement's burden, not an axiom.
* **Exact consumption**: `parse` succeeds only when the grammar consumes the
  whole string; trailing garbage makes a string non-well-formed.
* **The fallback is the empty formula** `[]` — trivially satisfiable, a
  tautology, and of width `0`. [AB09, footnote 3] maps non-well-formed strings
  to "some fixed formula" and notes the choice is immaterial; consequences of
  this particular choice (every non-well-formed string lies in `SAT` and
  `3SAT`) are recorded where the languages are defined.

## Main definitions

* `Std.Sat.CNF.serialize` (with `serializeLit`, `serializeClause`) — the
  encoding.
* `Std.Sat.CNF.parse` (with `takeTrues`, `parseLit`, `parseClause`,
  `parseClauses`) — the exact-consumption parser.
* `Std.Sat.CNF.fallback`, `Std.Sat.CNF.decode` — the [AB09, footnote 3]
  totalization.

## Main results

* `Std.Sat.CNF.parse_serialize`, `Std.Sat.CNF.decode_serialize` — the round
  trip: serialized formulas are well-formed and decode to themselves.
* `Std.Sat.CNF.numVars_decode_le` — a decoded formula mentions at most `|x|`
  variables; the bound certificate-length formulas are budgeted against.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1 with footnote 3, p. 45.)
-/

namespace Std.Sat.CNF

/-- Serialize one literal `(v, b)`: the variable index in unary (`v + 1` `true`s
— nonempty even for `v = 0`), the run terminator `false`, then the polarity bit
`b` verbatim. -/
def serializeLit (ℓ : Literal ℕ) : List Bool :=
  List.replicate (ℓ.1 + 1) true ++ [false, ℓ.2]

/-- Serialize one clause: its literals concatenated, closed by `false`. The
terminator is unambiguous because every literal begins with `true`. -/
def serializeClause (C : Clause ℕ) : List Bool :=
  C.flatMap serializeLit ++ [false]

/-- Serialize a formula: every clause prefixed by `true`, concatenated, closed
by `false`. At any formula-level position, `true` announces another clause and
`false` ends the formula; the empty formula is `[false]`. -/
def serialize (φ : CNF ℕ) : List Bool :=
  (φ.flatMap fun C => true :: serializeClause C) ++ [false]

/-- Split off the leading run of `true`s: `takeTrues x = (k, rest)` where `x`
begins with exactly `k` `true`s and `rest` is the remainder (which is empty or
begins with `false`). -/
def takeTrues : List Bool → ℕ × List Bool
  | true :: r => let (k, rest) := takeTrues r; (k + 1, rest)
  | r => (0, r)

/-- Parse one literal from the front: a nonempty run of `k + 1` `true`s, the
terminator `false`, and a polarity bit yield the literal `(k, ·)` and the
unconsumed remainder; anything else (no leading `true`, or the string ending
inside the literal) fails. -/
def parseLit (x : List Bool) : Option (Literal ℕ × List Bool) :=
  match takeTrues x with
  | (0, _) => none
  | (k + 1, false :: b :: rest) => some ((k, b), rest)
  | _ => none

/-- Parse one clause body with explicit fuel: a leading `false` closes the
clause; a leading `true` parses one literal and recurses. Exhausted fuel or an
exhausted string inside a clause fails. `Std.Sat.CNF.parse` supplies fuel
`x.length`, adequate because every literal consumes at least three bits. -/
def parseClause : ℕ → List Bool → Option (Clause ℕ × List Bool)
  | _, false :: rest => some ([], rest)
  | fuel + 1, x@(true :: _) =>
      match parseLit x with
      | some (ℓ, rest) =>
          match parseClause fuel rest with
          | some (C, rest') => some (ℓ :: C, rest')
          | none => none
      | none => none
  | _, _ => none

/-- Parse a clause list with explicit fuel: a leading `false` ends the formula;
a leading `true` parses one clause and recurses. -/
def parseClauses : ℕ → List Bool → Option (CNF ℕ × List Bool)
  | _, false :: rest => some ([], rest)
  | fuel + 1, true :: rest =>
      match parseClause fuel rest with
      | some (C, rest') =>
          match parseClauses fuel rest' with
          | some (φ, rest'') => some (C :: φ, rest'')
          | none => none
      | none => none
  | _, _ => none

/-- Parse a whole string as a formula, requiring **exact consumption**: the
grammar must account for every bit, and trailing garbage fails the parse.
Fuel `x.length` is adequate because every production consumes at least one bit
before recursing (part of the round-trip statement's burden). -/
def parse (x : List Bool) : Option (CNF ℕ) :=
  match parseClauses x.length x with
  | some (φ, []) => some φ
  | _ => none

/-- The fixed fallback formula of [AB09, footnote 3]: the empty CNF — trivially
satisfiable, a tautology, and of width `0`. -/
def fallback : CNF ℕ := []

/-- Total decoding: parse, and map non-well-formed strings to the fixed
`Std.Sat.CNF.fallback` ([AB09, footnote 3] — "such strings represent some fixed
formula"; the `Turing.MachineCode` decode-totality convention is the in-repo
precedent). -/
def decode (x : List Bool) : CNF ℕ :=
  (parse x).getD fallback

/-- Reading a nonempty unary run stops at its following `false`, preserving
the entire suffix. -/
private theorem takeTrues_replicate (k : ℕ) (r : List Bool) :
    takeTrues (List.replicate (k + 1) true ++ false :: r) = (k + 1, false :: r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (let (n, s) := takeTrues (List.replicate (k + 1) true ++ false :: r)
              (n + 1, s)) = _
      rw [ih]

/-- A serialized literal parses correctly with any unconsumed suffix. -/
private theorem parseLit_serializeLit (ℓ : Literal ℕ) (r : List Bool) :
    parseLit (serializeLit ℓ ++ r) = some (ℓ, r) := by
  simp only [serializeLit, List.append_assoc, List.cons_append, List.nil_append,
    parseLit, takeTrues_replicate]

/-- A clause round-trips with any suffix and any fuel at least its serialized
length.

**Proof sketch.** Induct on the literal list. The terminator closes the empty
clause without spending fuel. A literal consumes at least three bits, leaving
the decremented fuel large enough for the tail; apply the literal round trip
and then the induction hypothesis. -/
private theorem parseClause_serializeClause (C : Clause ℕ) (r : List Bool)
    (fuel : ℕ) (hf : (serializeClause C).length ≤ fuel) :
    parseClause fuel (serializeClause C ++ r) = some (C, r) := by
  induction C generalizing fuel with
  | nil => simp only [serializeClause, List.flatMap_nil, List.nil_append,
      List.cons_append, parseClause]
  | cons ℓ C ih =>
      cases fuel with
      | zero =>
          simp only [serializeClause, List.length_append, List.length_cons,
            List.length_nil] at hf
          omega
      | succ fuel =>
          have htail : (serializeClause C).length ≤ fuel := by
            simp only [serializeClause, List.flatMap_cons, List.length_append,
              serializeLit, List.length_replicate, List.length_cons, List.length_nil] at hf ⊢
            omega
          have hx : serializeClause (ℓ :: C) ++ r =
              serializeLit ℓ ++ (serializeClause C ++ r) := by
            simp only [serializeClause, List.flatMap_cons, List.append_assoc]
          rw [hx]
          have hlit := parseLit_serializeLit ℓ (serializeClause C ++ r)
          simp only [serializeLit, List.replicate_succ, List.cons_append] at hlit ⊢
          simp only [parseClause, hlit, ih fuel htail]

/-- A formula round-trips with any suffix and any fuel at least its serialized
length.

**Proof sketch.** Induct on the clause list. The empty formula reads its
terminator. A clause record has its leading marker and a nonempty serialized
body, so the decremented fuel suffices both for the clause body and for the
remaining formula. Thread the same suffix through the two round trips. -/
private theorem parseClauses_serialize (φ : CNF ℕ) (r : List Bool)
    (fuel : ℕ) (hf : (serialize φ).length ≤ fuel) :
    parseClauses fuel (serialize φ ++ r) = some (φ, r) := by
  induction φ generalizing fuel with
  | nil => simp only [serialize, List.flatMap_nil, List.nil_append,
      List.cons_append, parseClauses]
  | cons C φ ih =>
      cases fuel with
      | zero =>
          simp only [serialize, List.length_append, List.length_cons,
            List.length_nil] at hf
          omega
      | succ fuel =>
          have hclause : (serializeClause C).length ≤ fuel := by
            simp only [serialize, List.flatMap_cons, List.length_append,
              List.length_cons, List.length_nil] at hf
            omega
          have htail : (serialize φ).length ≤ fuel := by
            simp only [serialize, List.flatMap_cons, List.length_append,
              List.length_cons, List.length_nil] at hf ⊢
            omega
          have hx : serialize (C :: φ) ++ r =
              true :: (serializeClause C ++ (serialize φ ++ r)) := by
            simp only [serialize, List.flatMap_cons, List.cons_append, List.append_assoc]
          rw [hx]
          simp only [parseClauses, parseClause_serializeClause C _ fuel hclause,
            ih fuel htail]

/-- **The round trip**: serialized formulas parse back to themselves (with the
whole string consumed).

**Proof sketch.** Strengthen to suffix-carrying forms and induct.
(i) `takeTrues (List.replicate (k+1) true ++ false :: r) = (k+1, false :: r)`
by induction on `k`, so `parseLit (serializeLit ℓ ++ r) = some (ℓ, r)`.
(ii) For every clause `C` and suffix `r`, and any fuel at least
`(serializeClause C).length`,
`parseClause fuel (serializeClause C ++ r) = some (C, r)`: induction on `C`,
the nil case reading the closing `false`, the cons case chaining (i) and the
induction hypothesis — each literal consumes at least three bits, so the fuel
decrement stays adequate. (iii) The analogous statement for `parseClauses` over
the clause list, each clause consuming at least two bits. (iv) Instantiate at
the empty suffix: fuel `(serialize φ).length` suffices, the final `false` closes
the formula, and the remainder is exactly `[]`, so `parse` accepts. -/
theorem parse_serialize (φ : CNF ℕ) : parse (serialize φ) = some φ := by
  have h := parseClauses_serialize φ [] (serialize φ).length (Nat.le_refl _)
  simp only [List.append_nil] at h
  simp only [parse, h]

/-- Decoding inverts serialization: `decode` on a serialized formula is the
formula itself.

**Proof sketch.** `Std.Sat.CNF.parse_serialize` and `Option.getD` on a
`some`. -/
theorem decode_serialize (φ : CNF ℕ) : decode (serialize φ) = φ := by
  simp only [decode, parse_serialize, Option.getD_some]

/-- The counted unary run and the returned suffix partition the input length. -/
private theorem takeTrues_length (x : List Bool) :
    (takeTrues x).1 + (takeTrues x).2.length = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      cases b with
      | false => simp only [takeTrues, Nat.zero_add]
      | true =>
          simp only [takeTrues, List.length_cons]
          omega

/-- A successful literal parse consumes exactly its unary run, terminator,
and polarity bit. -/
private theorem parseLit_length {x r : List Bool} {ℓ : Literal ℕ}
    (h : parseLit x = some (ℓ, r)) : ℓ.1 + 3 + r.length = x.length := by
  have hlen := takeTrues_length x
  unfold parseLit at h
  split at h
  · cases h
  · rename_i k b rest ht
    cases h
    simp only [ht, List.length_cons] at hlen
    omega
  · cases h

/-- On a successful clause parse, the remainder is no longer than the input,
and every variable contribution fits inside the consumed prefix.

**Proof sketch.** Induct on fuel and distinguish the input marker. A closing
marker produces no literals. A literal consumes exactly its index plus three
bits; the induction hypothesis bounds the remaining parse. Add the final
remainder length to each variable contribution to avoid truncated subtraction. -/
private theorem parseClause_bounds {fuel : ℕ} {x r : List Bool} {C : Clause ℕ}
    (h : parseClause fuel x = some (C, r)) :
    r.length ≤ x.length ∧ ∀ ℓ ∈ C, ℓ.1 + 1 + r.length ≤ x.length := by
  induction fuel generalizing x C r with
  | zero =>
      cases x with
      | nil =>
          simp only [parseClause] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClause, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun ℓ hℓ => False.elim (List.not_mem_nil hℓ)⟩
          | true =>
              simp only [parseClause] at h
              cases h
  | succ fuel ih =>
      cases x with
      | nil =>
          simp only [parseClause] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClause, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun ℓ hℓ => False.elim (List.not_mem_nil hℓ)⟩
          | true =>
              cases hl : parseLit (true :: s) with
              | none =>
                  simp only [parseClause, hl] at h
                  cases h
              | some p =>
                  obtain ⟨lit, t⟩ := p
                  cases hc : parseClause fuel t with
                  | none =>
                      simp only [parseClause, hl, hc] at h
                      cases h
                  | some p =>
                      obtain ⟨D, u⟩ := p
                      simp only [parseClause, hl, hc, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      obtain ⟨hlen, hvars⟩ := ih hc
                      have hcons := parseLit_length hl
                      constructor
                      · omega
                      · intro ℓ hℓ
                        rcases List.mem_cons.mp hℓ with rfl | hℓ
                        · omega
                        · have hv := hvars ℓ hℓ
                          omega

/-- On a successful formula parse, the remainder is no longer than the input,
and every variable contribution fits inside the consumed prefix.

**Proof sketch.** Induct on fuel. A closing marker has no variables. Otherwise,
apply the clause bound to the first clause and the induction hypothesis to
the remaining formula. The final remainder is no longer than either earlier
suffix, so both sets of variable bounds persist when the parses are composed. -/
private theorem parseClauses_bounds {fuel : ℕ} {x r : List Bool} {φ : CNF ℕ}
    (h : parseClauses fuel x = some (φ, r)) :
    r.length ≤ x.length ∧ ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 + 1 + r.length ≤ x.length := by
  induction fuel generalizing x φ r with
  | zero =>
      cases x with
      | nil =>
          simp only [parseClauses] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun C hC => False.elim (List.not_mem_nil hC)⟩
          | true =>
              simp only [parseClauses] at h
              cases h
  | succ fuel ih =>
      cases x with
      | nil =>
          simp only [parseClauses] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun C hC => False.elim (List.not_mem_nil hC)⟩
          | true =>
              cases hc : parseClause fuel s with
              | none =>
                  simp only [parseClauses, hc] at h
                  cases h
              | some p =>
                  obtain ⟨D, t⟩ := p
                  cases ht : parseClauses fuel t with
                  | none =>
                      simp only [parseClauses, hc, ht] at h
                      cases h
                  | some p =>
                      obtain ⟨ψ, u⟩ := p
                      simp only [parseClauses, hc, ht, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      obtain ⟨hclen, hcvars⟩ := parseClause_bounds hc
                      obtain ⟨htlen, htvars⟩ := ih ht
                      simp only [List.length_cons]
                      constructor
                      · omega
                      · intro C hC ℓ hℓ
                        rcases List.mem_cons.mp hC with rfl | hC
                        · have hv := hcvars ℓ hℓ
                          omega
                        · have hv := htvars C hC ℓ hℓ
                          omega

/-- A uniform bound on literal contributions bounds the formula's maximum
variable index plus one. -/
private theorem numVars_le_of_literal_bounds (φ : CNF ℕ) (n : ℕ)
    (h : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 + 1 ≤ n) : φ.numVars ≤ n := by
  have fold_bound : ∀ s : List ℕ, (∀ k ∈ s, k ≤ n) → s.foldr max 0 ≤ n := by
    intro s hs
    induction s with
    | nil => exact Nat.zero_le _
    | cons k s ih =>
        exact Nat.max_le.mpr ⟨hs k List.mem_cons_self,
          ih (fun j hj => hs j (List.mem_cons_of_mem k hj))⟩
  unfold numVars
  apply fold_bound
  intro k hk
  obtain ⟨C, hC, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hk
  exact h C hC ℓ hℓ

/-- **A decoded formula mentions at most `|x|` variables**: for every string
`x`, `(decode x).numVars ≤ x.length`. This is the bound that lets the `SAT`
certificate length be the explicit formula `(n + 1)` bits — an assignment
certificate never needs more bits than the input is long.

**Proof sketch.** For the fallback (parse failure), `numVars [] = 0`. For a
successful parse, strengthen over the parsing functions: whenever
`parseLit`/`parseClause`/`parseClauses` succeeds on a string `y` returning a
remainder `r`, the consumed prefix has length `y.length - r.length`, and every
literal `(k, b)` produced consumed its own `k + 1` `true`s within that prefix —
so `k + 1 ≤ y.length`. Every mentioned variable of the parsed formula therefore
satisfies `v + 1 ≤ x.length`, and the `foldr max` defining
`Std.Sat.CNF.numVars` is bounded by `x.length` (each contribution is). -/
theorem numVars_decode_le (x : List Bool) : (decode x).numVars ≤ x.length := by
  unfold decode parse
  cases hp : parseClauses x.length x with
  | none => exact Nat.zero_le _
  | some p =>
      obtain ⟨φ, r⟩ := p
      cases r with
      | nil =>
          change φ.numVars ≤ x.length
          apply numVars_le_of_literal_bounds
          intro C hC ℓ hℓ
          simpa only [List.length_nil, Nat.add_zero] using
            (parseClauses_bounds hp).2 C hC ℓ hℓ
      | cons b r => exact Nat.zero_le _

end Std.Sat.CNF

## ===== TCSlib/Complexity/Formulas/DNF.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The DNF reading and the De Morgan dual

[AB09, §2.6.1, Example 2.21] negates the Cook-Levin CNF formula `φ_x` and asks
whether `¬φ_x` is a tautology; the negation of a CNF is a **DNF** — an OR of
ANDs of literals. This module supplies the minimal dual layer that renders
that argument: a DNF *evaluation* of the existing carrier, the literal-negating
dual map, and the De Morgan bridge between satisfiability and dual tautology.

## Design and deviations from [AB09]

* **A DNF is the same syntax read dually, not a new type**: a list of lists of
  literals evaluated as an OR of ANDs (`Std.Sat.CNF.evalDNF`), on the same
  carrier `Std.Sat.CNF ℕ` and therefore with the same audited serialization
  (`Std.Sat.CNF.serialize`/`decode`). This is deliberate and documented — the
  phase-3 round-1 audit's guidance (finding 7): the DNF rendering is presented
  **as a fragment**, never silently identified with [AB09]'s general Boolean
  formulas; the fragment is exactly what Example 2.21's reduction produces,
  and `TAUTOLOGY` over it carries the example's full mathematical content
  (`TCSlib.Complexity.ClassNP.Tautology`).
* **The dual map negates every literal in place**:
  `¬(⋀_i ⋁_j v_ij) = ⋁_i ⋀_j ¬v_ij` — same list shape, each polarity bit
  flipped. No distributive expansion occurs anywhere (which would be
  exponential); the dual is size-preserving.
* Under the DNF reading the conventions dualize: the empty formula evaluates
  `false` (empty OR) and an empty clause evaluates `true` (empty AND) — the
  exact mirror of the CNF conventions.

## Main definitions

* `Std.Sat.CNF.evalDNF` — the OR-of-ANDs evaluation of the carrier.
  [AB09, §2.6.1]
* `Std.Sat.CNF.dual` — the literal-negating De Morgan dual.
* `Std.Sat.CNF.DNFTautology` — every assignment satisfies the DNF reading.
  [AB09, §2.6.1]

## Main results

* `Std.Sat.CNF.evalDNF_dual` — the pointwise De Morgan law:
  the dual's DNF value is the negation of the CNF value.
* `Std.Sat.CNF.dnfTautology_dual_iff` — the dual is a DNF tautology iff the
  CNF is unsatisfiable; Example 2.21's pivot. [AB09, §2.6.1]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Example 2.21, pp. 55-56.)
-/

namespace Std.Sat.CNF

/-- The **DNF reading** of the carrier: an OR of ANDs — the formula holds when
some clause has all its literals satisfied (`(v, b)` satisfied iff the
assignment gives `v` the value `b`, as in the CNF reading). Empty formula:
`false`; empty clause: `true` — the duals of the CNF conventions. -/
def evalDNF (a : ℕ → Bool) (φ : CNF ℕ) : Bool :=
  φ.any fun C => C.all fun ℓ => a ℓ.1 == ℓ.2

/-- The **De Morgan dual**: negate every literal in place, keeping the list
shape — `¬(⋀_i ⋁_j v_ij) = ⋁_i ⋀_j ¬v_ij` read dually. Size-preserving; no
distributive expansion. -/
def dual (φ : CNF ℕ) : CNF ℕ :=
  φ.map (List.map fun ℓ => (ℓ.1, !ℓ.2))

/-- The formula is a *tautology under the DNF reading*: every assignment makes
`evalDNF` true. [AB09, §2.6.1]'s tautology notion, on the DNF fragment. -/
def DNFTautology (φ : CNF ℕ) : Prop :=
  ∀ a : ℕ → Bool, φ.evalDNF a = true

/-- **The pointwise De Morgan law**: the dual's DNF value is the negation of
the CNF value, at every assignment.

**Proof sketch.** Induction on the clause list with `Bool.not_and`/`Bool.not_or`
pushed through `List.any`/`List.all` (`List.any_map`, `List.all_map`,
`Bool.not_all` in its Mathlib spelling): at the literal level,
`a v == !b = !(a v == b)` by cases on the two booleans; at the clause level the
negated OR of literals is the AND of negated literals; at the formula level
the negated AND of clauses is the OR of negated clauses. -/
theorem evalDNF_dual (φ : CNF ℕ) (a : ℕ → Bool) :
    (dual φ).evalDNF a = !(φ.eval a) := by
  have hclause (C : Clause ℕ) :
      (C.map fun ℓ => (ℓ.1, !ℓ.2)).all (fun ℓ => a ℓ.1 == ℓ.2) = !(C.eval a) := by
    induction C with
    | nil => rfl
    | cons ℓ C ih =>
        simp only [List.map_cons, List.all_cons, Clause.eval_cons, ih, Bool.not_or]
        cases a ℓ.1 <;> cases ℓ.2 <;> rfl
  induction φ with
  | nil => rfl
  | cons C φ ih =>
      change ((C.map fun ℓ => (ℓ.1, !ℓ.2)).all (fun ℓ => a ℓ.1 == ℓ.2) ||
        (dual φ).evalDNF a) = !(C.eval a && eval a φ)
      rw [hclause, ih, Bool.not_and]

/-- **The De Morgan pivot of Example 2.21**: the dual is a DNF tautology iff
the original CNF is unsatisfiable.

**Proof sketch.** Unfold both sides through `Std.Sat.CNF.evalDNF_dual`:
`(dual φ).evalDNF a = true ↔ φ.eval a = false` pointwise, so "every `a`
satisfies the dual" is "no `a` satisfies `φ`", which is the negation of
`Std.Sat.CNF.Satisfiable`. -/
theorem dnfTautology_dual_iff (φ : CNF ℕ) :
    (dual φ).DNFTautology ↔ ¬φ.Satisfiable := by
  simp only [DNFTautology, evalDNF_dual, Satisfiable, not_exists,
    Bool.not_eq_true', Bool.eq_false_iff]

end Std.Sat.CNF

## ===== audits/logs/ch2-e1-axioms.log =====

'Complexity.polyTimeComputable_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.PolyTimeComputable.output_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.PolyTimeComputable.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.PolyTimeReducible.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.PolyTimeReducible.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_P_of_polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_eq_NP_of_NPHard_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NPComplete.mem_P_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.MultiTapeTM.toNDTM_runWith' depends on axioms: [propext, Quot.sound]
'Turing.NDTM.HaltsWithin.mono' depends on axioms: [propext, Quot.sound]
'Turing.FinNDTM.AcceptsWithin.mono' depends on axioms: [propext, Quot.sound]
'Complexity.NTIME.mono' depends on axioms: [propext, Quot.sound]
'Complexity.DTIME_subset_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NTIME_eq_empty_of_exists_zero' depends on axioms: [propext, Quot.sound]
'Complexity.P_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.compl_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_coNP_iff_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_NP_inter_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NP_eq_coNP_of_P_eq_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_EXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.eval_congr_of_lt_numVars' depends on axioms: [propext, Quot.sound]
'Complexity.exists_cnf_boolFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Std.Sat.CNF.parse_serialize' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.decode_serialize' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.numVars_decode_le' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.evalDNF_dual' does not depend on any axioms
'Std.Sat.CNF.dnfTautology_dual_iff' depends on axioms: [propext, Quot.sound]

## ===== scripts/ab_ch1_module_order.txt =====

TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Deterministic
TCSlib/Complexity/TuringMachine/StateRenaming
TCSlib/Complexity/TuringMachine/Finite
TCSlib/Complexity/TuringMachine/Oracle
TCSlib/Complexity/TuringMachine/Simulation
TCSlib/Complexity/TuringMachine/Sweep
TCSlib/Complexity/TuringMachine/Composition
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
TCSlib/Complexity/ClassP/DTIME
TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/ClassP/P
TCSlib/Complexity/ClassP/ModelInvariance
TCSlib/Complexity/ClassP/Examples
TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/Uncomputability/Computable
TCSlib/Complexity/Uncomputability/Diagonalization
TCSlib/Complexity/Uncomputability/Halting
TCSlib/Complexity/TuringMachine/Nondeterministic
TCSlib/Complexity/Formulas/CNF
TCSlib/Complexity/Formulas/CNFEncoding
TCSlib/Complexity/Formulas/DNF
TCSlib/Complexity/ClassNP/PolyTime
TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/CoNP
TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/Reductions
TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/TuringMachine
TCSlib/Complexity/ClassP
TCSlib/Complexity/Uncomputability
TCSlib/Complexity/Formulas
TCSlib/Complexity/CookLevin
TCSlib/Complexity/ClassNP
