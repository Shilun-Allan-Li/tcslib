# Chapter 2, epoch 2, batch B — partial continuation delivery

**Status: incomplete. None of the three headline targets is closed.** This archive
uses the brief's partial-delivery exception. It is not a passing completion of the
batch's no-`sorryAx` gate. The first target is reduced to one explicit native
verifier-construction obligation; the second and third targets are untouched to
preserve fill order. All 32 new private declarations are complete, with no new
private admissions.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Base branch: `complexity/arora-barak-ch1`.
Base commit: `6c09453e6af59ff1575060b66196d28812800d24`.
Working branch: `fill/ch2-e2-B`, created from that exact base as the brief requires.
Delivery commit: `43620097f4f6d934ed383e54eb0ff950e4bdfe99`.
One agent; no delegation. No push or PR was made.

## Target disposition and exact frontier

| Order | Target | Disposition |
|---|---|---|
| 1 | `ntime_poly_subset_NP` | Partial. Coefficient `2*a`, verifier language, and the entire certificate equivalence are supplied. The remaining local goal is `choiceVerifier N (2*a) c ∈ P`. |
| 2 | `NP_subset_iUnion_NTIME` | Original admission, unchanged; not advanced past the first target. |
| 3 | `NP_eq_iUnion_NTIME` | Original admission, unchanged. |

The completed work comprises:

- Unique splitting and a finite split-search specification, including explicit
  failure when no split exists.
- Forward padding and backward truncation of accepting choice words, using
  all-branch halting. The certificate equivalence has no admitted dependencies.
- A native deterministic simulation phase for a fixed NDTM, with disjoint input,
  choice and captured-output tapes. Its prepared-configuration contract has exact
  time `|u|+1`, including the final decision transition.
- A native three-tape copying phase. Given a prepared unary split countdown, it
  copies the input prefix and choice suffix in exactly `|x++u|+1` transitions,
  preserving empty physical output throughout.

**Neither prepared-configuration theorem is a theorem about running from the
machine's ordinary blank-tape initial configuration.** The finite search is a
Lean function specification, not a native polynomial-time implementation. No
polynomial-time conclusion is inferred merely from its being a total function.

To close the first target, a continuation must:

1. Implement native input-length measurement, the explicit polynomial arithmetic,
   and `certificateSplit`; budget them on all inputs before assuming validity.
2. On search failure, halt with the singleton false verdict. On success, prepare
   the unary split countdown and reset the physical input head to its proper
   initial position before the copying phase.
3. Embed the proved copier and simulator in one finite machine with disjoint
   source and administrative tapes. Rewind the two copied buffers from their
   right blanks, including the unconditional first left move and empty-word cases.
4. Enter the simulation with the source's initial finite state, blank source work
   tapes, empty capture tape, virtual input head one, and choice head zero. Preserve
   the administrative tapes and physical-output silence across phase boundaries.
5. Prove the timed phase-composition invariant and a single pointwise polynomial
   bound for all inputs, then apply `mem_P_of_dtime_le` or `mem_P_iff` to the
   remaining verifier-membership goal.

Only then should the continuation proceed to the guessing construction and the
final antisymmetry theorem. No `exists_comp_partial` or untimed `Computes`
substitution is used in this delivery.

## Binding forward invariant table

Each discharge below is explicitly limited to the proved phase's preconditions.

| Required component | Lemmas and remaining integration work |
|---|---|
| Source input and boundary clamping | `choiceCore_step` uses the public `bufferTape_inputSymbol` and `virtualMove_correct` lemmas. The source input has its own exact buffer, so it cannot expose the first certificate bit. `choiceCore_run` preserves the guarded read and clamping through all steps. `choiceCore_initial_tag` covers initial position one, including empty input. Installing that prepared buffer from the native initial configuration remains open. |
| Choice tape and choice alignment | `choiceCore_step` reads exactly `u[j]` and advances the choice head once. `choiceCore_run` identifies the source run with `runWith (u.take t)`. Its halted-source case absorbs all subsequent source steps. `choiceCopy_timed` supplies exact copied words once the countdown is prepared. Connecting the administrative phases before source step zero remains open. |
| Source state and disjoint tapes | `choiceCore` has finite control `Option N.State × Bool × Option Bool`. `choiceTapes` partitions source work tapes from three auxiliary tapes. The full configuration equalities in `choiceCore_step` and `choiceCore_run` preserve all source tapes and positions, not just the verdict. The integrated startup embedding remains open. |
| Output capture and exact verdict | `captureEmission_correct`, `capturedSummary_true`, `choiceCore_step`, `choiceCore_finish`, and `choiceCore_timed`. Every emission, including one on a halting transition, updates the complete capture tape and its finite summary. Physical output stays empty until the final transition. The final bit is true exactly for a halted source with output `[true]`; all other completed outputs and a live `[true]` reject. |

The implementation uses a physical head on the copied input and a finite boundary
tag instead of the sketch's binary position counter. This is the existing guarded
input-relocation representation proved by `virtualMove_correct`; its overhead is
one native step per source step. A separate capture tape retains the complete
output; the finite summary is only an exact singleton-test aid. This representation
choice and the partial frontier are recorded in an **append-only implementation
note** on the first target's docstring. Its original sketch and attribution remain.

## Binding reverse-direction five-step mapping

| Step | Status |
|---|---|
| 1. Evaluate the certificate length, initialize countdown, and schedule guesses independently of their values | Open; no reverse-direction machine or lemma is claimed. |
| 2. Cover and extract every exact-length certificate at its actual physical choice positions, including zero coefficient | Open. The forward simulator's choice alignment is not a proof of this reverse contract. |
| 3. Assemble the verifier input and run the relocated, captured verifier with identical tables outside guessing | Open; no reuse of the prepared forward core is asserted as a completed reverse construction. |
| 4. Prove all-branch totality, branch acceptance equivalence and common-budget padding | Open. The public epoch-1 monotonicity lemmas remain available, but this delivery supplies no reverse-machine hypotheses for them. |
| 5. Normalize the complete construction's time bound into a fixed-degree `NTIME` component | Open; no unproved machine-cost estimate is presented as a proved bound. |

## All new declarations

All names below are private within `Complexity`. There are 10 definitions and 22
lemmas; no new public declarations, axioms, unsafe declarations, or private sorries.

| Kind | Private declaration |
|---|---|
| lemma | `certificate_split_strictMono` |
| lemma | `certificate_split_unique` |
| def | `certificateSplit` |
| lemma | `certificateSplit_spec` |
| lemma | `certificateSplit_none_iff` |
| lemma | `certificateSplit_complete` |
| def | `choiceVerifier` |
| lemma | `choiceVerifier_append` |
| lemma | `choiceVerifier_no_split` |
| lemma | `acceptsWithin_iff_of_halts` |
| lemma | `choice_budget_le` |
| lemma | `choice_certificate_iff` |
| def | `capturedSummary` |
| def | `captureEmission` |
| lemma | `captureEmission_correct` |
| lemma | `capturedSummary_true` |
| def | `choiceTapes` |
| def | `choiceCore` |
| def | `choiceCoreCfg` |
| lemma | `choiceCore_step` |
| lemma | `choiceCore_run` |
| lemma | `choiceCore_finish` |
| lemma | `choiceCore_timed` |
| lemma | `choiceCore_initial_tag` |
| def | `copyTapes` |
| def | `choiceCopy` |
| def | `choiceCopyCfg` |
| lemma | `choiceCopy_prefix_step` |
| lemma | `choiceCopy_suffix_step` |
| lemma | `choiceCopy_prefix_run` |
| lemma | `choiceCopy_suffix_run` |
| lemma | `choiceCopy_timed` |

## Admissions and frozen surface

The owned file still contains exactly eight explicit `sorry` occurrences, the same
count as the base. Their current declarations and line numbers are:

| Declaration | Explicit `sorry` line |
|---|---|
| `ntime_poly_subset_NP` | 682 |
| `NP_subset_iUnion_NTIME` | 713 |
| `NP_eq_iUnion_NTIME` | 723 |
| `ntime_expPow_subset_NEXP` | 743 |
| `NEXP_subset_iUnion_NTIME` | 764 |
| `NEXP_eq_iUnion_NTIME` | 775 |
| `EXP_eq_NEXP_of_P_eq_NP` | 811 |
| `P_ne_NP_of_EXP_ne_NEXP` | 817 |

The first three rows are unfinished in-scope targets, permitted here only under
the brief's partial-delivery exception. They are not sanctioned admitted
dependencies for a completed batch. The final five rows are the untouched epoch-3
padding cluster. All other campaign admissions are unchanged.

`verification/surface-check.json` and its reproducible script confirm:

- Exactly one changed tracked path:
  `TCSlib/Complexity/ClassNP/Nondeterminism.lean`.
- All eight existing public declaration headers are identical after stripping
  comments and normalizing whitespace, with identical order and no additions or
  removals.
- From the second target's docstring through the end of the file, source bytes are
  identical to the base. This includes both later in-scope targets and all padding.
- Every original block comment is preserved, except for the documented append-only
  note on the first target. No attribution was changed.
- `git diff --check` passes. The file exceeds the 600-line target because ownership
  restricts this phase's private helpers to this file; it remains below 1000 lines.

Requested shared lemmas: **none**. Statement escalations: **none**; the frontier is
missing construction work, not a demonstrated defect in a frozen statement.

## Verification

- Final full sweep: **PASS**, all 53 modules, exit 0, zero `error:` lines, fresh oleans.
- Admission warnings: **32**, unchanged from the base campaign count.
- Axiom command: exit 0; all 35 requested declarations were printed.
- New private declarations: **32/32 within** `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- Headline targets: **0/3 closed**; all three contain `sorryAx`. The complete-batch axiom gate fails.
- Style lint: **0 FAIL, 0 WARN** over the ten ClassNP files.
- Surface comparison, patch replay and git bundle verification: **PASS**.

The environment uses Lean 4.25.0 and the committed dependency manifest. The required
`lake exe cache get` was invoked once. It ended with server failures and a missing
shared temporary cache file. Completed downloads were copied to an isolated task
cache and unpacked; disk exhaustion during unpacking required pruning this
checkout's generated cache to the campaign dependency closure. These setup
failures are recorded in the included setup logs. The final sweep below was run
after recovery. No `lake build` was run.

The bootstrap was resumed after its first missing dependency. Iteration checked
the owned module; the final owned-and-downstream check and the final full sweep
both use the committed `scripts/lean_check_tree.sh`, which removes each old olean
and requires a fresh nonempty replacement, Lean exit zero, and no `error:` line.

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

The full axiom output is `verification/axiom-print.log`. Its three target lines
are reproduced here to make the incomplete status unmistakable:

```text
'Complexity.ntime_poly_subset_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.NP_subset_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.NP_eq_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Archive and replay

The archive contains this report, the full modified source at its repository path,
one `git format-patch`, an incremental git bundle, the raw final sweep and axiom
logs, the module order, surface and style checks, and `SHA256SUMS`. The checksum
file covers every other archive member.

The bundle verifies against the recorded base. The patch was applied to a separate
copy of the base source and reproduced the delivered source byte-for-byte.
`verification/patch-replay.log` and `verification/bundle-verify.log` record these
checks. The patch preserves the local commit's Codex authorship. No remote branch
was modified.

To recheck the surface in a repository containing the base and applied patch, run
`python3 verification/verify_surface.py /path/to/tcslib`. For elaboration, use the
brief's full module loop and the included `AxiomChecks.lean` on the resulting fresh
olean tree. A zero-error sweep here certifies elaboration of a partial source; it
does not close the three headline proofs.
