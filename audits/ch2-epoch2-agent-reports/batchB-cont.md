# Chapter 2, E2 continuation, batch B — partial delivery

**INCOMPLETE: one of three public targets is closed.** This delivery uses the
continuation/partial-delivery allowance in `briefs/ch2-e2cont-batchB.md` and
`briefs/ch2-epoch2-batchB.md`. It is not a passing completion of the entire
batch's no-`sorryAx` gate. The forward compilation is complete; the reverse
compilation has proved native components but still lacks its integrated
controller. The equality remains untouched to preserve target order.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Requested base branch: `complexity/arora-barak-ch1`.
Required and actual source base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
Working branch: `fill/ch2-e2cont-B`.
Delivery commit: `2239b0f3b128c5acf4f35d5e83918b8aa0e6b492`.
The continuation brief was read from `cc103db9d9f00e28924a685919629be9b3ec1b63`,
the next commit on the requested branch; the source branch was then created
from the brief's required base. No other branch was changed. No push or PR.
Single-agent execution; no delegation.

## Public targets and exact remaining frontier

| Order | Target | Result |
|---|---|---|
| 1 | `ntime_poly_subset_NP` | **Proved.** Native split search, failed-split rejection, paired-input loading, both rewinds, source simulation, and the uniform polynomial bound close `choiceVerifier ∈ P`. Kernel admission roots are empty. |
| 2 | `NP_subset_iUnion_NTIME` | **Incomplete.** Proved a native guessing phase, its exact physical-position extraction/coverage, its unary-generator instance, and final time normalization. The whole NDTM controller remains the only admission in this target. |
| 3 | `NP_eq_iUnion_NTIME` | Original admission, byte-identical together with its docstring. Not filled ahead of target 2. |

The first target retains the predecessor's complete certificate equivalence.
The second target now extracts the verifier's timed witness and applies the
proved `cont_guess_normalize`. Its exact remaining local goal is:

```lean
-- L : Language Bool; C c : ℕ; V : Language Bool
-- hcert : ∀ x, x ∈ L ↔ ∃ u, u.length = C * (x.length + 1)^c ∧ x ++ u ∈ V
-- M : FinTM Bool; A d : ℕ
-- hM : M.DecidesInTime V (fun n => A * (n + 1)^d)
⊢ ∃ (K r : ℕ) (N : FinNDTM Bool),
    N.DecidesInTime L (fun n => K * (n + C * (n + 1)^c + 1)^r)
```

The native `contGuessTM` is a **phase**, not that missing decider. Its source
scheduler's completed state is a live, stationary return state; the phase
never claims all-branch halting. `cont_poly_guess_phase` runs its scheduler
on the unary word of length `n`, not on an arbitrary original input word.
The polynomial scheduler budget may include absorbed source steps; a host
must dispatch on an actual completed scheduler (for example its first halt)
and prove that seam, rather than infer a native clock from an upper bound.

A continuation should do the following, in this order:

1. Build the native host preserving the original input and installing its
   length-only scheduler/countdown. The library unary generator is available;
   its function-level contract alone does not assert value-independent
   running times on arbitrary original input strings. Relocating it to the
   unary input, or proving an equivalent normalization of input reads, is an
   explicit missing seam.
2. Embed the proved guessing table with source and administrative tapes
   disjoint. Translate its physical write mask into the complete branch
   word, including the startup offset; all non-guess choices are ignored.
   Reuse `cont_guess_coverage` at the actual scheduler completion time.
3. Assemble the preserved original input followed by the captured guesses.
   Prepare the verifier with blank source tapes, empty capture output and
   virtual head one; prove the two tables coincide outside guessing. Capture
   its completed output, including any halting emission, and issue one bit.
4. Prove every branch completes, that its certificate has the exact required
   length, and that branch acceptance is precisely verifier membership. Use
   a common upper bound; actual verifier halting times may depend on guesses.
5. Bound the entire construction by the displayed envelope. The proved
   `cont_guess_normalize` then closes target 2, including forward padding and
   backward truncation. Only then fill target 3 by antisymmetry.

## Forward invariant table: complete discharge

| Required component | Discharge |
|---|---|
| Source input and boundary clamping | `cont_parse_run`, `cont_copy_run`, `cont_rewind_input`, `cont_start_core` install the exact undoubled input buffer and initial virtual head. `cont_core_run` embeds the unchanged `choiceCore_step`/`choiceCore_run`, whose `bufferTape_inputSymbol` and `virtualMove_correct` enforce both blanks and repeated outward-move clamping. `choiceCore_initial_tag` includes the empty input. The choice suffix is on a separate tape. |
| Choice tape and source-choice alignment | `cont_copy_run` copies exactly the suffix; `cont_rewind_choices` returns its head to zero. Administrative steps do not invoke the source simulation. The unchanged `choiceCore_run` consumes one copied bit per source step, absorbing halted source configurations. |
| Source state and disjoint tapes | `contLoadCfg` keeps all original source tapes and the source-output capture tape blank during setup. `cont_start_core` installs the complete prepared initial configuration. `cont_core_run` is an exact configuration equality using the public state-renaming definitions; it preserves the predecessor's tape partition and full source-state invariant. |
| Output capture and exact verdict | All successful loader steps are silent. `cont_pair_empty` emits exactly `[false]` for split failure. The unchanged `captureEmission_correct`, `capturedSummary_true`, and `choiceCore_timed` capture all source emissions and accept exactly a halted source with output `[true]`. A live `[true]`, empty output, false output, and multi-bit output reject. `cont_pair_computes` and `cont_split_answer` connect this to the completed verifier output. |

The predecessor's `choiceCopy` family and all other 32 private declarations
are retained byte-for-byte. The new loader uses the library's encoded split
output directly, so it does not need a separate unary split countdown. This
is documented in an append-only note on the first public target.

## Split convention and time ledger

The exact bridge in this owned file is

```lean
cont_split_bridge (C c m : ℕ) : solveSplit C c m = certificateSplit C c m
```

It is proved by reflexivity. **There is no coefficient shift for batch B.**
The recorded `solveSplit (C+1) c = certificateSplit C c` vocabulary note
concerns the marker-padding parser in `ClassNP/NP.lean`, whose formula has
coefficient `C+1`. This file's predecessor already defines its own
`certificateSplit C c` using coefficient `C`. Therefore the public forward
target instantiates split search at coefficient `2*a`, degree `c`, exactly.
Applying the unrelated shift here would be incorrect.

| Phase | Proved bound or equality |
|---|---|
| Library split search | `A * (m+1)^(c+2)` on every original verifier input, successful or failed |
| Emitted split length | At most `2*m+2`, by `cont_split_length` |
| Paired parser | Exactly `2*|x|+2`, by `cont_parse_run` |
| Suffix copy | Exactly `|u|`, by `cont_copy_run` |
| Buffer rewinds and dispatch | Exactly `|x|+|u|+3`, by `cont_start_core` |
| Unchanged source core | Exactly `|u|+1`, by `choiceCore_timed` |
| Full paired machine | `3*|x|+3*|u|+6 ≤ 3*(|pairEncode x u|+1)` |
| Timed composition startup | At most split-search budget plus emitted length plus 2, by `bufferedComp_start` |
| Complete verifier | At most `(A+13)*(m+1)^(c+2)`, by `cont_choiceVerifier_mem_P` |

All bounds are pointwise, including coefficient zero, degree zero and empty
strings. No untimed composition is used. The second stage is proved on every
possible first-stage output (valid pairs or the empty failure word); the
proof does not substitute an arbitrary time function at an inflated length.

## Reverse five-step contract: proved pieces and limitations

| Binding step | Proved here | Remaining |
|---|---|---|
| 1. Compute the explicit length, initialize control, and schedule guesses independently of their values | `contEmissionMask`, `cont_mask_length`, `cont_mask_count`; `contGuessTM` uses the deterministic scheduler's source bank and never reads guessed data. `cont_poly_guess_phase` supplies a polynomial unary-generator instance with a schedule depending only on `n`. | The whole host's original-input preservation, native unary-input preparation/relocation, countdown installation and phase entry. No completed implementation of this entire step is claimed. |
| 2. Certificate coverage and extraction at the actual physical write positions, including `C=0` | `contSelect`, `cont_select_length`, `cont_select_surjective`, `cont_guess_step`, `cont_guess_run`, `cont_guess_coverage`, `cont_poly_guess_phase`. They select emission positions, not the first `Q(n)` physical choices. Zero writes extract and cover only `[]`. | Lift the standalone phase's correspondence to the complete branch word and its startup offset. |
| 3. Assemble `x++u`, initialize and capture the relocated verifier, identical tables outside guessing | The forward construction provides relevant loader and timed relocation precedents, but is not a reverse-host proof. | Entire integrated reverse assembly/verifier phase and its all-branch termination proof. |
| 4. Branch acceptance equivalence and padding to a common bound | `cont_guess_normalize` proves budget transfer using all-branch halting and `acceptsWithin_iff_of_halts`, once a whole-decider contract is provided. | Acceptance equivalence and all-branch totality for the actual host. |
| 5. Normalize the complete envelope into one `NTIME` component | `cont_guess_time_bound` proves the exact coefficient `K*(C+1)^r*2^(r*max 1 c)` and exponent `r*max 1 c`; `cont_guess_normalize` packages the result. | Establish the displayed complete-envelope hypothesis for the missing host. |

## Library and existing contracts consumed

| Contract | Use |
|---|---|
| `Turing.FinTM.computesFunInTime_splitSolve` | The actual first-stage machine in `cont_choiceVerifier_mem_P` |
| `Turing.FinTM.computesFunInTime_polyUnary` | Concrete scheduler in `cont_poly_guess_phase` |
| `Turing.captureAction` | The transition transformer in `contGuessTM`; its one-step correspondence is proved locally in `cont_guess_step` |
| `Turing.Action.mapState`, `Turing.Cfg.mapState` | Embed the unchanged deterministic core without duplicating these public definitions |
| `Turing.MultiTapeTM.runFrom_comm_of_step` | Exact core embedding invariant |
| `Turing.FinTM.bufferedComp_start`, `bufferedSecondCfg_run` | Timed, captured first stage and relocated paired machine in the completed forward compiler |
| `Complexity.mem_P_iff` | Conclude polynomial-time verification and obtain the reverse verifier witness |
| `Complexity.succ_pow_le`, `Turing.NDTM.HaltsWithin.mono`, predecessor `acceptsWithin_iff_of_halts` | Reverse-envelope normalization and correct acceptance transfer |

`capture_run` and the private `timed_rewind` are not falsely claimed as
invoked contracts. The forward source core already captures output; this
host directly loads its prepared tapes, proves its own two timed rewinds,
and then uses the public timed buffered-composition interface.

## All 36 new private declarations

Seven definitions and 29 lemmas; no new public declarations or private admissions.

| Kind | Name |
|---|---|
| lemma | `cont_split_bridge` |
| def | `contPairTM` |
| def | `contLoadCfg` |
| lemma | `cont_core_run` |
| lemma | `cont_rewind_choices` |
| lemma | `cont_rewind_input` |
| lemma | `cont_write_apply` |
| lemma | `cont_load_read` |
| lemma | `cont_load_right` |
| lemma | `cont_copy_run` |
| lemma | `cont_start_core` |
| lemma | `cont_suffix_run` |
| lemma | `cont_parse_double` |
| lemma | `cont_parse_separator` |
| lemma | `cont_parse_run` |
| lemma | `cont_pair_computes` |
| lemma | `cont_pair_empty` |
| def | `contSplitWord` |
| lemma | `cont_split_length` |
| lemma | `cont_split_answer` |
| lemma | `cont_choiceVerifier_mem_P` |
| def | `contSelect` |
| lemma | `cont_select_length` |
| lemma | `cont_select_surjective` |
| def | `contEmissionMask` |
| lemma | `cont_mask_length` |
| lemma | `cont_mask_count` |
| def | `contGuessTM` |
| def | `contGuessCfg` |
| lemma | `cont_guess_step` |
| lemma | `cont_guess_run` |
| lemma | `cont_guess_initial` |
| lemma | `cont_guess_coverage` |
| lemma | `cont_guess_time_bound` |
| lemma | `cont_guess_normalize` |
| lemma | `cont_poly_guess_phase` |

## Frozen surface, admissions and policy

Only the tracked path `TCSlib/Complexity/ClassNP/Nondeterminism.lean` changed.
All eight public headers are identical after comment stripping and whitespace
normalization; public order and inventory are unchanged. The original 32-private
block is byte-identical. All original docstrings remain, with append-only
implementation/checkpoint notes on the first two targets. From the third
public target's docstring through the end, source bytes are unchanged.
`git diff --check` passes. `surface-check.json` and `verify_surface.py` provide
reproducible evidence.

The final file has **1,670 lines, 88,871 UTF-8 bytes**. SHA-256:
`7268c31897087c78aa95f3849e855692e3ff5edcfb3a02306c8e8bfc1af9819e`.

| Remaining explicit admission | Line | Disposition |
|---|---:|---|
| `NP_subset_iUnion_NTIME` | 1564 | In-scope partial frontier described above |
| `NP_eq_iUnion_NTIME` | 1574 | In-scope, untouched pending target 2 |
| `ntime_expPow_subset_NEXP` | 1594 | Epoch 3, untouched |
| `NEXP_subset_iUnion_NTIME` | 1615 | Epoch 3, untouched |
| `NEXP_eq_iUnion_NTIME` | 1626 | Epoch 3, untouched |
| `EXP_eq_NEXP_of_P_eq_NP` | 1662 | Epoch 3, untouched |
| `P_ne_NP_of_EXP_ne_NEXP` | 1668 | Epoch 3, untouched |

The owned file's explicit admission count falls from 8 to 7. The five padding
admissions remain exactly as inherited. No other file's admissions changed.

Statement escalations: **none**; the unfinished compiler is missing proof/
construction work, not evidence of a false frozen statement. Requested shared
lemmas: **none**. File-size exception: the brief's exclusive ownership and its
prohibition on moving the predecessor's families require these helpers to stay
in the owned file. A serial split/dedup is deferred to the recorded E5 work;
no other source file is changed to evade this ownership rule. The style lint
has 0 FAIL and 2 WARN over the ten ClassNP files: this size warning and the
pre-existing `TMSAT.lean` size warning. No new compiler lint warnings occur
in the owned module beyond its seven documented admissions.

## Verification

- Lean **4.25.0**; mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**.
  Installed dependency revisions match the manifest (`environment.log`).
- Required `lake exe cache get`: invoked **once**, completed successfully
  (`cache-get.log`). No `lake build` invocation. The pinned existing toolchain
  was reused; generated dependency artifacts outside this task's import
  closure were pruned locally after cache extraction to recover disk space.
- Final **57/57** fresh-module sweep: exit **0**, **zero `error:` lines**,
  `FULL_SWEEP_COMPLETE`. The committed check script removes each old olean
  before checking and requires a fresh nonempty replacement.
- Final admission warnings: **27**, down from the pinned campaign baseline 28.
- Owned-and-downstream recheck: pass (`downstream-final.log`).
- Kernel closure traversal and prints on the final fresh tree: exit **0**.
  First target has empty admission roots and only the standard triple.
  **All 36 new helpers and all their generated descendants (114 declarations
  total) have empty admission roots and axiom sets within the standard triple.**
- The other two public targets still depend on `sorryAx`, each rooted in its
  own admission. Therefore **the complete-batch axiom gate does not pass**.
  The instrument's `PARTIAL_CLOSURE_AUDIT_PASS` means exactly the stated partial
  expectations passed, not that those targets were completed.
- Statement/private/docstring/padding checks, two-patch replay and incremental
  git-bundle verification: pass. Patch replay reproduces the source byte-for-byte.

Axiom prints and target admission roots:

```text
'Complexity.ntime_poly_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NP_subset_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.NP_eq_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
TARGET ROOTS Complexity.ntime_poly_subset_NP: []
TARGET ROOTS Complexity.NP_subset_iUnion_NTIME: [Complexity.NP_subset_iUnion_NTIME]
TARGET ROOTS Complexity.NP_eq_iUnion_NTIME: [Complexity.NP_eq_iUnion_NTIME]
```

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
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

## Flat archive and replay

`fill-ch2-e2cont-B.zip` is flat: every member, including `SHA256SUMS`, is at
the archive root. `Nondeterminism.lean` is the complete modified source and
maps to `TCSlib/Complexity/ClassNP/Nondeterminism.lean` in the repository.
The archive also contains this report, two format-patches, the incremental
git bundle, the full final sweep and axiom logs, the axiom program, module
order, environment/cache record, surface verifier, declaration inventory,
style result, and replay/bundle validation logs. `SHA256SUMS` covers every
other archive member; no toolchain, dependency cache, or olean is included.

From an extracted archive, `sha256sum -c SHA256SUMS` verifies the payload.
Apply the two numbered patches in order with `git am` to a checkout of the
required base; this preserves Codex authorship. The bundle is an alternative
containing the same two commits and requires that base to be available.
For elaboration, use the committed 57-module order/check script under the
pinned toolchain, then run `AxiomChecks.lean` with the fresh olean tree and
pinned package build directories on `LEAN_PATH`. The source-header verifier
can be run as `python3 verify_surface.py /path/to/tcslib` on the delivery branch.

## Notation

`n` is original input length; `m` is a verifier input length. `x,u` are input
and certificate words; `|w|` is word length. `C,c` are the exact certificate
coefficient and degree. `a` is the original NTIME coefficient. `A` denotes
the relevant deterministic time coefficient; `d` is the verifier's degree.
`K,r` are the missing reverse compiler's whole-time envelope parameters.
`Q(n)=C(n+1)^c`; `T` is a physical scheduler budget. Machine and lemma names
refer to the declarations in the delivered source and pinned library.
