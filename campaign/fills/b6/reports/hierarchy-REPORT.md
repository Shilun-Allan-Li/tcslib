# B6 hierarchy fill — final report

**Outcome:** `Complexity.space_hierarchy` and `Complexity.LOGSPACE_ssubset_PSPACE` are
proved on `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. All 43 new private
declarations are also admission-free. Checkpoint 8, reached last, proves the padding implication
and ends in the specifically permitted escalation **E-PAD**: the exact padded-language
linear-space decider. `SPACE_linear_ne_NP` keeps its original `sorry` and literal “Proof sketch”.
F6 is byte-preserved. No new admission, push or PR.

The full 52-module downstream sweep passes with the two expected Hierarchy sorry warnings
and two unchanged baseline style warnings in `Randomized/Classes`
(1,274.870 seconds summed wall time; peak RSS 2,528,956 KiB).
The 71-definition seal passes, all 75 controls pass unsealed and fail sealed, and the final
321-name import probe passes. Campaign lint: 0 FAIL, 81 WARN. The final text screen has 12 new pairs, all below 90%; **new copies: none**.

## Identity and authorized scope

- Exact base: `e6bc196838b4e2675e4214306c730e7404624ab8`.
- Base source blob: `287acce8326a1de271dfa6be2cc3776f3a2caa32`.
- Local branch: `fill/b6-hierarchy`, created at exactly the base after the ancestor check passed.
- Final commit: `30222bbd264a75057ae0779535a32e1a30dd2394`.
- No rebase, merge, cherry-pick, push or PR.
- Only tracked change: `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`, in regions (a)–(d).
  All four public statements are byte-identical to the base. The complete `space_universal`
  docstring/body and its module main-results entry are byte-identical. Imports are exactly the
  five base imports plus the four required overlay imports.
- Source: 2,563 physical lines, four public declarations and 43 private declarations.
  The standalone linter counts the trailing empty split segment as line 2,564. No new admission,
  no forbidden R3 row, no directly cited foreign private, and no added line over 100 characters.

The dispatch files were verified against the supplied manifest before reading:

| File | SHA-256 |
|---|---|
| `b6-fill-hierarchy.md` | `3c92e156529b5a7f1f061e3b1d5beaf0918fe3b11355e34362441b56c36bd357` |
| `fill-environment-addendum.md` | `9f5bd5e74bb767e50a6e7a372e98a5567998ec14be432c1dfb7ff8856eb9bd28` |

The first local serialization appended a newline; writing the fetched bytes exactly corrected
that local serialization before verification/read. Neither remote artifact mismatched.

## Checkpoints and declarations

| Checkpoint | Status |
|---|---|
| 1 | Overlay, inclusion and permitted documentation cleanup committed and checked |
| 2 | Validation, returning radius capture, both rewinds and framed initializer committed and checked |
| 3 | Complete simulation suffix: runner, test, all three exits, opposite answer and head envelope |
| 4 | Full validation/capture/rewind/record/suffix composition; all-input space bound; binary language in SPACE g |
| 5 | Normalization and universal-machine window lemma committed and checked |
| 6 | Complete public hierarchy proof, admission-free |
| 7 | Complete public logarithmic-space strictness corollary, admission-free |
| 8 | Last checkpoint: conditional padding proof complete; named decider escalation E-PAD |

| Private declaration | Role |
|---|---|
| `sph_inclusion` | Mandatory inclusion proof via the finite exceptional prefix and SPACE.mono_const |
| `sph_code_window` | Normalize a smaller-space decider, pad only its payload, and obtain the universal halted window summary |
| `sph_sq_le_two_pow` | Mandatory square-versus-exponential arithmetic |
| `sph_logSpace_dom` | Mandatory eventual logarithmic domination |
| `sph_logspace_ssubset` | Mandatory corollary from an explicit hierarchy hypothesis |
| `sphRightTM` | Permitted one-step input-head move leaf |
| `sph_right_run` | Framed run, positive input position, first return and unchanged work heads |
| `sphEmitTM` | Permitted one-step verdict emitter leaf |
| `sph_emit_run` | One-symbol emission and halt, with unchanged work heads |
| `sphDigit` | Finite validator predicate on the rich alphabet |
| `sph_fold_valid` | The fold accepts exactly digit-embedded binary words, including empty input |
| `sph_validation_run` | Framed validation with first-exit cut and unchanged work heads |
| `sphWitnessSel` | Witness bank after record, radius and both scratch banks |
| `sph_witness_cap` | Radius tape is outside the witness selection |
| `sph_radius_run` | Returning capture, complete output buffer, framed endpoint, silence and per-run space bound |
| `sphEmptySel` | Empty selection for the zero-work-tape input rewind |
| `sph_input_rewind_run` | Lifted input rewind via R1 on an arbitrary positive input position |
| `sphRewindsTM` | Published seams joining the right move, input rewind and radius rewind |
| `sph_rewinds_run` | Framed composed rewind endpoint and first return, with radius head at zero |
| `sphInitSel` | Initializer selection preserving the runner and witness banks |
| `sph_initial_record` | Framed initial record on the full tape plan, with first return and head envelope |
| `sph_select_fields` | Shared R1 selected-configuration readings via reconstruction; also used by the initializer |
| `sphRunnerSel` | Runner bank: record zero plus its separate scratch bank |
| `sph_runner_run` | Published runner by R1, including cuts, all exits, record endpoint and displacement bound |
| `sphRecordSel` | Single record-tape selection for the test |
| `sph_test_run` | Published record test by R1 with complete physical frame |
| `sphEmitContract` | Existing one-step emitter packaged as a stationary-head contract |
| `sphVerdictTM` | Published two-exit seam from record test to opposite-bit emitters |
| `sph_verdict_run` | Tested bit complement and shared head envelope |
| `sph_summary` | Returned stopped record aligned with a certified halting summary by stop uniqueness |
| `sph_seam_heads` | Common absolute interval transported through a published single-exit seam |
| `sph_seam_avoids` | A dispatched seam cannot revisit a different left-hand exit |
| `sph_written_record` | Shared record-boundary argument after an interior layout write |
| `sphRunnerTailTM` | Three published seams route halted, left and exhausted runner exits |
| `sph_runner_tail_run` | Complete three-exit suffix run and absolute head bound |
| `sph_suffix` | Uniform initial-record-to-halt suffix with opposite acceptance and displacement bound |
| `sph_record_suffix` | Initializer and complete runner suffix joined on the disjoint tape plan |
| `sph_record_size` | Record, radius digits and fixed overhead bounded by `(4*k+9)*g(n)` |
| `sph_valid_machine` | Complete post-validation machine and absolute head envelope on embedded words |
| `sph_halt_contract` | Public first-halt theorem packages a known bounded run as a branch contract |
| `sph_validated_machine` | Published two-exit validation branch, total on all rich inputs, with a summed space bound |
| `sph_linear_ne_NP_of_padding` | Separation from NP given the exact padded-language decider, using only published padding and preimage hosts |
| `sph_diagonal_language` | Total Boolean language, alphabet reduction and membership in SPACE g |

Every new private lemma has a literal Proof sketch; the small selection/leaf definitions have
public-facing descriptions. The only open target is `SPACE_linear_ne_NP`, with literal **Proof sketch** text. The
untouched F6 body `space_universal` remains `sorry` with its original docstring. Both completed
public target bodies and all 43 private declarations are admission-free. No other source file
or admission was changed.

## Tape plan and first phases

The physical tape count is `KI + KR + M.k + 2`: record 0, radius 1, initializer scratch
2 through `KI + 1`, runner scratch `KI + 2` through `KI + KR + 1`, then the witness bank.
The initializer selects only its own bank plus record/radius. The witness selection starts
strictly after both scratch banks, so its dirty endpoint cannot enter the future runner bank.

The validator uses `inputFoldTM_run_ofCfg` and recognizes exactly the image of `digitEmb`.
The returning radius phase chooses a first halting time of the constructibility witness,
lifts its binary run, and calls `embedSilentRetTM_run`. Its last emitted bit is included.
The radius tape ends at the buffer's length; outside the witness selection and radius tape,
all tape contents and heads are the supplied arbitrary frame. The physical output is unchanged.
Its proved per-run space bound is

```text
(KI + KR + M.k + 2) * (c * g |x| + |bits (g |x|)| + 1).
```

Here `KI` and `KR` are the initializer and runner scratch counts, `M` is the constructibility
witness, `c` its space coefficient, `g` the target bound, and `x` the binary input. This bound
is for the radius phase only, not yet a full-machine space claim.

The one-step right move handles a witness stopped at input position zero, and also handles the
right boundary. The lifted zero-tape input rewind runs by `embedEmitTM` on an empty selection.
`sphRewindsTM` joins it and `rewindTM` by two published general-configuration seams.
`sph_rewinds_run` restores input position one and radius-head position zero, preserves every
work-tape cell and the accumulated output, and proves the first-return cut. Empty captured
words are admitted. The initializer then calls `exists_recordInitTM` by R1, reading the selected
configuration through reconstruction and public field equations. Only its scratch bank must be
blank; the endpoint changes record tape zero only, with the published time and head bounds.

## Simulation suffix

`sph_suffix` applies `exists_configWindowRunnerTM` at the fixed finite machine with `Fin 3`,
`summaryTag` and initial tag zero. The tape-zero record and separate runner scratch bank are
selected by R1. On a halted exit, the returned record for an unspecified stopped round count
is matched to the certified halting summary by `windowRun_stop_unique`. The published record
test checks state `none` and tag one; the emitter writes the complementary bit. Left and
exhausted exits emit true. Exhaustion does not inspect the unspecified record.

Three existing single-exit seams handle the runner's three anchors. This is a composition of
published hosts, not a new seam transformer. The two verdict-test anchors use the published
two-exit seam and its branch contract. Every head stays within

```text
(CR + CT) * (recordLength M.k |x| s + 1)
```

of its initial physical position throughout the suffix. `CR` is the runner coefficient,
`CT` the record-test coefficient, `M` the fixed simulated machine, `x` its binary input and
`s` the radius. These constants do not depend on the input's code part. The suffix halts with
one output symbol on every valid initial record. Whenever `M` halts within the radius at its
configuration-count bound, that symbol is the opposite of its singleton-true acceptance.

## Full-machine space and binary packaging

The strengthened `sph_radius_run` additionally bounds every intermediate physical head by the
absolute ambient frame position plus `c*g(n) + |bits(g(n))|`. Selected heads use the public
space-to-window bound; the capture head uses output-prefix monotonicity; frame heads do not
move. `sph_rewinds_run` retains the published rewind envelope: displacement at most
`|bits(g(n))|+1`, with all cells preserved. The generic seam head lemma is moved earlier solely
so both compositions can share it.

Let `K = KI + KR + G.k + 2` be the physical tape count, `G` the constructibility witness,
`c` its space coefficient, `M` the fixed simulated machine, `n` the binary input length,
`s = g(n)`, and `L = recordLength M.k n s`. Put `C = CI + CR + CT`, the sum of the
initializer, runner and record-test head coefficients. The proof establishes, term by term:

```text
radius capture:       rR = c*s + |bits(s)|
through both rewinds: rW = rR + |bits(s)| + 1
record/suffix motion: rS = C*(L + |bits(s)| + s + 1)
combined radius:      rW + rS
                    <= (c + 3 + C*(4*M.k + 9))*s = B*s.
```

The arithmetic uses `|bits(s)| <= s`, `posWidth n <= 2*logSpace n <= 2*s`, the public formula
`L = M.k*(2*s+1) + posWidth n + M.k + 4`, and `1 <= s`. It does not cite the pending #208
bit-length lemma. Constants are chosen from fixed machines before the input and its code are
known. The record and both scratch banks are initially blank because the radius capture frames
them, and the initializer changes only record zero.

The actual `FinTM` starts the published input fold and uses `seamCompTM₂`/`Contract.branch`.
On a valid embedded word it enters the above machine; on a foreign symbol it emits false.
The branch contract uses a first halt of the valid run without changing its completed output.
Every work head is in `[-B*g(n), B*g(n)]` through the final halt, including on invalid rich
inputs. The public interval theorem gives

```text
D.spaceUsed(init ys, haltTime ys) <= K*(2*B*g(|ys|)+1).
```

The public halted-run space theorem extends this to every time. Applying
`decidesInSpace_of_alphabetReduction` yields a binary decider within
`c'*(K*(2*B*g(n)+1)+1)`. `SPACE.mono_const` absorbs this into `SPACE g`, since

```text
K*(2*B*g(n)+1)+1 <= (K*(2*B+1)+1)*g(n).
```

The language is the set of binary inputs on which the chosen total output of `D` is true.
The indicator equation is obtained through the already imported
`FinTM.toFinNDTM_haltsWithin_and_accepts_iff`: the permitted one-symbol emitter, instantiated
at that indicator bit, identifies acceptance using the public ND embedding/acceptance
readings. No indicator definition is unfolded. The shorter published
`LogProg.indicator_eq_decide` is outside the frozen nine-import closure, so no import was added
and no duplicate generic indicator lemma was introduced. Moving that convenience reading into
a lower imported module would simplify this local consumer calculation.

New notation in these displayed bounds: `rR`, `rW`, `rS` are the three intermediate radii;
`B` is their fixed combined coefficient; `c'` is alphabet reduction's coefficient. Other
symbols are defined immediately above the calculation. The construction proves the actual
existence of the diagonal language in `SPACE g`, not only a conditional packaging statement.

## Normalization and contradiction arithmetic already proved

The second private is `sph_code_window`. It normalizes an arbitrary smaller-space decider by
`one_work_tape_binary_spaceUsed` and `exists_codeTM_spaceUsed`, then uses the supplied universal
machine's per-code simulation contract. It returns a padded input and the exact time
`U₀.configBound x.length (g x.length)`, together with the correct one-bit output, space at most
`g x.length`, and the exact halted window-run summary at the next round.

The constant is chosen after the code and its universal constant:

```text
A = C * (c₁ * c₀ + c₁ + 1)
C * (c₁ * (c₀ * f n + 1) + 1)
  ≤ C * (c₁ * (c₀ * f n + f n) + f n)
  = A * f n ≤ g n.
```

Here the first inequality uses `1 ≤ f n`, and the final inequality uses the domination
threshold. The payload is `List.replicate N₀ true`, so the paired input's length is at least
`N₀`; the code itself is unchanged. The published halting-space theorem supplies the
configuration-bound time, and `windowRun_summary_of_halts` supplies the window conclusion.
No statement of `space_hierarchy` is used in this private proof.

The new symbols in this calculation are the existing proof parameters: `c₀` is the original
decider's coefficient, `c₁` the normal-form coefficient, `C` the fixed code's universal
simulation coefficient, `A` their domination coefficient, and `N₀` the resulting threshold. This `C` is the route's
`C_α`, fixed for the normalized decider's code `α` before its payload is padded.


## Public hierarchy contradiction

Choose the published self-universal machine and the diagonal language already proved in
`SPACE g`. Assuming the reverse inclusion puts that language in `SPACE f`. The normalization
lemma supplies a payload-padded input at which the universal machine computes the language's
indicator within the radius and configuration-count bound. The diagonal language then gives
that same indicator as the negation of whether its singleton output is `[true]`. The two
Boolean cases are contradictory. The forward inclusion is the required finite-prefix lemma.
The logarithmic-space corollary now inherits the resulting admission-free theorem.

## Required edge cases

| Case | Checked lemma or public reading |
|---|---|
| Empty binary input | `sph_fold_valid` proves the empty-list case; `sph_valid_machine` and `sph_diagonal_language` quantify over every `List Bool` with no nonempty premise; the floors give a positive radius |
| Rich input containing a foreign symbol | `sph_fold_valid` characterizes the valid image; `sph_validated_machine` sends the false branch directly to the stationary-head false emitter |
| Witness halts with input head at zero | `sph_right_run` uses `moveInputPos_pos_of_ne_right` and `moveInputPos_rightBoundary` to obtain positivity, then `sph_input_rewind_run` restores position one |
| Witness's final transition emits | `sph_radius_run` uses `embedSilentRetTM_run` at the first halt; `embedSilentCfg_cap` reads the complete captured output |
| Universal output is not `[true]` | `sph_summary` uses `outSummaryCode_eq_one_iff`; `sph_verdict_run` emits the complement of the test, hence true |
| Window exit is `left` | The `left` branch of `sph_runner_tail_run` dispatches directly to the true emitter |
| Clock exit is `exhausted` | The `exhausted` branch of `sph_runner_tail_run` dispatches directly to the true emitter without reading or testing the unspecified record |
| Run clock is beyond an earlier halt | `sph_code_window` uses `FinTM.ComputesInTime.spaceUsed_le_of_halt`; `sph_summary` uses `windowRun_stop_unique` to align endpoint round counts |
| Input length below the domination threshold | `sph_inclusion` absorbs the finite prefix; the diagonal contradiction's `sph_code_window` chooses a payload whose paired length is at least the threshold by `length_pairEncode` |
| The lower bound needs `1 ≤ f n` | `sph_code_window` derives it from `spaceConstructible_iff` and `logSpace_eq` before bounding the universal simulation coefficient |

## Environment and verification

Part 1 preflight passed before bootstrap: 57.747 GiB free on the work filesystem and 9.075 GiB
MemAvailable. No cgroup controller was exposed. The first attempt to read a cgroup limit failed;
the logged fallback used `/proc/meminfo`. `/tmp` is tmpfs; all compilation/cache temporary files
used the disk-backed task `TMPDIR` instead. A later resource check still found over 51 GiB free
and 8.6 GiB MemAvailable.

Lean 4.25.0 was installed from the official release archive into a fresh task directory. It
starts normally (commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`); no loader shim or borrowed
compiled artifact was used. Every present package matched both its manifest revision and URL;
absent optional packages were not named by the module order. The cache was fetched for exactly
the 63 derived Mathlib roots, never unfiltered.

The first narrowed cache fetch succeeded. A subsequent probe was rejected because its source
resolved through a symlink outside the repository root. Conservatively, the single cleaned
retry was taken: package/build configuration artifacts were removed, preflight and pin checks
repeated, and the same roots fetched again using the freshly obtained 1,057 archives. A physical
`FillProbes/CacheProbe.lean` then passed. No empty `.olean` was found. This was a path-validation
error, not evidence of corrupt cached proofs.

The fresh **220-module bootstrap passed**, with exactly the supplied 26 sorry warnings in ten
modules. Per-module wall time and peak RSS are recorded using `os.wait4` in
`evidence/logs/bootstrap/`; summed module time was 2,834.864 seconds, maximum RSS 2,994,428 KiB.
The cache probe and every other Lean invocation also have separate resource logs. Only one
agent-started Lean invocation ran at a time; the permitted low-priority text screen ran beside it.
No `lake build`, unfiltered cache fetch or module timeout was used.


The draft checks build each composition before landing it. `cp4-edit` and the final
`cp4-seal-final` and `cp4-controls-final` series check the owned module and facade after every landed proof edit.
The owned source, full-seal, controls, extended-host and axiom checks pass. A first seal attempt
caught a repeated ND embedding field occurrence that `rw` had left to definitional reduction;
explicit public simplification of both transport occurrences fixed it. All diagnostic failures
and repairs remain in the evidence.

The 71-definition seal includes every reached other-file TCSlib `def`, including the extra
ND acceptance/embedding operations, `posWidth`, `counterValue` and finite-state instances.
The four primitive simp attributes are removed. There are 75 effective controls: 67 delta
controls, cardinality usage controls for the two enumerated rewind-state instances, recursive equation usage controls for `windowRun` and `NDTM.runWith`, and four
primitive simp controls. All pass unsealed and fail sealed. The generic whole-instance delta goal was initially ineffective for two enumerated Fintype structures (eta contraction); their cardinality goals replace it and detect the seal. Both raw runs are retained. Reducible abbreviations are excluded by the pinned `policy.md:72–79` and
`campaign/standards/TEMPLATE.md:43–49`: they are notation and Lean's default reducibility
validation rejects sealing them. In particular, `Cfg.Halted` is read as its state equation in
the two first-halt consumers, exactly the policy's explicit example; it is never an argument to
`simp`, `rw` or `unfold`. Generated structure projections and recursors are also recorded as
abbreviations. No unsafe reducibility override is used. The exact policy excerpt is shipped.

The final citation inventory combines elaborated proof references with explicit source
identifier resolution: 900 outside constants, 272 from TCSlib, with no directly cited foreign
`_private` constant. The elaborated walk alone records 882 constants, 269 from TCSlib; explicit
source resolution contributes three further TCSlib readings that simplification removed from
proof terms. The final import probe has 321 checks, adding 150 to the supplied 171. Its source
is `FinalImportProbe.lean`; the complete citation list is `evidence/citations/final.md`.
The bundled ND field readings' source modules are correctly recorded as
`TuringMachine/Nondeterministic`. No additional definition needed sealing.

The source-identifier diagnostic initially used two incompatible metaprogramming calls;
`final-source-citations-v2` is the successful run on the corrected source, with the earlier
errors retained. The inspection table `evidence/inspection/final_v2.md` enumerates all 443
rewriting/reduction tactic sites, including complete multiline arguments and public target
bodies. The final extraction also includes `simp_all` and complete multiline `change` targets,
which were not fully displayed by the earlier 442-site checkpoint table. The accompanying
`final-rewrite-heads.json` checks explicit bracket heads against Lean-resolved declaration
kinds; no foreign definition or abbreviation is supplied as a reduction rule. Own lets/leaves
and public equations are the only explicit reduction arguments.

| Axiom walk | Result |
|---|---|
| All 43 private declarations, including the complete diagonal-language construction | Subsets of `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `space_hierarchy` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `LOGSPACE_ssubset_PSPACE` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `SPACE_linear_ne_NP` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |

The two source sorry warnings remain the untouched F6 and `SPACE_linear_ne_NP`.
The public hierarchy theorem uses the private construction, normalization and inclusion. Neither completed public target depends on any admission.

## Baseline admissions by name

The bootstrap has exactly 26 warnings in the following ten modules. The only removals are
`space_hierarchy` and `LOGSPACE_ssubset_PSPACE`; the remaining 24 admissions are unchanged.
The complete original list is also in `evidence/logs/base-sorries.txt`.

| Module under `TCSlib/Complexity` | Baseline declarations |
|---|---|
| `TuringMachine/Simulation` | `branchTM_spaceUsed` |
| `TuringMachine/Encoding` | `pairDiagTM_computes` |
| `TuringMachine/Composition` | `idTM_computes`, `ifEqTM_computes`, `condTM_computes_iff` |
| `ClassP/TimeConstructible` | `_root_.Turing.FinTM.lengthBitsTM_computes`, `_root_.Turing.FinTM.lengthBitsTM_spaceUsed` |
| `TuringMachine/Build/Wrappers` | `timedCondTM_computes`, `timedCondTM_spaceUsed` |
| `TuringMachine/Build/Loop` | `loopHostTM_contracts`, `loopHostTM_decides`, `loopHostTM_finds`, `loopHostTM_spaceUsed_le_budget`, `emitLoopTM_computes` |
| `TuringMachine/Build/Primitives` | `polyUnaryTM_spaceUsed`, `unaryTokenTM_computes`, `appendBitTM_computes` |
| `TuringMachine/Build/RecordTable` | `exists_tableFindTM`, `exists_tableAppendTM`, `exists_recordValidTM`, `exists_recordNextTM` |
| `SpaceComplexity/Savitch` | `savitch` |
| `SpaceComplexity/Hierarchy` | `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`, `SPACE_linear_ne_NP` |

## Duplication and lint

The before-screen is byte-identical to the supplied base: 1,854 declarations, 1,689 pairs and
534,736 reproduced characters, no pair on Hierarchy. The frozen-checkpoint-1 screen has exactly
the same pair lines. The frozen-checkpoint-2 screen completed with 1,871 declarations,
1,693 pairs and 536,116 reproduced characters: four added pairs, none at 90% or higher.
Its only added cross-file pair is the five-field `Cfg.ext`/public-map-state-reading idiom in
`sph_rewinds_run`, 82% against `Cfg.mapState_mapState`. The framed endpoint also changes input
and radius head, so it does not restate that public pure relabeling lemma. The other three
pairs are between this file's distinct leaves/bank selections. Full dispositions are in
`screen-cp2-classification.txt`. For completed screens, **new copies: none**.

The frozen-checkpoint-3 screen completed: 1,885 declarations, 1,697 pairs and 538,487
reproduced characters. Its eight added pairs are all below 90%; full dispositions are in
`screen-cp3-classification.txt`. The second cross-file pair is `sph_verdict_run` against the
same public configuration-field idiom (84%), not a reproof of mapState composition. 

The first frozen-final screen, at `bf4d026a7bea613fa9649bc8fe9ca05dbe6632d1`, found
12 new pairs, all below 90%, with 1,893 declarations, 1,701 pairs and 539,440 reproduced
characters. Inspection identified two pure `mapState` composition calculations inside
`sph_valid_machine`. They now directly cite the public `Cfg.mapState_mapState`, removing
13 lines. This is a re-derivation repaired by citation, not merely an idiom disposition.
Only the unpublished checkpoint-8 commit was amended; its refreshed archive supersedes its
first version. All raw first-screen evidence is retained as history. The final screen and
sweep below concern the amended commit.

The amended commit's final screen completes with 1,893 declarations,
1,701 pairs and 539,326 reproduced characters. There are 12 new pairs
and no removed baseline pairs. It ran under `nice -n 10` in 2,789.130 seconds
(peak RSS 486,544 KiB), with the unmodified pinned v3 script. Each new pair is
classified below; the complete raw outputs and `screen-final-classification.txt` are included.

| Target in `Hierarchy.lean` | Source | Match | Disposition |
|---|---|---:|---|
| `sph_verdict_run` | `InputRewind.lean::Cfg.mapState_mapState` | 339/402 (84%) | idiom: Public field readings establish a branch precondition using its live-state hypothesis and emitted endpoints with changed state/output; this is not the generic composition equation. |
| `sph_right_run` | `Hierarchy.lean::sph_emit_run` | 490/588 (83%) | same-file leaf idiom: The two explicitly permitted one-step leaves have different effects and share public action-field readings. |
| `sph_rewinds_run` | `InputRewind.lean::Cfg.mapState_mapState` | 330/402 (82%) | idiom: Public field readings for a framed endpoint that changes input position and the radius head; not pure state-map composition. |
| `sphWitnessSel` | `Hierarchy.lean::sphInitSel` | 70/88 (80%) | same-file arithmetic idiom: Distinct bank selections share elementary embedding-injectivity arithmetic. |
| `sph_record_suffix` | `InputRewind.lean::Cfg.mapState_mapState` | 293/402 (73%) | idiom: Restore the original live entry configuration using its state hypothesis and unchanged physical fields; the conclusion is not the generic composition equation. |
| `sph_valid_machine` | `Hierarchy.lean::sph_witness_cap` | 69/111 (62%) | same-file arithmetic idiom: This excludes the entire initializer/runner bank from the witness bank; sph_witness_cap is already cited for the distinct claim excluding radius tape one. |
| `sph_runner_run` | `Hierarchy.lean::sph_initial_record` | 1059/1728 (61%) | same-file R1 consumer idiom: Distinct published clocked-runner and initializer hosts, both embedded through R1; shared field transport already factors through sph_select_fields. |
| `sph_valid_machine` | `InputRewind.lean::Cfg.mapState_mapState` | 245/402 (61%) | idiom; earlier pure re-derivations repaired: The remaining match is the concrete initial-configuration comparison through capture, lift, blank-frame and initialization fields. Both pure composition calculations now cite Cfg.mapState_mapState directly. |
| `sph_runner_run` | `Hierarchy.lean::sph_test_run` | 836/1424 (59%) | same-file R1 consumer idiom: Distinct published clocked-runner and Boolean record-test hosts, with shared R1 field transport through sph_select_fields. |
| `sph_validated_machine` | `InputRewind.lean::Cfg.mapState_mapState` | 232/402 (58%) | idiom: Concrete initialization and branch-precondition identities through Cfg.init and mapState field readings. |
| `sph_seam_avoids` | `Hierarchy.lean::sph_seam_heads` | 137/241 (57%) | same-file public-trajectory idiom: The same public seam case split supports different conclusions: exit-state avoidance and a physical head envelope. |
| `sph_emit_run` | `Hierarchy.lean::sph_right_run` | 490/915 (54%) | same-file leaf idiom: Reverse direction of the same permitted-leaf comparison. |

**New copies: none.** No new pair rederives a foreign private declaration; no promotion is
required by the text screen. Optional general-consumer promotions are listed below.

Every new private lemma has name and statement-family searches against the exact base and all
four open PR heads observed during this task:

| PR | Read-only fetched head |
|---|---|
| 211 | `f239dafd09f060ec87ca0992103ae8eb48bce31e` |
| 210 | `fff0430c7c9db136e60ed14b069e972c2ea56fc8` |
| 208 | `d01c56a4ed9487fa2c84c7d62470cee2c6bef960` |
| 195 | `40553944417ba519d736985a300e61fbd13eaffc` |


The initial route searches and probes cover `sph_inclusion`, the square, logarithmic domination,
and strictness helper. The mandated route copies are renamed exactly as required. The separate
normalization/window exact? probe fails to find a published replacement. The corollary probe
finds the owned admitted public target, which is not a usable proved external lemma.

For checkpoint 2, nine exact? goals run against the base overlay imports and own definitions
only, deliberately excluding the new lemma proofs: right move, emitter, fold characterization,
validation run, witness-cap disjointness, radius capture, input rewind, paired rewinds and
initial record. All nine fail to find an exact proof. The companion per-lemma git-grep logs
record the named hosts that are cited in the implementation. The diagnostic probe's nonzero
exit is expected and is not an owned-source failure. The nine probes are in `CP2Semantic.lean`.

For checkpoint 3, ten further apply? probes run against the base overlay plus the checked
checkpoint-2 declarations and new machine definitions, excluding all ten checkpoint-3 lemma
proofs. The per-lemma name/statement searches cover all four observed open PR heads. Hosts
found by those searches are cited, rather than copied. The apply? results are recorded in
`CP3Semantic.lean` and its raw diagnostic log. No complete published replacement was found. Generic logical candidates and partial proofs are not replacements. The initial unrestricted exact? and apply? diagnostics were interrupted after failing to return promptly; the final apply? run used Lean's standard 200,000-heartbeat per-declaration search budget and completed in 55.129 seconds. Its expected nonzero exit, partial suggestions and any search-budget failures are retained. This diagnostic does not certify absence of equivalents; the base/open-PR statement searches were also reviewed. No wall-clock timeout was imposed on an owned module check, and no item was stopped.

The two checkpoint-3 goals that reached the search budget, `sph_verdict_run` and
`sph_seam_heads`, were additionally isolated and rerun with `exact?` and a
1,000,000-heartbeat per-declaration budget in `FinalSemanticRetry.lean`, again excluding their
proofs and all other checkpoint-3 lemma proofs. Both again reached the heartbeat budget (159.306 seconds total), so this diagnostic
still does not certify absence of a replacement. A final interface-only version applies the
same 71-definition seal immediately before the two goals; both searches also reached the 1,000,000-heartbeat budget (156.367 seconds total). The raw errors remain in `final-semantic-sealed`; no complete published replacement was certified by these diagnostics.

Checkpoint 4 has six further per-lemma searches and exact? probes, using the base overlay
and earlier checkpoint proofs while excluding all six new lemma proofs. All six fail to find an exact published replacement (15.833 seconds total); there are no heartbeat failures. The expected diagnostic exit is nonzero.
The two strengthened earlier lemmas still consume their already searched capture/rewind hosts.
The generic first-halt contract cites `exists_first_halt`; it does not reimplement first-halt
selection. The six searches also cover `Contract.ofSegment`, record/suffix compositions,
validation hosts and the indicator-reading alternative. Raw searches/probes are shipped.

Campaign lint: **0 FAIL, 81 WARN over 111 files**. The sole additional campaign warning is
file length above 1,000 lines. Justification: the brief explicitly imposes no size cap and
restricts ownership to this one file's private region; splitting into another source file would
violate that ownership. The standalone linter reports the same size threshold and the baseline
missing Main definitions heading. No new proof-sketch or long-line finding remains.

## Per-private semantic duplication ledger

Each search covers the exact base and the four observed open PR heads listed above, by name
and statement family. Paths in this table are under `evidence/logs/`; diagnostic probe sources
are under `evidence/probes/`. Expected failed-search errors are not source-check failures.
The twelve remaining private declarations are definitions of permitted leaves, bank selections
or compositions of named hosts; their roles are listed in the complete declaration table.

| Private lemma | Name/statement search | Search tactic and result | Disposition |
|---|---|---|---|
| `sph_inclusion` | `semantic-search-initial.log` | `baseline-dup`: exact? found no replacement | Required renamed route-probe copy; public supporting lemmas cited |
| `sph_code_window` | `semantic-sph_code_window.log` | `cp5-dup`: exact? found no replacement | Consumer of normalization, coding, universal and window hosts |
| `sph_sq_le_two_pow` | `semantic-search-initial.log` | `baseline-dup`: exact? found no replacement | Required renamed route-probe copy; public supporting lemmas cited |
| `sph_logSpace_dom` | `semantic-search-initial.log` | `baseline-dup`: exact? found no replacement | Required renamed route-probe copy; public supporting lemmas cited |
| `sph_logspace_ssubset` | `semantic-search-initial.log` | `cp7-dup`: finds the admitted public target, unusable as an external proved replacement | Required renamed route-probe copy, with explicit hierarchy hypothesis |
| `sph_right_run` | `semantic-sph_right_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_emit_run` | `semantic-sph_emit_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_fold_valid` | `semantic-sph_fold_valid.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_validation_run` | `semantic-sph_validation_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_witness_cap` | `semantic-sph_witness_cap.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_radius_run` | `semantic-sph_radius_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_input_rewind_run` | `semantic-sph_input_rewind_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_seam_heads` | `semantic-sph_seam_heads.log` | `cp3-semantic-bounded`: apply? search reached its 200,000-heartbeat budget | Public-host composition/reading; no complete replacement certified by this diagnostic; name/statement search reviewed |
| `sph_rewinds_run` | `semantic-sph_rewinds_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_select_fields` | `semantic-sph_select_fields.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_initial_record` | `semantic-sph_initial_record.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_runner_run` | `semantic-sph_runner_run.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_test_run` | `semantic-sph_test_run.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_verdict_run` | `semantic-sph_verdict_run.log` | `cp3-semantic-bounded`: apply? search reached its 200,000-heartbeat budget | Public-host composition/reading; no complete replacement certified by this diagnostic; name/statement search reviewed |
| `sph_summary` | `semantic-sph_summary.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_seam_avoids` | `semantic-sph_seam_avoids.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_written_record` | `semantic-sph_written_record.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_runner_tail_run` | `semantic-sph_runner_tail_run.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_suffix` | `semantic-sph_suffix.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_record_suffix` | `semantic-sph_record_suffix.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_record_size` | `semantic-sph_record_size.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_valid_machine` | `semantic-sph_valid_machine.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_halt_contract` | `semantic-sph_halt_contract.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_validated_machine` | `semantic-sph_validated_machine.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_diagonal_language` | `semantic-sph_diagonal_language.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_linear_ne_NP_of_padding` | `semantic-sph_linear_ne_NP_of_padding.log` | `cp8-semantic-final`: exact? found no replacement | Conditional consequence of the exact missing padding interface |

## Escalation E-PAD — exact padded-language space decider

The only unresolved target is `SPACE_linear_ne_NP`. No hierarchy obstruction remains.
The missing public interface, in namespace `Complexity` with `open Turing`, is:

```lean
∀ L : Language Bool, L ∈ SPACE (fun n => n ^ 2 + 1) →
  ({y | ∃ x ∈ L,
    y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} : Language Bool) ∈
      SPACE (fun n => n + 1)
```

This is a scoped API gap, not a claim that the statement is false or mathematically
unprovable. It must validate the exact paired syntax, all-true pad and its quadratic length
on **every** input, then run the original decider on the first component, with a linear
space bound measured in the padded input's length. Malformed or short-pad inputs must reject
without first allocating the potentially larger quadratic workspace.

The brief explicitly permits this named escalation at the last checkpoint. Name and
statement-family searches against the exact base and all four observed open PR heads found
no proved public replacement. The two exact? goals (the conditional corollary and this
missing interface) found none; raw diagnostic output is supplied. The search excludes the
admitted public target from the probe environment. The final diagnostic takes 14.326 seconds and has exactly two expected failed-search errors, with no heartbeat failures. Its initial version had a doc-comment/command parse error; that draft is retained and the corrected probe was rerun.

The published `FinTM.exists_inputCallTM` at `computesFunInTime_pairFst` supplies first-component
extraction/installation. Its time bound can be charged to space by the published general
space-from-time inequality. `vhostEmitTM_runFrom` and `vhostEmitTM_spaceUsed_le` supply a
buffered-input simulation with the original space plus buffer length and two. These are
pieces of a consumer assembly, not the exact all-input pad validator or its final decider
contract. The private padding implementation in `ClassNP/Nondeterminism` proves different
time/NP statements and cannot be cited or copied under the ownership and host rules.

Everything downstream of that interface is proved in `sph_linear_ne_NP_of_padding`:
the prescribed polynomial-time padding map, its exact preimage by `pairFstD_pairEncode`,
NP closure by `preimage_mem_NP`, and the contradiction with the linear/quadratic instance
of the hierarchy (domination threshold `A + 1`). The helper takes the hierarchy statement
and missing interface as explicit hypotheses; its axiom print has no `sorryAx`.

No unproved helper is introduced, and the last public body remains literally `sorry`.
Potential promotions of the checked general consumers are `sph_select_fields`, the seam
head/avoidance consumers, and `sph_written_record`; these are public-reading consequences,
not copies of foreign private implementations. Drafts are continuation material; the
committed source and patch series are the landed code.

Proposed implementation paragraphs for the maintainer (not inserted into the frozen target docstrings):

- `space_hierarchy`: **Implementation.** Absorb the finite exceptional prefix for inclusion.
  For strictness, compute the radius under `embedSilentRetTM`, rewind the radius and input,
  initialize the fixed self-universal machine's record, and use the configuration-count runner
  with `summaryTag`. The clock belongs to the runner. Test a halted endpoint and emit the
  opposite verdict, with foreign inputs rejected before the radius computation. Normalize a
  putative smaller-space decider through the published space-preserving normal form and coding
  clauses, fix its per-code universal constant, then pad only the payload.
- `LOGSPACE_ssubset_PSPACE`: **Implementation.** Apply the space hierarchy to `logSpace` and
  `n + 1`, using the integer-logarithm domination lemma, and transport strictness through the
  published linear-space inclusion into `PSPACE`.
- `SPACE_linear_ne_NP`: **Implementation.** Use the polynomial-time quadratic-padding map and
  `preimage_mem_NP`. A linear-space decider for the precisely padded language would turn an
  assumed equality of linear space and `NP` into the reverse of the linear/quadratic hierarchy.
  If that padded decider cannot be assembled from the named hosts, retain the admission and
  escalate its exact missing statement.

The supplied base sorry inventory is included verbatim in `evidence/logs/base-sorries.txt`.
Only the two completed target warnings disappear: the 220-module closure has 24 remaining
admissions versus 26 at baseline, all unchanged except those removals. The final tail has the two expected Hierarchy sorry warnings and two unchanged baseline
style warnings in `Randomized/Classes.lean` (unnecessary `<;>` at line 499 and unused simp
argument `hp` at line 1215). These also occur in the bootstrap and first final sweep; the
earlier summary recorded only admission warnings. The affected source is byte-identical
to the pinned base. Every other final-tail module has exactly its baseline warning list. Use the committed source and patches, not unchecked drafts.


Current checkpoint-8 validation is `final-v2-edit`: the corrected owned module and facade,
the elaborated walk, all 43-private/three-public axiom prints, and the complete 71-definition
seal all pass. `final-v2-import` passes all 321 checks (12.247 seconds; peak RSS 2,080,164 KiB).
The unchanged 71-definition seal has the same 75 effective controls as `cp8-final`, all passing
unsealed and failing sealed. The inspection has 443 sites, including the `simp_all` site. The final lint logs are
`final-v2-campaign-lint.txt` (0 FAIL, 81 WARN) and `final-v2-style-lint.txt` (only the baseline
heading finding and permitted file-length finding).

## Current evidence index

All paths below are inside this ZIP. The sources in `evidence/probes/final_v2/` match the
final source exactly, apart from the seal's inserted attributes and the axiom-print suffix;
`final-proof-snapshot-integrity.json` records that comparison and the unchanged control set.
The earlier `cp*`, `final-sweep/` and first-screen records are preserved diagnostic history.

| Verification | Current evidence |
|---|---|
| Preflight, official toolchain, manifest pins, narrowed cache, base identity | Original environment logs and runtime scripts under `evidence/logs/` and `evidence/runtime/` |
| Fresh 220-module bootstrap, each module's wall time and peak RSS | `evidence/logs/bootstrap/`, including `summary.jsonl` |
| Corrected source and facade | `evidence/logs/final-v2-edit/001-TCSlib_Complexity_SpaceComplexity_Hierarchy.log` and `002-TCSlib_Complexity_SpaceComplexity.log` |
| Full 71-definition seal | `evidence/probes/final_v2/Seal.lean`; `evidence/logs/final-v2-edit/005-FillProbes_final_v2_Seal.log` |
| All 75 effective controls, both flavors | `evidence/probes/cp8/HSealControl_unsealed.lean` and `HSealControl_sealed.lean`; corresponding `002` and `003` raw logs in `evidence/logs/cp8-final/` |
| All 43-private/three-target axiom prints | `evidence/logs/final-v2-edit/004-FillProbes_final_v2_Axioms.log`; `evidence/logs/final-axiom-accounting.json` |
| Complete citation inventory and extended import probe | `evidence/citations/final.md`, `evidence/citations/final.json`, `evidence/probes/FinalImportProbe.lean`, `evidence/logs/final-v2-import/` |
| Explicit rewrite/reduction inspection | `evidence/inspection/final_v2.md`, `evidence/logs/final-rewrite-heads.json` |
| Corrected commit's 52-module final sweep | `evidence/logs/final-sweep-v2/`, `evidence/logs/final-sweep-summary.md`, `evidence/logs/final-sweep-v2-accounting.json` |
| Full before/after text screens | `evidence/logs/screen-before.txt`, `evidence/logs/screen-after-final-v2.txt`, their resource logs, and `evidence/logs/screen-final-classification.txt` |
| Lint | `evidence/logs/final-v2-campaign-lint.txt`, `evidence/logs/final-v2-style-lint.txt` |
| Scope, patches and archive integrity | `evidence/logs/final_v2-source-audit.json`, `evidence/logs/delivery-integrity.json`, `evidence/logs/final-delivery-identity.json`, root `SHA256SUMS` and `bundle-verify.log` |

## Delivery integrity

All eight checkpoint archives pass every entry of their `SHA256SUMS` manifests and ZIP CRC
validation; each source matches its recorded commit. The eight format-patches were applied,
in order, to an isolated Git index at the pinned base. The reconstructed tree exactly equals
`e7b54ea9ddf1cda851f0d31838a4f4b43c8bf5d5`, the final commit's tree. This did not change any branch.
The bundle has only the pinned base as a prerequisite; its verification log is included.
The tracked working tree is clean and the only tracked change against base is Hierarchy.
The final manifest covers every ZIP entry except itself, including the embedded dispatch
manifest. The archive verification checks both that complete coverage and each digest.

| Checkpoint | Commit | ZIP SHA-256 |
|---|---|---|
| cp1 | `fd925fa2ee9de1509a74300ae7ea5202f7461605` | `daf114b1f1438a0d5aee549328a20273fb49623cebacea5f14cb07629370851b` |
| cp5 | `eec4e0a5e9dd3533340250f845369e04b1a07535` | `2dc340326d43bdc5bc8572dc941cbee9f610b109f2c33753eefcf1ab635e4383` |
| cp7 | `a55f653ddd191a33fb5adeda7f9d6dac3ed09567` | `b8d29e843ba76638847a4b06be0f6b89cf8b3948226b8190a003247d416dc9b4` |
| cp2 | `aae09bb9510e75b7760bdd1ac7ce190749c086be` | `69334d4e065d45dfffa377d463cacc871c2a39fbb4eb09db1fcb6d47430174c8` |
| cp3 | `80b00fe9c1c9be8155b48152615b904621cb0706` | `85ff547f1f129c920871b6dc4dcb8ce1570e64532136d48629dafa63cfc262aa` |
| cp4 | `f32dc1709aca0c6c24ca08c9492f5269b4a8ccf8` | `d71fd7bebe12f58a9cb82a2721ef6055c93fea939f0974f1b583c8ce0dbd1fd0` |
| cp6 | `37a041bc4053ca1e6d6b7272eeaeaddab7407839` | `2e16739d2a58c73d81eb2485d8b0ddda57533c5e1993db61f233433f44b06799` |
| cp8 | `30222bbd264a75057ae0779535a32e1a30dd2394` | `6dda89966bf6dc2306c14f3bb6a984d96dd2c27c3aa24a736e805edbfd918dfa` |

Final citation verification: `final-v2-import` checks the 321-name union; all checks pass
(12.247 seconds; peak RSS 2,080,164 KiB).
