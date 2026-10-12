# B7 continuation 2 — partial delivery

**Ground rule 9 partial: 1/5 requested targets is proved (target 8). Targets 9–12 retain their original `sorry` bodies.** Targets 1–7 are proved and frozen, so B7 is now at 8/12. There are **no admitted new private helpers** and **no completed target proved modulo an admission**. The complete-delivery gate of zero owned admissions is **not met**.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Starting campaign branch: `complexity/arora-barak-ch3-4`.
- Base: `4aafe9e41a5a8c9850bbfdfdc9a34a105ed26b9d`.
- Working branch: `fill/ch34-b7-cont2`; delivery commit: `2edcc7d1f7ea156a3d9138d8ba2610f99aac8a47`.
- Required ancestor check was the first repository gate: `git merge-base --is-ancestor 8e9a9b7eef75941a83ce036a195795c784758763 HEAD` succeeded before proof work. See `evidence/ancestry.log`.
- Read the preceding continuation report first, then its integration record, the earlier brief, the specified audit findings/resolutions/addendum, policy, workflow §4, and plan §4e.
- The diff changes only `InputAccess.lean` and `QueryReshape.lean`. Full snapshots of all four owned files are included. `Reductions.lean` and `Mult.lean` are byte-identical to the base.
- No push, PR, rebase, new repository file, new import, external mathematical source, or change to the checker. Every Lean check used `scripts/lean_check_tree.sh`; no `lake build`.

## Target and admission ledger

| Targets | Status | Axioms / remaining work |
| --- | --- | --- |
| 1–7 | Proved, frozen | Standard triple only; neither statements nor bodies changed. |
| 8 — `implicitlyLogspaceComputable_dropIdx` | **Proved** | `[propext, Classical.choice, Quot.sound]`. |
| 9 — `ImplicitlyLogspaceComputable.compQ` | Original admission remains | Seven proved preparation declarations added; its ARM is not yet constructed. |
| 10 — `ImplicitlyLogspaceComputable.comp` | Original admission remains | Must follow target 9 by the prescribed preimage corollary. |
| 11 — `LogspaceReducible.trans` | Original admission remains | Must follow target 10. |
| 12 — `multLang_mem_LOGSPACE` | Original admission remains | Complete multiplication ARM and proved carry invariant still required. |

New admitted private helpers: **none**. Proved-modulo set: **empty**. Mathematical or statement escalations: **none**. The reason for this partial is the continuation budget, not an obstruction in the frozen statements. No out-of-scope admission was modified or used by target 8.

## Completed construction

`dropARM mode : ARM 9 2 DropState` is one finite table for both query languages, over exactly `![inputBitLang, inputLenLang]`. The mode changes the final answer, while validation, decoding, and position arithmetic share their proofs. The all-input run preserves the exact bound `4 * h.length + 4` at every pre-halt configuration; `drop_mem` applies `arm_decides_poly` with coefficient 4 and exponent 1.

The program first counts the physical host length using the frozen `inputLength_loop`, then scans its outer pair shape with `alignedPair_loop` at stride 1. It saves the tail start and copies the host length into a width cap. The new shared tail fragment halves that cap once per tail bit and tracks the last bit, rejecting over-width or noncanonical tails **before any query-value accumulation**. The empty tail is accepted as zero. After success, the reverse decoder uses the frozen `query_accumulator_bound` to bound every suffix accumulator by twice the host length, hence by the machine bound.

The two nested shape scans instantiate the same frozen `alignedPair_loop` at strides 2 and 4. The discarded and retained payloads remain arbitrary words; no payload canonicality is assumed. Separator subtraction is factored into `drop_decrement_run`. The final shared segment walk seeks through the kept prefix at stride 4 and retained suffix at stride 2. The frozen `dropIdx_prefix_address` and `dropIdx_suffix_address` supply the output-bit identities. Length mode accepts a hit; a miss in both segments rejects. Malformed outer pairs, malformed nested pairs, bad canonical tails, excessive query width, and out-of-range queries all halt with false. No payload value is copied into a register.

The register roles at phase boundaries are:

| Register | Meaning |
| ---: | --- |
| 0 | Physical host pointer. |
| 1 | Physical host length. |
| 2 | End of the outer payload, in host coordinates. |
| 3 | Start of the retained suffix, in host coordinates. |
| 4 | End of the inner first field, in host coordinates. |
| 5 | End of the kept prefix, in host coordinates. |
| 6 | Decoded bounded query index. |
| 7 | Width cap / arithmetic scratch / lookup output index, reused by phase. |
| 8 | Saved outer-tail start. |

## New declarations and flagged changes

There are **58 new handwritten declarations: 6 public shared exports and 52 private declarations**. All are definitions or fully proved lemmas; none contains an admission. The following tables enumerate each source-level declaration and its role. `DropState` also generates its ordinary constructors, recursors, and the requested derived instances.

### `InputAccess.lean`

| Declaration | Visibility | Role |
| --- | --- | --- |
| `register_update_le` | **public export (flagged)** | Shared bound preservation after one register update. |
| `registerCopy_loop` | **public export (flagged)** | Shared bounded counting copy, preserving the source register. |
| `registerScale_loop` | **public export (flagged)** | Shared transfer into a destination at a fixed natural multiplier, including zero. |
| `access_width_half` | private | Binary width drops by one under halving a nonzero cap. |
| `canonicalTail_loop` | **public export (flagged)** | Shared strided tail scan: canonicality and width rejection before numerical decoding; empty tail represents zero. |
| `boundedDecode_loop` | **public export (flagged)** | Shared reverse binary decoder, with a supplied bound on every suffix accumulator. |
| `indexedSeek_loop` | **public export (flagged)** | Shared bounded pointer/index walk within a strided segment; returns either a hit or its end. |

### `QueryReshape.lean`

| Declaration | Visibility | Role |
| --- | --- | --- |
| `DropState` | private | Finite control states for the single mode-parametrized index-dropping ARM, including its derived finite and decidable instances. |
| `dropCopy` | private | Destination, source, and continuation for each of eight counting-copy stages. |
| `dropStride` | private | The three aligned-scan strides, 1, 2, and 4. |
| `dropLimit` | private | Physical end register for each aligned-scan layer. |
| `dropScanDone` | private | Successful continuation of each pair scan. |
| `dropAdvance` | private | Finite increment chains that instantiate the received aligned scan. |
| `dropTailAdvance` | private | One-cell advance of the bounded outer query tail. |
| `dropDecodeAdvance` | private | Two increments for the decoder doubling transfer. |
| `dropWalk` | private | Lookup pointer advance at stride four or two. |
| `dropARM` | private | One complete ARM 9 2 table for bit and length queries; its Boolean parameter selects the answer mode. |
| `dropBank` | private | The fixed two-language input-access oracle bank. |
| `dropLang` | private | Uniform mode-parametrized query language for dropIdx. |
| `drop_preS` | private | All syntactic ARM side conditions, including distinct registers and call-argument constraints. |
| `dropOracle` | private | Truthful indicators of the two access-bank languages. |
| `DropGood` | private | Abbreviation for PreS and the exact 4 * host.length + 4 register bound. |
| `DropReach` | private | Specialization of received AReach; no new reachability argument. |
| `DropHalt` | private | Specialization of received AHalt to the same table, oracle, and bound. |
| `dropValues` | private | Nine-register boundary vector with named physical offsets and scratch values. |
| `drop_bit` | private | Bit-oracle equation for a genuine paired query. |
| `drop_len` | private | Length-oracle equation for a genuine paired query. |
| `drop_ret` | private | Bounded one-step return. |
| `drop_hit` | private | Mode-dependent successful lookup: accept in length mode, read the host bit in bit mode. |
| `drop_copy_run` | private | Every copy stage invokes the single shared registerCopy_loop. |
| `drop_pair_run` | private | Every pair layer invokes the frozen alignedPair_loop with physical addresses. |
| `drop_canon` | private | The last-bit flag equals Canon, including the empty word. |
| `dropValues_apply` | private | Simp normalization of a boundary-vector lookup. |
| `dropValues_update` | private | Simp normalization of one boundary-vector update. |
| `dropValues_bound` | private | Nine scalar inequalities imply the uniform register bound. |
| `drop_tail_decode` | private | Outer-tail canonicality and width scan, rejection, scratch reset, and bounded reverse decoding. |
| `drop_seek_run` | private | Both output segments instantiate indexedSeek_loop. |
| `drop_lookup` | private | Complete output lookup, using the frozen prefix/suffix address lemmas and two shared segment walks. |
| `drop_first_read` | private | Even-position first-field lookup by the frozen pairEncode_getD law. |
| `drop_decrement_run` | private | One induction for the finite separator-subtraction chains used by both nested-pair preparations. |
| `drop_z_prepare` | private | Derive the first payload end from its separator, then restart the stride-two scan. |
| `drop_u_prepare` | private | Save the retained suffix start, derive the inner end, then restart the stride-four scan. |
| `drop_lookup_prepare` | private | Save the last pair boundary and restart the final segmented lookup. |
| `drop_inner_run` | private | Stride-four shape validation, malformed-inner rejection, and transition into output lookup. |
| `drop_nested_run` | private | Stride-two shape validation, malformed-payload rejection, and transition into the inner scan. |
| `drop_lang_pair` | private | The query-language indicator on a genuine canonical query. |
| `drop_bad_shape` | private | A malformed outer pair is in neither query language. |
| `drop_bad_tail` | private | A noncanonical outer tail is in neither query language. |
| `drop_rejected_tail` | private | Canonicality or width failure has false query answer, citing the frozen overflow lemma. |
| `drop_run` | private | Full all-input bounded halting proof: host length, outer shape, tail, nested shape, and lookup. |
| `drop_mem` | private | Single mode-parametrized arm_decides_poly assembly against the proved access bank. |
| `compLift` | private | The two f-query languages pulled back through dropIdx twice. |
| `compLift_mem` | private | Both lifted languages belong to LOGSPACE by N2 twice along proved N3. |
| `compBank` | private | Four languages: physical input bit/length and lifted f bit/length. |
| `compBank_mem` | private | All four oracle languages belong to LOGSPACE. |
| `compLift_query` | private | A genuine lifted call from the twice-paired host answers the f query; inner payload canonicality is separate. |
| `compQ_host_cap` | private | Full compQ output bound expressed using the physical host length. |
| `compQ_query_overflow` | private | An index wider than the full compQ cap has false bit and length answers before decoding. |

**Flagged exports and documentation:** each of the six public lemmas is in `Complexity.LogProg` within `InputAccess.lean`, in the marked continuation-2 shared block, and each has one new `## Main results` bullet. These are shared arithmetic, validation, decoding, and positioning fragments usable with other ARM tables; all six print within the standard axiom set. No further shared declaration is requested for serial integration. The private `access_width_half` supports the tail scanner.

**Flagged status update:** only target 8's `(phase P4.4b; spec, fill pending)` tag became `(phase P4.4b; proved)`. Its existing proof sketch was preserved. The combined module label for the two query reshaping maps was left unchanged because target 9 is still pending. No existing attribution, other documentation, target signature, or helper body changed. No sketch appendices were appended to existing declarations. New helpers have their own documentation and proof sketches where useful.

Imports added or changed: **none** (TCSlib and Mathlib). Declarations removed, renamed, or re-signed: **none**. The stronger byte-for-byte freeze reconstruction in `evidence/check-frozen.py` removes only the marked additions, six bullets, target-8 body, and its permitted status edit, and recovers each original owned file exactly. It also checks the whole frozen `PreimageHost.lean` and diff ownership. See `evidence/freeze.log`.

## Continuation frontier

**Resume at target 9.** Target 8 and all new fragments are proved. The seven private composition preparations in `QueryReshape.lean` are:

1. `compLift`, `compLift_mem`: twice-preimage f-query languages, using N2 twice along proved N3.
2. `compBank`, `compBank_mem`: the required four-oracle bank, all in LOGSPACE.
3. `compLift_query`: truthful lifted answers from the twice-paired host; its inner payload is arbitrary and must later be validated separately.
4. `compQ_host_cap`: `|compQ f w| ≤ (2*C+3) * (|pairEncode w tail|+1)^(e+1)` from the landed composition bound.
5. `compQ_query_overflow`: both queries reject when the canonical outer index is wider than that full composition cap. This uses `compQ_length_le`, not the shorter dropIdx bound.

No target-9 program or run proof has been started in the shipped source. Still required: one mode-parametrized ARM over `compBank`; physical-host and pair validation; bounded construction of the polynomial output cap; outer width/canonicality validation before storing p; bounded decoding of p; independent canonicality validation of the inner b; capped lifted-length search for F; all output-layout branches; full bounded all-input halting proof; and `arm_decides_poly` assembly.

For the search, query j only while j is below `C*(|x|+1)^e`. Return the first failed j or the cap itself when all earlier queries succeed. A zero cap must yield F = 0 without a query. Preserve the separator cells, the suffix's doubled physical address, and the length boundary `p < 2*F+2+|b|`.

**Canonicality caution for the next continuation:** `canonicalTail_loop` validates a bounded query tail by consuming a numerical cap through halving. It is appropriate for the outer query index. It must not be used to impose a polynomial numerical bound on the arbitrary-length canonical inner b: validate that inner field as empty or ending in true without decoding its potentially large represented value.

Then targets 10 and 11 follow the brief's short corollary routes, in order. Their source files are untouched. Target 12 still needs the complete multiplication ARM and a proved pure column/carry invariant over `bitsVal`, three canonical-field checks, excessive-result-length rejection, zero-padded result comparison, and the final carry check. No multiplication helper or substitute assumption was added.

## Environment and verification

Lean is v4.25.0; mathlib remains pinned at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The environment initially failed Lean executable discovery through `/proc/<self-pid>/exe`. As in the previous continuation, an environment-only `LD_PRELOAD` shim redirects that exact readlink to `/proc/self/exe`; its source is included as `evidence/lean-self-path.c`. It changes neither Lean's kernel nor repository source. With it, `lake exe cache get` succeeded and unpacked 7,506 cache files.

The initial bootstrap attempt stopped at module 2 when duplicate generated caches filled the disk (`evidence/bootstrap-environment-failure.log`). Replacing 2,083 byte-identical generated `.olean` copies with links to the same pinned cache freed 1,313,494,368 bytes. The fresh 104-module bootstrap then completed successfully against the base, with 0 errors and exactly the expected 24 original sorry warnings (`evidence/bootstrap.log`). All final checks use the freshly bootstrapped normal check tree. Local proof experiments used scratch files and the same unchanged check script; these experiments are not shipped as repository changes.

The original warning set, identified by declaration name, is included in `evidence/base-sorries-names.txt`:

```text
Base: 4aafe9e41a5a8c9850bbfdfdc9a34a105ed26b9d

TCSlib/Complexity/SpaceComplexity/Constructible.lean · spaceConstructible_logSpace
TCSlib/Complexity/SpaceComplexity/Constructible.lean · spaceConstructible_linear
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean · NSPACE_subset_exp_dtime
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean · NL_subset_P
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean · polyTimeReducible_of_mem_NL
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean · expandTM_run_ofCfg
TCSlib/Complexity/SpaceComplexity/Inclusions.lean · b2b_host_contract
TCSlib/Complexity/SpaceComplexity/Savitch.lean · spaceConstructible_poly
TCSlib/Complexity/SpaceComplexity/Savitch.lean · savitch
TCSlib/Complexity/SpaceComplexity/Savitch.lean · PSPACE_eq_NPSPACE
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean · space_universal
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean · space_hierarchy
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean · LOGSPACE_ssubset_PSPACE
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean · SPACE_linear_ne_NP
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean · implicitlyLogspaceComputable_dropIdx
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean · ImplicitlyLogspaceComputable.compQ
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean · ImplicitlyLogspaceComputable.comp
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean · LogspaceReducible.trans
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean · PATH_mem_NL
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean · PATH_NLComplete
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean · compl_PATH_mem_NL
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean · NL_eq_coNL
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean · NSPACE_compl_eq
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean · multLang_mem_LOGSPACE

TOTAL 24
```

| Verification | Result | Evidence |
| --- | --- | --- |
| Required ancestor | PASS before work | `evidence/ancestry.log` |
| Fresh bootstrap, prescribed 104-module order | 0 errors; exactly 24 base sorry warnings | `evidence/bootstrap.log` |
| Final eight-module suffix, including all owned and required downstream modules | 0 errors; 4 retained owned admissions and 5 unchanged downstream admissions | `final-sweep.log`, `evidence/final-sweep.sh` |
| InputAccess and frozen PreimageHost | 0 errors, 0 sorry warnings | `final-sweep.log` |
| QueryReshape | 0 errors; only target 9 remains admitted | `final-sweep.log` |
| Reductions / Mult | 0 errors; original targets 10, 11 / 12 remain admitted | `final-sweep.log` |
| Path / ImmermanSzelepcsenyi | Exactly the original 2 / 3 sorry warnings | `final-sweep.log` |
| SpaceComplexity facade | 0 errors, no own sorry warning; root TCSlib excluded | `final-sweep.log` |
| Unchanged maintainer pre-ship probe | 0 errors, no own sorry; target prints show 1–8 standard, 9–12 sorryAx | `evidence/preship-probe.log` |
| All twelve target prints, plus six exports | Targets 1–8 and all exports admission-free; exactly targets 9–12 have sorryAx | `axioms.log` |
| Frozen text, ownership, and unchanged imports | PASS | `evidence/freeze.log` |
| Campaign style lint | `style_lint: 0 FAIL, 2 WARN over 45 files` | `evidence/stylelint.log` |
| Diff whitespace | PASS | `evidence/diff-check.log` |
| Format-patch replay | Isolated base index produces exactly the delivery tree | `evidence/patch-replay.log` |
| Incremental bundle verification | PASS, with the recorded base prerequisite | `evidence/bundle-verify.log` |

The final-sweep PASS means successful elaboration under the explicitly recorded partial-warning set; it does **not** assert the complete-delivery admission gate. That complete gate remains unmet until targets 9–12 are filled.

The pre-ship probe was copied byte-for-byte from `audits/evidence/b7/B7StatementsProbe.lean.txt` into the ignored `.lake/b7-probes/` location and run through `scripts/lean_check_tree.sh`. Its old comments about the original statement-stage admissions remain unchanged; the current printed axioms are authoritative. The additional `FinalAxioms.lean.txt` prints all twelve targets in brief order and the six shared exports, through the same checker.

### Final sweep

```text
Checking TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
Checking TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
Checking TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:1204:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:95:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:105:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:104:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:133:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:71:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity
Final sweep: PASS (8 modules; partial-delivery warning set recorded in REPORT.md)
```

### Twelve target and six export axiom prints

```text
'Complexity.LogProg.OIS.run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.compile_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_of_logspaceReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.readIn_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_dropIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.compQ' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.comp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.trans' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.multLang_mem_LOGSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogProg.register_update_le' does not depend on any axioms
'Complexity.LogProg.registerCopy_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.registerScale_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.canonicalTail_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.boundedDecode_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.indexedSeek_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Owned file sizes

| File | Base lines | Delivery lines |
| --- | ---: | ---: |
| `InputAccess.lean` | 1569 | 2016 |
| `QueryReshape.lean` | 297 | 1208 |
| `Reductions.lean` | 153 | 153 |
| `Mult.lean` | 74 | 74 |

The two lint warnings concern only file size. Binding ground rule 8 explicitly removes the size cap, requires these counts, and prohibits new files/import changes. That is the recorded justification for keeping the shared and target-specific constructions in the owned files. It does not require a statement escalation.

## Duplication ledger

**new copies: none**

The prescribed before-screen is byte-identical to `audits/logs/b7-fill-2-screen-after.txt`: **273 declarations, 67 pairs, 17,169 characters**. The final after-screen is **317 declarations, 72 pairs, 19,550 characters**. All 67 baseline rows remain unchanged. There are **no new cross-file pairs**, and **no new pair at or above 90%**. The screen counts the declaration forms recognized by its parser; the separate source-level inventory above also includes definitions and abbreviations it does not screen.

An intermediate screen caught a 91% preparation pair. The shared finite subtraction proof was factored into `drop_decrement_run` and both preparations now invoke it. The final screen below is after this factoring. The aligned scan, host-length loop, paired lookup, copy loop, decoder, and positioning loop are each cited through their shared proof.

| New in-file row (all in QueryReshape) | Fraction | Justification |
| --- | ---: | --- |
| `drop_u_prepare` reproduces `drop_lookup_prepare` | 311/349 = 89% | Both normalize shared copy endpoints and clear the pointer; the inner preparation additionally saves the retained start and invokes the shared four-cell subtraction chain. |
| `drop_z_prepare` reproduces `drop_lookup_prepare` | 291/349 = 83% | Both normalize a shared copy and clear; the outer preparation additionally invokes shared two-cell subtraction to derive its scan end. |
| `drop_u_prepare` reproduces `drop_z_prepare` | 442/584 = 76% | Different physical layers instantiate the same copy and subtraction proofs with their own registers, bounds, and continuations. |
| `drop_inner_run` reproduces `drop_nested_run` | 895/1388 = 64% | Each dispatches a received pair-scan result; stride four enters output lookup, while stride two enters the inner validator, with different address transport and malformed-input semantics. Neither re-proves the scan. |
| `drop_z_prepare` reproduces `drop_u_prepare` | 442/871 = 51% | Reverse direction of the distinct layer-specific copy/subtraction endpoint instantiations above. |

Identified privately copied received proof material remains **0 lines (0%) in each owned file**, consistent with the prior deliveries' ledgers. New copied material is also 0 in each file. The textual overlaps above are the justified in-file endpoint/case normalizations, not separate copies of the shared arguments. The screen's reproduced-character totals are overlapping pair scores, not cumulative copied source size.

### Before (full output)

```text
declarations screened: 273; copy pairs (target reproduces >= half of source): 67; reproduced text: 17,169 chars
   ARMKit.lean::vword_unary₂  reproduces  ARMKit.lean::vword_unary₁: 176/176 = 100%
   ARMKit.lean::vword_unary₁  reproduces  ARMKit.lean::vword_unary₂: 176/176 = 100%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.trans: 200/202 = 99%
   ARMProof.lean::AReach.trans  reproduces  DblLang.lean::Rch.trans: 200/202 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   ImplicitPoly.lean::regCfg_cfg  reproduces  DblLang.lean::regCfg_K: 121/124 = 98%
   ARMProof.lean::AReach.halt  reproduces  ARMProof.lean::AReach.trans: 197/202 = 98%
   ARMProof.lean::AReach.halt  reproduces  DblLang.lean::Rch.trans: 185/202 = 92%
   ParsePlain.lean::validPlain_iff  reproduces  ARMKit.lean::takeWhile_pairEncode_replicate: 94/105 = 90%
   CounterProgSimRun.lean::Bd  reproduces  CounterProgSim.lean::cf: 190/220 = 86%
   DblLang.lean::regCfg_K  reproduces  ImplicitPoly.lean::regCfg_cfg: 121/143 = 85%
   ARMProof.lean::AReach.trans  reproduces  ARMProof.lean::AReach.halt: 197/236 = 83%
   InputAccess.lean::access_reject  reproduces  InputAccess.lean::access_jump: 93/113 = 82%
   DblLang.lean::sym_lt  reproduces  DblLang.lean::sym_eq: 83/101 = 82%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_eq: 82/101 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   ParsePlain.lean::rrun_one_x  reproduces  Frag.lean::rrun_one_eq: 67/84 = 80%
   Frag.lean::rrun_one_eq  reproduces  ParsePlain.lean::rrun_one_x: 67/85 = 79%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.halt: 185/236 = 78%
   InputAccess.lean::access_clear  reproduces  InputAccess.lean::access_inc: 212/271 = 78%
   FragDec.lean::rrun_one_reg  reproduces  Frag.lean::rrun_one_eq: 64/84 = 76%
   FragDec.lean::decDAct  reproduces  Lib.lean::incCAct: 61/82 = 74%
   DblLang.lean::sym_eq  reproduces  DblLang.lean::sym_lt: 83/112 = 74%
   CounterProgSim.lean::cf  reproduces  CounterProgSimRun.lean::Bd: 190/257 = 74%
   InputAccess.lean::access_answer  reproduces  InputAccess.lean::access_jump: 83/113 = 73%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_lt: 81/112 = 72%
   Frag.lean::half_run  reproduces  FragDec.lean::clr_run: 375/520 = 72%
   Frag.lean::eqB_run  reproduces  Parse.lean::regBack_x: 617/864 = 71%
   InputAccess.lean::access_inc  reproduces  InputAccess.lean::access_clear: 212/299 = 71%
   CounterProgSimRun.lean::ans_append  reproduces  CounterProgSimRun.lean::ans_of_le: 60/86 = 70%
   Lib.lean::incB_run  reproduces  Frag.lean::eqB_run: 654/938 = 70%
   FragDec.lean::decD_run  reproduces  Lib.lean::incC_run: 1179/1733 = 68%
   Frag.lean::halfL_run  reproduces  FragDec.lean::clrE_run: 928/1366 = 68%
   CounterProgSimRun.lean::ans_of_le  reproduces  CounterProgSimRun.lean::ans_append: 60/90 = 67%
   ImplicitPoly.lean::rounds  reproduces  DblLang.lean::Rch.trans: 134/202 = 66%
   CounterProgSim.lean::pr_reach  reproduces  CounterProgSim.lean::pr_halt: 836/1262 = 66%
   Parse.lean::regBack_x  reproduces  Frag.lean::eqB_run: 617/938 = 66%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_inc: 177/271 = 65%
   FragDec.lean::clrEAct  reproduces  FragDec.lean::toEndAct: 144/229 = 63%
   Lib.lean::incB_run  reproduces  Parse.lean::regBack_x: 536/864 = 62%
   InputAccess.lean::readFrame  reproduces  InputAccess.lean::readAt: 66/107 = 62%
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   QueryReshape.lean::dropIdx_prefix_address  reproduces  QueryReshape.lean::dropIdx_suffix_address: 256/420 = 61%
   InputAccess.lean::readIn_run  reproduces  InputAccess.lean::read_one: 81/135 = 60%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   QueryReshape.lean::dropIdx_suffix_address  reproduces  QueryReshape.lean::dropIdx_prefix_address: 256/443 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   InputAccess.lean::access_jump  reproduces  InputAccess.lean::access_reject: 93/167 = 56%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   InputAccess.lean::read_cleanup  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::read_cleanup: 523/993 = 53%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_clear: 157/299 = 53%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%
```

### After (full output)

```text
declarations screened: 317; copy pairs (target reproduces >= half of source): 72; reproduced text: 19,550 chars
   ARMKit.lean::vword_unary₂  reproduces  ARMKit.lean::vword_unary₁: 176/176 = 100%
   ARMKit.lean::vword_unary₁  reproduces  ARMKit.lean::vword_unary₂: 176/176 = 100%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.trans: 200/202 = 99%
   ARMProof.lean::AReach.trans  reproduces  DblLang.lean::Rch.trans: 200/202 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   ImplicitPoly.lean::regCfg_cfg  reproduces  DblLang.lean::regCfg_K: 121/124 = 98%
   ARMProof.lean::AReach.halt  reproduces  ARMProof.lean::AReach.trans: 197/202 = 98%
   ARMProof.lean::AReach.halt  reproduces  DblLang.lean::Rch.trans: 185/202 = 92%
   ParsePlain.lean::validPlain_iff  reproduces  ARMKit.lean::takeWhile_pairEncode_replicate: 94/105 = 90%
   QueryReshape.lean::drop_u_prepare  reproduces  QueryReshape.lean::drop_lookup_prepare: 311/349 = 89%
   CounterProgSimRun.lean::Bd  reproduces  CounterProgSim.lean::cf: 190/220 = 86%
   DblLang.lean::regCfg_K  reproduces  ImplicitPoly.lean::regCfg_cfg: 121/143 = 85%
   ARMProof.lean::AReach.trans  reproduces  ARMProof.lean::AReach.halt: 197/236 = 83%
   QueryReshape.lean::drop_z_prepare  reproduces  QueryReshape.lean::drop_lookup_prepare: 291/349 = 83%
   InputAccess.lean::access_reject  reproduces  InputAccess.lean::access_jump: 93/113 = 82%
   DblLang.lean::sym_lt  reproduces  DblLang.lean::sym_eq: 83/101 = 82%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_eq: 82/101 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   ParsePlain.lean::rrun_one_x  reproduces  Frag.lean::rrun_one_eq: 67/84 = 80%
   Frag.lean::rrun_one_eq  reproduces  ParsePlain.lean::rrun_one_x: 67/85 = 79%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.halt: 185/236 = 78%
   InputAccess.lean::access_clear  reproduces  InputAccess.lean::access_inc: 212/271 = 78%
   FragDec.lean::rrun_one_reg  reproduces  Frag.lean::rrun_one_eq: 64/84 = 76%
   QueryReshape.lean::drop_u_prepare  reproduces  QueryReshape.lean::drop_z_prepare: 442/584 = 76%
   FragDec.lean::decDAct  reproduces  Lib.lean::incCAct: 61/82 = 74%
   DblLang.lean::sym_eq  reproduces  DblLang.lean::sym_lt: 83/112 = 74%
   CounterProgSim.lean::cf  reproduces  CounterProgSimRun.lean::Bd: 190/257 = 74%
   InputAccess.lean::access_answer  reproduces  InputAccess.lean::access_jump: 83/113 = 73%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_lt: 81/112 = 72%
   Frag.lean::half_run  reproduces  FragDec.lean::clr_run: 375/520 = 72%
   Frag.lean::eqB_run  reproduces  Parse.lean::regBack_x: 617/864 = 71%
   InputAccess.lean::access_inc  reproduces  InputAccess.lean::access_clear: 212/299 = 71%
   CounterProgSimRun.lean::ans_append  reproduces  CounterProgSimRun.lean::ans_of_le: 60/86 = 70%
   Lib.lean::incB_run  reproduces  Frag.lean::eqB_run: 654/938 = 70%
   FragDec.lean::decD_run  reproduces  Lib.lean::incC_run: 1179/1733 = 68%
   Frag.lean::halfL_run  reproduces  FragDec.lean::clrE_run: 928/1366 = 68%
   CounterProgSimRun.lean::ans_of_le  reproduces  CounterProgSimRun.lean::ans_append: 60/90 = 67%
   ImplicitPoly.lean::rounds  reproduces  DblLang.lean::Rch.trans: 134/202 = 66%
   CounterProgSim.lean::pr_reach  reproduces  CounterProgSim.lean::pr_halt: 836/1262 = 66%
   Parse.lean::regBack_x  reproduces  Frag.lean::eqB_run: 617/938 = 66%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_inc: 177/271 = 65%
   QueryReshape.lean::drop_inner_run  reproduces  QueryReshape.lean::drop_nested_run: 895/1388 = 64%
   FragDec.lean::clrEAct  reproduces  FragDec.lean::toEndAct: 144/229 = 63%
   Lib.lean::incB_run  reproduces  Parse.lean::regBack_x: 536/864 = 62%
   InputAccess.lean::readFrame  reproduces  InputAccess.lean::readAt: 66/107 = 62%
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   QueryReshape.lean::dropIdx_prefix_address  reproduces  QueryReshape.lean::dropIdx_suffix_address: 256/420 = 61%
   InputAccess.lean::readIn_run  reproduces  InputAccess.lean::read_one: 81/135 = 60%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   QueryReshape.lean::dropIdx_suffix_address  reproduces  QueryReshape.lean::dropIdx_prefix_address: 256/443 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   InputAccess.lean::access_jump  reproduces  InputAccess.lean::access_reject: 93/167 = 56%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   InputAccess.lean::read_cleanup  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::read_cleanup: 523/993 = 53%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_clear: 157/299 = 53%
   QueryReshape.lean::drop_z_prepare  reproduces  QueryReshape.lean::drop_u_prepare: 442/871 = 51%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%
```

## Delivery contents and replay

`fill-ch34-b7-cont2.zip` contains this report; all four complete owned source snapshots at their repository paths; one format-patch in `patches/`; `fill-ch34-b7-cont2.bundle`; the final sweep and axiom logs at the root; supporting verification evidence and exact probe sources; and `SHA256SUMS` for every other file in the archive.

The patch series is based on `4aafe9e41a5a8c9850bbfdfdc9a34a105ed26b9d` and replays to the delivery commit's exact tree. The incremental bundle advertises `refs/heads/fill/ch34-b7-cont2` and requires the recorded base. Only the two permitted source changes are committed; the report, probes, logs, and packaging files are outside the repository. The source working tree is clean. The archive is intended for maintainer verification and integration via the existing workflow; no integration action was performed.
