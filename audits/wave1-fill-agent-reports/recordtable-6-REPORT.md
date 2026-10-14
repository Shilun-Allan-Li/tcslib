# Record tables, continuation 5 — row 18

## Result and base

**1/1 target proved:** `Turing.exists_recordInitTM`. Its statement is unchanged. There is no `sorryAx` in row 18, row 17, or any new private declaration. The four paused rows remain admitted and unchanged.

- Pinned prerequisite / HEAD at branch creation: `8dfbc88195ece4448d2262b34f156268e4572e3c`.
- Checked out `complexity/arora-barak-ch3-4` first. Its observed tip was `4c9762c6a35a1427d1837425d7b219e5834eaf2f`; `git merge-base --is-ancestor 8dfbc88195ece4448d2262b34f156268e4572e3c HEAD` succeeded there.
- Created `fill/w1-recordtable-cont5` at exactly the pinned prerequisite. No later campaign commit was merged, rebased, or cherry-picked. No push or PR was made.
- Attached brief SHA-256: `028464a3a488cb25f5bea68916ba8caff9ebc96051e448a95b9eb708336b4264`. The repository brief is identical after its `@ANCESTOR@` placeholders are instantiated with the prescribed hash.
- Delivery commit: **6aef1d2a4af4147d05e1c0f3417406aca10d5a21**. The patch and bundle start at the pinned prerequisite; the bundle has that one prerequisite only.

## Implementation and scope

The implementation follows all fourteen prescribed phases. Row 17 is transported to scratch tape 2 with radius tape 1; tape 0 receives the record. The position variant is **copy, constant-zero map, leading-one write**, retaining three separate catalog phases. The tail is the suggested finite recursion on `k`, implemented only by catalog rows and public R2 seams. Its definitions and contract statement are unchanged in substance; the suggested `rt_tail_run` statement, including its time and head bounds, is taken verbatim and proved.

The phase chain is grouped into a three-phase position component, the finite tail, a three-phase cleanup component, and a contract for the thirteen phases after the scratch template. Each component is connected at its certified first exit with the inherited `rt_copy_seam`. The proof reuses the existing seam certificate, R1 identification, R1 envelope and field-layout facts. It adds no second word-move or field-layout lemma beyond the prescribed initial-record identity, and no runtime loop, counter, clock, hand controller or Bool phase. The prescribed R1 helper uses `Cfg.select`, `embedEmitCfg_select`, `embedEmitCfg_eq`, and the inherited `rt_embed_radius`.

| Prescribed phases | Implementation |
|---|---|
| 1 | `rt_exists_scratchTemplateTM`, at the prescribed R1 bank. |
| 2–3 | `writeConstTM` for the state, then `skipTM` in `rt_initRestTM`. |
| 4–6 | `rt_positionTM`: `copyTM`, `scanTM` with `scanMap`, `writeConstTM`. |
| 7–8 | Destination and scratch `skipTM` calls in `rt_initRestTM`. |
| 9 | `rt_tailTM`: the finite window-copy chain and tag writer. |
| 10–11 | Two destination `skipBackTM` calls in `rt_initRestTM`. |
| 12–14 | `rt_cleanTemplateTM`: `clearTM`, `skipBackTM`, `clearTM`. |

For a scratch template `[u,v]`, the suffix restores every head and clears the entire scratch tape. If `L` is the final layout length, its time is at most `16L + 8|v| + 16` and its head displacement is at most `2L + 2|v| + 8`. The row-18 wrapper absorbs these bounds and row 17's bounds at `2C + 64`, including the uncopied scratch window when `k = 0`. The exact endpoint preserves input position, prior output, the radius tape, and all destination cells outside the record slot.

Only `TCSlib/Complexity/TuringMachine/Build/RecordTable.lean` changes in the git delivery:

1. The prescribed home, opened by `/-! ### Initial-record fill, continuation 5 -/`, contains all 18 new private declarations.
2. Row 18's body is replaced with its proof.
3. A flagged `Fill appendix (continuation 5, proved)` is appended to its docstring; both earlier appendices are retained.
4. The module's flagged Status paragraph and row-18 Main results tag report the new proof.

The reused inherited privates are `rt_copy_seam`, `rt_embed_radius`, `rt_centeredWord`, `rt_template_fields`, `rt_bufferMask` and `rt_fields_slice`. Imports are unchanged. Reversing only these authorized edits reproduces the pinned source byte-for-byte. In particular, all 15 previously proved targets, all four paused rows and their docstrings, every frozen statement, and all 82 inherited privates are byte-identical. `evidence/verify_scope.py` and `evidence/logs/scope-check.log` record this check. The three prescribed statements and proofs are verbatim; only their “(Prescribed, proved.)” docstring tags were removed as instructed.

Final size: **6,131 lines; 28 public / 100 private declarations**, from 4,779 lines; 28 public / 82 private. The brief explicitly permits this size and assigns every new private to this home. No split or shared-file edit was attempted.

## Every new declaration

All names below are private and live in namespace `Turing` at the prescribed home.

| Declaration | Role |
|---|---|
| `rt_exists_scratchTemplateTM` | Prescribed row-17 transport to an R1-selected host bank; exact frame, cut, time and envelope. |
| `rt_binDigits_one` | Prescribed digits of one at positive width. |
| `rt_initRecord_fields` | Prescribed initial-record identity in the route's field words. |
| `rt_tailState` | Suggested finite control for `k` window copies and the last field. |
| `rt_tailState_fintype` | Finiteness of that recursively assembled control. |
| `rt_tailState_decidableEq` | Decidable equality for that control. |
| `rt_tailEntry` | Entry anchor for the finite tail. |
| `rt_tailExit` | Exit anchor for the finite tail. |
| `rt_tailTM` | Suggested catalog/seam chain copying `k` fields and writing the tag. |
| `rt_tail_run` | Proof of the unchanged suggested first-return, frame, time and envelope contract. |
| `rt_positionTM` | Copy/map/write position component. |
| `rt_position_run` | Its exact run, first exit and head bounds; preserves the framed source. |
| `rt_cleanTemplateTM` | Clear second field, skip back, clear first field. |
| `rt_cleanTemplate_run` | Its exact run, first exit, head bounds and global scratch erasure. |
| `rt_initRestState` | Control type for phases 2–14. |
| `rt_initRestExit` | Final cleanup exit in that control. |
| `rt_initRestTM` | The thirteen-phase suffix assembled from the components and catalog rows. |
| `rt_initRest_run` | Its first-return contract, complete record endpoint, restoration, time and envelope. |

No new helper is admitted. Requested missing shared infrastructure: **none**. Escalations or repository conflicts: **none**. Promotion candidates for maintainer consideration are the scratch-template transport, the generic finite-tail writer and contract, the copy/map/write position component, the two-field cleanup component, and the generic positive-width `binDigits_one` fact. The remaining initializer packaging is specific to this row. No promotion or shared-file modification is included.

## Verification

All checks use Lean 4.25.0 and `scripts/lean_check_tree.sh`; no `lake build` was used. Mathlib remains pinned to the repository's `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` revision. `lake exe cache get` populated the required Mathlib closure. Bootstrap and final checks used separate output trees, and the checker removed each target's stale `.olean` before recompiling.

The bootstrap completed all **271 modules** with zero errors and exactly the **69** prescribed sorry warnings, by declaration name. The final sweep completed the same **271 modules**, in the prescribed order, with zero errors and exactly **68** sorry warnings. The only removed admission is `Turing.exists_recordInitTM`; none was added. `evidence/logs/sweep-comparison.log` records both set comparisons.

Final sweep tail:

```text
CHECK TCSlib/Complexity/TuringMachine/SelfUniversal
TCSlib/Complexity/TuringMachine/SelfUniversal.lean:89:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/SelfUniversal.lean:144:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/NDCodeSimulator
TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean:91:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean:128:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
```

The owned-file check has zero errors and exactly these four sorry warnings:

- `exists_tableFindTM`
- `exists_tableAppendTM`
- `exists_recordValidTM`
- `exists_recordNextTM`

There are no other warnings in the modified file. The full order and the declaration-by-declaration sorry-name comparisons are included. The final sweep was performed in two consecutive ranges of the same prescribed order: the first 156 unchanged modules, then the owned module and all 114 following modules against the final source.

- `RT5ImportProbe.lean.txt`: the original 86 checks plus 97 additional explicit references; **183 checks, zero errors or warnings**.
- `RT5ConsumerProbe.lean.txt`: unchanged prescribed probe; **zero errors or warnings**.
- `RT5Sanity.lean.txt`: **zero errors or warnings**.
- `RT5Axioms.lean.txt`: both targets and every new private, **20 axiom prints**, with only subsets of `[propext, Classical.choice, Quot.sound]`.
- Style lint: `style_lint: 0 FAIL, 11 WARN over 32 files` (same warning count as the base).
- `git diff --check`: clean.

The two target prints are:

```text
'Turing.exists_recordTemplateTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_recordInitTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The full private-declaration prints are in `evidence/logs/axioms.log`. No `sorryAx`, `Lean.ofReduceBool`, or other extra axiom occurs.

Runtime note: the host's restricted `/proc/.../exe` lookup initially prevented Lean/Lake from finding their executable. A local `readlink` fallback shim, confined to that failed self-executable lookup, supplied the toolchain executable path; it did not change Lean, the source, the kernel, or any proof. The shim source and wrapper settings are included under `evidence/runtime/`. The initial cache setup was corrected before the successful bootstrap. Mathlib cache storage was isolated for this task. All 271 repository modules were rebuilt in this checkout for each successful sweep; no other campaign's TCSlib proof objects were used.

## Sanity cases, including complete runs

The evidence gives three bounded runs of the complete existential constructor, including its scratch-template phase, on:

| Input | Radius | Radius digits | Simulated work tapes |
|---|---:|---|---:|
| `[]` | 0 | `[]` | 0 |
| `[]` | 0 | `[]` | 1 |
| `[true, false, true]` | 2 | `[false, true]` | 1 |

These examples instantiate the actual witness supplied by the proved public theorem and retain the first-exit, time, all-head bounds and exact complete-configuration endpoint. They are bounded-run proofs, as permitted by the brief; they do not claim to numerically evaluate an existentially chosen row-17 witness.

In addition, kernel `decide` executes the actual catalog suffix for the same three input/radius/tape-count cases in **58, 71 and 115 steps**, respectively. These checks use distinct head origins, a preserved radius tape, pre-existing output and foreign destination cells. They check the exit and every earlier state, every head at every time through the exit, restored input/head/output positions, and all tape cells in the tested interval `[-12,205]`. The full bounded-run endpoint equality covers all integer cells. No machine is reimplemented in the evidence, and no `native_decide` is used.

## Duplication

Both screens use the unchanged `flat-screen.sh` over the prescribed 43-file population with byte-identical, path-encoded copies. The before output is byte-identical to the provided base after its one descriptive header line. The after input is byte-identical to the final source.

```text
Before: declarations screened: 2098; copy pairs (target reproduces >= half of source): 2428; reproduced text: 790,157 chars
After: declarations screened: 2115; copy pairs (target reproduces >= half of source): 2433; reproduced text: 792,188 chars
```

**new copies: none**. There are five new in-file pairs, no removed pairs, and no new cross-file pair involving the owned file. All five are below 90%; the ten pre-existing in-file pairs are unchanged. Every new pair is listed below in the screen's direction (“target reproduces source”):

| Target → source | Measurement | Justification |
|---|---:|---|
| `rt_initRestTM` → `rt_tailTM` | 113/191 = 59% | Shared public seam/copy/skip composition syntax; the suffix calls the tail and adds the distinct position, return and cleanup phases. |
| `rt_position_run` → `rt_moveWord_run` | 954/1606 = 59% | Common framed catalog-contract and R2 composition bookkeeping; this component preserves its source and maps/overwrites the destination, while the existing move contract clears its source. Both use `rt_copy_seam`; no second move or seam certificate is introduced. |
| `rt_tailState_decidableEq` → `rt_tailState_fintype` | 64/98 = 65% | Pre-disclosed structural recursion on the same finite sum control, for different typeclasses; the suggested instances are unchanged. |
| `rt_tailState_fintype` → `rt_tailState_decidableEq` | 64/106 = 60% | Reverse of that pre-disclosed instance pair, with the same structural-recursion justification. |
| `rt_tail_run` → `rt_moveWord_run` | 836/1606 = 52% | Shared framed copy/return and seam bookkeeping; the tail's induction preserves the source, writes repeated fields plus a tag and restores the destination. It does not re-prove the existing source-clearing move. |

No pair links `rt_tail_run` with the frozen recursive copier, and no new pair involves the public R1 reconstruction family, the Contract seam layer, or downstream private helpers.

The complete outputs are included as `evidence/logs/screen-before.txt` and `evidence/logs/screen-after.txt`; the comparison and threshold check are in `evidence/logs/screen-comparison.log`.

## External declarations cited (rule 10)

Only APIs public at the pinned prerequisite and this file's own frozen/new privates are used. There is no citation to a downstream module, another file's private declaration, or a post-pin landing. No body in Seam, Embed, CounterLoop or CfgRecord is unfolded beyond what the three explicitly prescribed proofs contain. The supplemental probe covers the following explicit external APIs, types, projections, and logical/arithmetic/list facts; ordinary notation and tactic implementations are not additional mathematical citations.

```text
Bool
Bool.toNat
Classical.typeDecidableEq
DecidableEq
EmbeddingLike.apply_eq_iff_eq
Fin
Fin.ext
Fin.val
Finset.Icc
Finset.mem_Icc
Fintype
Function.Embedding.coeFn_mk
Function.update
Function.update_of_ne
Function.update_self
List
List.append_nil
List.exists_cons_of_ne_nil
List.ext_getElem
List.flatten_cons
List.flatten_nil
List.getElem?_cons_succ
List.getElem?_eq_none
List.getElem?_replicate
List.getElem_cons_zero
List.intercalate
List.intersperse
List.length
List.length_append
List.length_cons
List.length_map
List.length_nil
List.map
List.map_append
List.map_cons
List.map_const'
List.map_map
List.map_nil
List.map_replicate
List.nil_append
List.range
List.range_succ_eq_map
List.replicate
List.replicate_succ
List.replicate_zero
List.sum
List.sum_append
List.sum_cons
List.sum_nil
List.take_succ_cons
List.take_zero
Nat.add_sub_cancel
Nat.bits
Nat.cast_add
Nat.cast_one
Nat.cast_zero
Nat.mul_add
Nat.ofDigits
Nat.size_eq_bits_len
Nat.size_pos
Nat.succ_pos
Nat.testBit
Nat.testBit_succ
Nat.zero_add
Sum.inl
Sum.inr
Turing.Cfg
Turing.Cfg.ext
Turing.Cfg.init
Turing.Cfg.inputPos
Turing.Cfg.mapState
Turing.Cfg.output
Turing.Cfg.select
Turing.Cfg.state
Turing.Cfg.workTapePos
Turing.Cfg.workTapes
Turing.FinTM.bufferTape
Turing.MultiTapeTM
Turing.MultiTapeTM.runFrom
Turing.RecSym
Turing.RecSym.cell
Turing.RecSym.digit
Turing.RecSym.digitEmb
Turing.RecSym.st
Turing.RecSym.tag
Turing.ScanPhase
Turing.ScanPhase.fwd
Turing.SeekPhase
Turing.SeekPhase.run
Turing.SweepPhase
Turing.SweepPhase.sweep
Turing.WritePhase
Turing.WritePhase.wr
Turing.binDigits
Turing.cfgRecord
Turing.clearTM
Turing.clearTM_run_ofCfg
Turing.copyTM
Turing.copyTM_run_ofCfg
Turing.embedEmitCfg
Turing.embedEmitCfg_eq
Turing.embedEmitCfg_select
Turing.embedEmitTM
Turing.embedEmitTM_runFrom
Turing.fieldOffset
Turing.fieldsTape
Turing.fieldsTape_cons_shift
Turing.fieldsTape_field
Turing.joinFields
Turing.joinFields_cons_cons
Turing.posWidth
Turing.scanKeep
Turing.scanMap
Turing.scanResult_map
Turing.scanTM
Turing.scanTM_run_ofCfg
Turing.seamCompTM
Turing.skipBackTM
Turing.skipBackTM_run_ofCfg
Turing.skipTM
Turing.skipTM_run_ofCfg
Turing.writeConstTM
Turing.writeConstTM_run_ofCfg
Unit
abs_le
abs_of_nonneg
abs_sub_le
abs_zero
add_assoc
add_le_add
add_zero
congrArg
false_and
funext
if_false
if_neg
if_pos
if_true
inferInstanceAs
sub_self
true_and
zero_add
```

## Archive contents and reproduction

The archive contains this report, the full modified source at its repository-relative path, the one-commit format-patch series, a bundle with the pinned prerequisite only, all required evidence and logs, the exact order/population lists, and `SHA256SUMS`.

At a checkout with the pinned prerequisite available, the bundle and patch are alternative ways to obtain the same change. Verify the bundle with `git bundle verify`; apply the patch series to the pinned prerequisite, or check out the bundle's delivered branch. Run the prescribed 271-module order through `scripts/lean_check_tree.sh`. Copy the evidence `.lean.txt` files to temporary `.lean` files in the checkout and check them with the same script. `verify_scope.py`, `verify_sweeps.py` and `verify_screens.py` document the source, warning-set and screen comparisons; their logs are included. The screen verifier accepts the repository root and, optionally, the after-screen flattened directory as arguments.

The git delivery changes only the owned source file. The report, evidence, patch and bundle are delivery files, not additional repository edits.
