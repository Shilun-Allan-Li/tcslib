# B7 continuation partial delivery: target 7

**Partial delivery under `briefs/ch34-b7-cont.md`, ground rule 9. This continuation proves 1/6 targets (target 7); targets 8–12 retain their original `sorry` bodies.** Targets 1–6 remain proved and frozen. There are **no new admitted private helpers**, and no completed target is proved modulo an admission. The complete-delivery gate of zero owned admissions is not met.

No mathematical obstruction or landed-table defect was found. Work stopped at the continuation budget while preparing target 8. This is an incomplete construction, not an escalation about an unprovable statement. Targets 10 and 11 were not filled ahead of the binding target order.

## Repository, ancestry, and delivery

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch checked out: `complexity/arora-barak-ch3-4`, not `main`.
- Recorded base: `37ab609199b2fad253b136375243db20faf88b16`.
- Required ancestor: `fdce1a557627b83872ce22b606e4eea17773914f`.
- The required `git merge-base --is-ancestor` check passed before proof work. Its equivalent check against the recorded base is in `evidence/ancestry.log`.
- Working branch: `fill/ch34-b7-cont`; no rebase.
- Delivery commit: `689f6770b7de945927156eeaa2d8415f22f05a99`.
- The first delivery report and the brief's binding policy, workflow, plan, route resolutions, addendum, and statement-gate documents were read before the continuation work.
- No PR was opened and nothing was pushed. The patch series and incremental bundle contain the same one local commit against the recorded base.

## Target status

| Target | Declaration | Status |
| --- | --- | --- |
| 1 | `LogProg.OIS.run` | Received proof frozen; standard axioms only. |
| 2 | `LogProg.OIS.compile_decides` | Received proof frozen; standard axioms only. |
| 3 | `mem_LOGSPACE_preimage` | Received proof frozen; standard axioms only. |
| 4 | `mem_LOGSPACE_of_logspaceReducible` | Received proof frozen; standard axioms only. |
| 5 | `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` | Received proof frozen; standard axioms only. |
| 6 | `LogProg.readIn_run` | Received proof frozen; standard axioms only. |
| 7 | `implicitlyLogspaceComputable_id` | Proved in this delivery; standard axioms only. |
| 8 | `implicitlyLogspaceComputable_dropIdx` | Original admission remains; six private support lemmas and shared ARM fragments proved. |
| 9 | `ImplicitlyLogspaceComputable.compQ` | Original admission remains. |
| 10 | `ImplicitlyLogspaceComputable.comp` | Original admission remains. |
| 11 | `LogspaceReducible.trans` | Original admission remains. |
| 12 | `multLang_mem_LOGSPACE` | Original admission remains. |

Here “standard axioms” means a subset of `[propext, Classical.choice, Quot.sound]`.

## Completed construction

Target 7 uses **one call-free program with a mode bit** for both query languages. Its four registers hold the physical scan pointer, the received reader's temporary counter, the candidate index, and the doubled data pointer. The query's index tail is compared against the candidate register while streaming; it is never copied into workspace. A finite-control last-bit flag rejects non-canonical tails, including `[false]`, and accepts the empty representation of zero.

The program validates the aligned pair and canonical tail on each candidate round, restoring the candidate head and clearing the scan pointer afterwards. Repeating validation avoids retaining an extra parsed offset. The data phase reads the candidate's two physical cells, answers on a match, rejects at the separator, or advances to the next candidate. The correctness proof covers malformed hosts, non-canonical queries, empty payloads, zero indices, and indices beyond the data length.

Every physical read cites the frozen `readIn_run`. Register updates and cleanup cite the received increment, clear, and rewind fragments. The bounded path is an abbreviation of the existing `Relation.ReflTransGen`; its existing composition is used rather than re-proved. `access_mem` applies `compile_space` against `Dbl.nilTM`. All four work heads stay in `[-1, W]` for `W = |bits (|y| + 1)|`, giving `4*(W+2)` cells, including origins and boundary cells. `log_poly_bound` closes the logarithmic bound.

The target 8 support is fully proved but does **not** constitute its missing ARM run theorem. The nested lookup lemmas preserve arbitrary discarded and retained fields. The width lemmas give `q ≤ 2*|h|` after a successful width check and bound every reverse-decoding accumulator. The overflow lemma proves that both queries are false when the canonical tail is wider than `bits |h|`.

## New declarations

There are 52 new declarations: three public shared theorems and 49 private declarations. Every new theorem/lemma is proved; there is no admitted helper or unproved machine skeleton. Names in the first block are in `Complexity.LogProg`, except `Complexity.pairEncode_getD`; the six `QueryReshape` helpers are in `Complexity`.

| Declaration | Visibility | Role |
| --- | --- | --- |
| `pairEncode_getD` | public | Shared bit-address rule for doubled first fields, separator cells, and suffixes; cites the received `getElem?_dbl`. |
| `inputLength_loop` | public | Shared bounded ARM length-query/increment loop; oracle law is required only through the first failing query. |
| `arm_increments` | private | Private bounded increment-chain proof used by the shared aligned scan. |
| `alignedPair_loop` | public | Shared bounded ARM pair-shape scan at any positive stride; rejects malformed pairs without imposing field canonicality. |
| `AccessLabel` | private | Finite continuations for the one input-access program. |
| `AccessState` | private | Finite reader, increment, rewind, clear, candidate-bump, and answer states. |
| `accessReg` | private | Selects the scan pointer or doubled data pointer for a received read. |
| `accessExit` | private | Selects rejection or a data-phase continuation after validation. |
| `accessTr` | private | Single mode-parametrized transition table for both identity query languages. |
| `accessProg` | private | The call-free program wrapping that table. |
| `accessCfg` | private | Boundary configurations with four binary registers and an optional candidate-head offset. |
| `accessSafe` | private | Work-head bounds in the inclusive interval from minus one to the host-length binary width. |
| `AccessPath` | private | Abbreviation of the received `Relation.ReflTransGen` for safe ordinary steps; no new transitivity proof. |
| `accessPath_run` | private | Converts a bounded closure path into a finite `rrun` with the required trace bound. |
| `accessPath_of_run` | private | Converts a finite bounded `rrun` into the same closure. |
| `accessCfg_safe` | private | Checks the common boundary configuration against the head bound. |
| `access_read` | private | Instantiates frozen `readIn_run`, preserving the candidate head and all other registers. |
| `access_frame` | private | Converts a received one-register fragment frame into the common head bound. |
| `access_inc` | private | Instantiates the received increment fragment on a selected pointer register. |
| `access_clear` | private | Instantiates the received clear fragment on the scan pointer. |
| `access_step` | private | Records one non-call transition in the bounded closure. |
| `access_inc_pointer` | private | Normalizes the pointer-increment endpoint for scan/data continuations. |
| `access_return` | private | Restores the candidate head with `regBack_x`, then clears the scan pointer. |
| `accessTail` | private | Pure specification of streamed tail comparison and the final canonicality bit. |
| `accessTail_eq` | private | Characterizes the streamed comparison by equality with the candidate binary word. |
| `accessTail_canonical` | private | Relates the final tail check to canonical binary representation. |
| `accessCheck` | private | Pure pair-shape/canonical-tail validation result, parameterized by candidate index. |
| `accessCheck_pair` | private | Evaluates that specification on a genuine canonical query. |
| `accessCheck_some` | private | Extracts a genuine pair and canonical index from successful validation. |
| `access_go` | private | Evaluates a control-only step on a boundary configuration. |
| `access_move` | private | Evaluates a single candidate-head movement. |
| `access_symbol` | private | Identifies the candidate tape symbol with its bounded binary-word lookup. |
| `access_tail_run` | private | Proves the streaming tail scan without storing the input index in a register. |
| `access_reject` | private | Composes rejection with the required pointer cleanup. |
| `access_jump` | private | Specializes a control-only bounded transition. |
| `accessCheck_dup` | private | Preserves the pure validation result when stripping an equal doubled pair. |
| `access_scan_run` | private | Proves the aligned physical input scan, tail check, and cleanup. |
| `access_bump` | private | Increments the candidate and completes the doubled data-pointer advance. |
| `accessValue` | private | Mode-parametrized Boolean answer for the identity bit/length query. |
| `accessDone` | private | Halted boundary configuration containing the one-bit answer. |
| `access_answer` | private | Proves the final answer transition. |
| `access_data_run` | private | Reads the two doubled data cells and handles a match, next candidate, or separator. |
| `access_valid` | private | Proves termination and correctness of the candidate loop on a genuine query. |
| `accessLang` | private | Mode-parametrized identity query language. |
| `access_run` | private | Proves correctness on every host, including malformed/non-canonical inputs. |
| `access_mem` | private | Compiles the common program against `Dbl.nilTM` and closes the logarithmic space bound. |
| `dropIdx_prefix_address` | private | Kept output-prefix lookup at host address `4*j`, for arbitrary discarded/retained payloads. |
| `dropIdx_suffix_address` | private | Retained suffix lookup after the nested outer separator, with an explicit in-range hypothesis. |
| `query_index_bound` | private | A successful binary-width check bounds the decoded index by twice the cap, including cap zero. |
| `query_suffix_value_le` | private | Dropping low-order binary digits cannot increase the represented value. |
| `query_accumulator_bound` | private | Bounds all reverse-scan partial accumulators after the width check, using canonicality only of the query tail. |
| `dropIdx_query_overflow` | private | Proves both query answers false when the canonical index is wider than the host-length bound. |

## Scope and flagged changes

Only `InputAccess.lean` and `QueryReshape.lean` are modified, both within the four-file ownership allowance. Full snapshots of all four owned files are included. `Reductions.lean` and `Mult.lean` are unchanged. `PreimageHost.lean` is completely unchanged.

**Imports: unchanged**, including Mathlib imports. No use is made of `ConfigGraph`, `Path`, or `ImmermanSzelepcsenyi` to prove a target.

**New shared exports, flagged under rule 3:** `Complexity.pairEncode_getD`, `Complexity.LogProg.inputLength_loop`, and `Complexity.LogProg.alignedPair_loop`. Each has one new `## Main results` bullet in `InputAccess`. The address theorem is used by both target 8 lookup lemmas. The two bounded ARM fragments are proved continuation infrastructure for the input-length and aligned-layout scans needed across targets 8, 9, and 12; their presence does not claim those targets complete. The aligned fragment is stride-parametrized and checks pair shape only, so it can be reused at the nested strides without separate copies.

**Status edits, flagged:** the target 7 module-result label changes from “sorried” to “proved”, and its theorem docstring's `(phase P4.4b; spec, fill pending)` tag changes to `(phase P4.4b; proved)`. The rest of every landed docstring, including its original proof sketch, is unchanged. No sketch appendix was added. No landed definition, theorem signature, helper body, attribution, or first-delivery proof was altered.

`evidence/check-frozen.py` reconstructs the exact base text by removing the specifically identified new blocks, the three new result bullets, the permitted target 7 proof replacement, and the two status edits. It then compares every owned file byte-for-byte against the base and separately checks all of `PreimageHost`. The check passed, including the target 7 signature comparison. This covers targets 1–6 and every landed declaration in the edited files, not only the named freeze list.

**Escalations: none.** The one size warning is covered by the continuation brief's explicit ground rule 8, “No size cap”; the same rule prohibits adding a split source file. This report records that justification. There is no request to change an interface, import edge, or bound.

## File sizes

| Owned file | Lines | Change |
| --- | ---: | --- |
| `InputAccess.lean` | 1569 | modified |
| `QueryReshape.lean` | 297 | modified |
| `Reductions.lean` | 153 | unchanged snapshot |
| `Mult.lean` | 74 | unchanged snapshot |

## Verification

All campaign Lean checks used the unchanged `scripts/lean_check_tree.sh`. No `lake build` command was issued. The required `lake exe cache get` was attempted; its initial dependency setup failed at executable discovery, and after the environment workaround its internal ProofWidgets release fetch failed. `lake exe cache unpack` successfully unpacked 2,348 already-available cache files. These setup results are recorded in the three cache logs. The pinned mathlib revision remains `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, with a clean dependency working tree.

Lean is v4.25.0. This environment required the same executable-discovery workaround documented by the first delivery: a small `LD_PRELOAD` shim maps only the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`. Its source is `evidence/lean-self-path.c`; it does not change Lean, its kernel, the scripts, or library source. The shim can be compiled with `cc -shared -fPIC evidence/lean-self-path.c -o /absolute/path/lean-self-path.so -ldl`. Set `LD_PRELOAD` to that absolute path only in environments needing the workaround.

The prescribed 92-module bootstrap was run once on the recorded base, in the exact `briefs/orders/ch34-b7.txt` order. It passed with zero errors and exactly 25 baseline sorry warnings. The final sweep rebuilt the eight-module suffix starting at `InputAccess`; its log is reproduced below. There are zero errors, five expected remaining owned admissions (targets 8–12), and exactly the five unchanged downstream warnings (`Path` 2, `ImmermanSzelepcsenyi` 3). `InputAccess` and `PreimageHost` have zero sorry warnings.

```text
Checking TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
Checking TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
Checking TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:262:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:293:8: warning: declaration uses 'sorry'
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
Final sweep: PASS (8 modules)
```

The received `B7StatementsProbe.lean.txt` was copied unchanged to the ignored verification directory and rerun via the campaign script. It passed with zero errors and no admission of its own. A second small probe printed the three new public helpers' axioms, also within the standard triple. Both probe sources and their combined output are included. The twelve target prints, in target order, are:

```text
'Complexity.LogProg.OIS.run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.compile_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_of_logspaceReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.readIn_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_dropIdx' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.compQ' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.comp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.trans' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.multLang_mem_LOGSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The linter's final line is:

```text
style_lint: 0 FAIL, 1 WARN over 45 files
```

`git diff --check` passed. The format-patch series was applied to an isolated index initialized at the base; its resulting tree exactly equals the delivery commit's tree. `git bundle verify` passed. See `evidence/patch-replay.log` and `evidence/bundle-verify.log`.

## Continuation frontier

Resume at **target 8**. Its public statement and original sketch remain untouched. The available public fragments in `InputAccess` are now:

- `pairEncode_getD`: the common positional lookup law.
- `inputLength_loop`: counts the physical host length with a length-query/increment loop while preserving the chosen register bound.
- `alignedPair_loop`: validates a word read by an oracle at an arbitrary positive stride. It uses distinct pointer/end registers and four bounded increment chains, with no canonicality restriction on the decoded fields. On success its pointer is just beyond the separator; on failure it reaches the caller's failure label. It only assumes bit answers at genuine in-range addresses.

Instantiate these in one mode-parametrized ARM over `![inputBitLang, inputLenLang]`. The missing work is the canonical outer-tail scan and width test before accumulating the query value, a bounded decoder, the nested pair-shape scans, final position arithmetic, full all-input run proof, and `arm_decides_poly` assembly. The six private `QueryReshape` lemmas can be cited directly there. Preserve the required register bound `4*|h|+4` and keep both dropped/retained payloads arbitrary.

Then continue in order with target 9's four-oracle bank, canonical inner tail, polynomial output cap (including cap zero and the all-success cap case), and `compQ_length_le` overflow handling. Targets 10 and 11 follow their prescribed corollary routes only after that. Target 12 still needs its complete multiplication ARM, proved column/carry invariant, canonical three-field validation, excessive-result-length rejection, and final carry check. No substitute restatement or additional oracle assumption has been introduced.

## Duplication ledger

**new copies: none**

The exact prescribed screen changed from **227 declarations / 58 pairs / 15,630 characters** to **273 declarations / 67 pairs / 17,169 characters**. All 58 baseline pair rows are unchanged. There are **no new cross-file pairs**, and no new pair at or above 90%. The nine new rows are routine-specific normalizations within a file; their common underlying fragments and address rule are cited, not re-proved.

| New in-file row | Fraction | Justification |
| --- | ---: | --- |
| `access_reject` reproduces `access_jump` | 93/113 = 82% | Both normalize a control step; rejection additionally performs the scan-pointer cleanup. |
| `access_clear` reproduces `access_inc` | 212/271 = 78% | Both transport distinct received register fragments into the same boundary configuration and head invariant. |
| `access_answer` reproduces `access_jump` | 83/113 = 73% | Both establish a one-step boundary record; one halts and writes an answer, while the other changes control. |
| `access_inc` reproduces `access_clear` | 212/299 = 71% | Reverse screen direction of the distinct increment/clear fragment normalization above. |
| `access_bump` reproduces `access_inc` | 177/271 = 65% | Candidate advancement instantiates the received increment fragment and then advances the separate doubled pointer. |
| `dropIdx_prefix_address` reproduces `dropIdx_suffix_address` | 256/420 = 61% | Both cite the one shared paired lookup theorem; prefix and suffix require different range hypotheses and addresses. |
| `dropIdx_suffix_address` reproduces `dropIdx_prefix_address` | 256/443 = 58% | Reverse screen direction of the distinct prefix/suffix address normalization above. |
| `access_jump` reproduces `access_reject` | 93/167 = 56% | Reverse screen direction of the control-step normalization above. |
| `access_bump` reproduces `access_clear` | 157/299 = 53% | Both normalize received register endpoints; one increments two counters and the other clears the scan pointer. |

The shared increment-chain lemma and aligned scan do not introduce a screen pair. The before and after outputs are quoted in full below and included separately.

### Before

```text
declarations screened: 227; copy pairs (target reproduces >= half of source): 58; reproduced text: 15,630 chars
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
   DblLang.lean::sym_lt  reproduces  DblLang.lean::sym_eq: 83/101 = 82%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_eq: 82/101 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   ParsePlain.lean::rrun_one_x  reproduces  Frag.lean::rrun_one_eq: 67/84 = 80%
   Frag.lean::rrun_one_eq  reproduces  ParsePlain.lean::rrun_one_x: 67/85 = 79%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.halt: 185/236 = 78%
   FragDec.lean::rrun_one_reg  reproduces  Frag.lean::rrun_one_eq: 64/84 = 76%
   FragDec.lean::decDAct  reproduces  Lib.lean::incCAct: 61/82 = 74%
   DblLang.lean::sym_eq  reproduces  DblLang.lean::sym_lt: 83/112 = 74%
   CounterProgSim.lean::cf  reproduces  CounterProgSimRun.lean::Bd: 190/257 = 74%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_lt: 81/112 = 72%
   Frag.lean::half_run  reproduces  FragDec.lean::clr_run: 375/520 = 72%
   Frag.lean::eqB_run  reproduces  Parse.lean::regBack_x: 617/864 = 71%
   CounterProgSimRun.lean::ans_append  reproduces  CounterProgSimRun.lean::ans_of_le: 60/86 = 70%
   Lib.lean::incB_run  reproduces  Frag.lean::eqB_run: 654/938 = 70%
   FragDec.lean::decD_run  reproduces  Lib.lean::incC_run: 1179/1733 = 68%
   Frag.lean::halfL_run  reproduces  FragDec.lean::clrE_run: 928/1366 = 68%
   CounterProgSimRun.lean::ans_of_le  reproduces  CounterProgSimRun.lean::ans_append: 60/90 = 67%
   ImplicitPoly.lean::rounds  reproduces  DblLang.lean::Rch.trans: 134/202 = 66%
   CounterProgSim.lean::pr_reach  reproduces  CounterProgSim.lean::pr_halt: 836/1262 = 66%
   Parse.lean::regBack_x  reproduces  Frag.lean::eqB_run: 617/938 = 66%
   FragDec.lean::clrEAct  reproduces  FragDec.lean::toEndAct: 144/229 = 63%
   Lib.lean::incB_run  reproduces  Parse.lean::regBack_x: 536/864 = 62%
   InputAccess.lean::readFrame  reproduces  InputAccess.lean::readAt: 66/107 = 62%
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   InputAccess.lean::readIn_run  reproduces  InputAccess.lean::read_one: 81/135 = 60%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   InputAccess.lean::read_cleanup  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::read_cleanup: 523/993 = 53%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%
```

### After

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

## Archive use

Run `sha256sum -c SHA256SUMS` in the extracted archive directory. The manifest covers every other archive file and excludes itself.

Apply the patch series to the recorded base, or fetch `fill/ch34-b7-cont` from `fill-ch34-b7-cont.bundle` into a repository containing that base. The bundle is incremental and declares the base as a prerequisite. The full source snapshots use their original `TCSlib/...` paths; the two unchanged owned snapshots are included for completeness.

For a fresh checkout, first bootstrap the prescribed order with `scripts/lean_check_tree.sh`. To repeat the final sweep, run `bash /path/to/extracted/evidence/final-sweep.sh` from the repository root. Copy the two probe sources into `.lake/b7-verification/` and run each through the same script. Run the frozen-source check as `python3 /path/to/extracted/evidence/check-frozen.py /path/to/repo 37ab609199b2fad253b136375243db20faf88b16`.

This archive is a verified partial continuation. Targets 8–12 must still be completed to meet the brief's full zero-admission gate.
