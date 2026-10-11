# B7 partial fill delivery: targets 1–6

**Status: partial delivery under the continuation-budget provision of `briefs/ch34-b7.md`, ground rule 9.** Targets 1–6 are proved. Targets 7–12 retain their original `sorry` bodies. There are **no new admitted helpers**, and **no completed target is proved modulo an admission**. The complete-delivery requirement of zero owned admissions is therefore still unmet.

No mathematical obstruction or frozen-table defect was found. The remaining machine constructions were not completed within this run's continuation budget. This report distinguishes that incomplete work from an escalation about an unprovable statement.

## Repository and handoff

| Item | Value |
| --- | --- |
| Repository | `https://github.com/Shilun-Allan-Li/tcslib` |
| Checked-out campaign branch | `complexity/arora-barak-ch3-4` |
| Base | `a1999089922a3485628426c5d8cbdc8d96b7b6b9` |
| Required ancestor | `315571bec99312e635121a8e3c9b6e8cf5e9f283` |
| Ancestor check | `git merge-base --is-ancestor` succeeded before editing; rechecked against the recorded base |
| Working branch | `fill/ch34-b7` |
| Delivery commit | `b548494681801107c2a000d16db1f3056cfae1d3` |
| Patch series | One `git format-patch` patch, against the recorded base |
| Bundle | `fill-ch34-b7.bundle`, incremental, with the recorded base as its prerequisite |
| Remote actions | No push, PR, or rebase |

The patch replay was checked with an isolated Git index initialized at the base. Its resulting tree exactly equals the delivery commit's tree. `git bundle verify` also passed. Their logs are in `evidence/patch-replay.log` and `evidence/bundle-verify.log`.

The archive includes full snapshots of all five owned files. Only three differ from the base:

| File under `TCSlib/Complexity/SpaceComplexity/Logspace/` | Lines | Change |
| --- | ---: | --- |
| `InputAccess.lean` | 541 | Target 6 and 14 private helpers |
| `PreimageHost.lean` | 822 | Targets 1–3 and 16 private helpers |
| `QueryReshape.lean` | 195 | Unchanged snapshot |
| `Reductions.lean` | 153 | Targets 4–5 |
| `Mult.lean` | 74 | Unchanged snapshot |

All tracked edits are in the three owned files above. Reports, logs, temporary probes and packaging files were kept outside tracked source files. No file split or additional source file was introduced.

## Target and axiom ledger

The numbers and processing order are those of the brief. Every entry below was checked by the unchanged pre-ship probe on fresh owned/downstream oleans. `Std` means exactly `[propext, Classical.choice, Quot.sound]`; `Std + sorryAx` includes the original admission.

| # | Target, in namespace `Complexity` | Status | Axioms |
| ---: | --- | --- | --- |
| 1 | `LogProg.OIS.run` | Proved | Std |
| 2 | `LogProg.OIS.compile_decides` | Proved | Std |
| 3 | `mem_LOGSPACE_preimage` | Proved | Std |
| 4 | `mem_LOGSPACE_of_logspaceReducible` | Proved | Std |
| 5 | `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` | Proved | Std |
| 6 | `LogProg.readIn_run` | Proved | Std |
| 7 | `implicitlyLogspaceComputable_id` | Original admission retained | Std + sorryAx |
| 8 | `implicitlyLogspaceComputable_dropIdx` | Original admission retained | Std + sorryAx |
| 9 | `ImplicitlyLogspaceComputable.compQ` | Original admission retained | Std + sorryAx |
| 10 | `ImplicitlyLogspaceComputable.comp` | Original admission retained | Std + sorryAx |
| 11 | `LogspaceReducible.trans` | Original admission retained | Std + sorryAx |
| 12 | `multLang_mem_LOGSPACE` | Original admission retained | Std + sorryAx |

New private helpers remaining `sorry`: **none**. Proved targets depending on admitted private helpers: **none**. The existing `inputBitLang_mem` and `inputLenLang_mem` still depend on target 7 and still print `sorryAx`. No unexpected axiom appears in the probe.

## Binding routes followed

1. **Oracle simulation.** `imageCfg` stores the source tapes on `castSucc` registers, the canonical input index on the last register, and the left-boundary condition in the phase. `represented_step` obtains the symbol with at most two genuine calls, applies the frozen lifted action, and realizes the frozen `nextPh` table through the received increment/decrement fragments and zero test. The proof uses only the stated oracle laws: length calls at `i ≤ |v|`, and bit calls at `i < |v|`. `run` inducts up to the first source halt. `source_head_bounds` cites the visited-cell displacement bound, visited-set monotonicity, and the individual summand bound for total space.

   A terminal source action already halts the host through the frozen lifted action. Consequently, the private representation requires index equality with the source input position only while the source is live; after a halt the old index remains bounded. This is an internal invariant choice and does not alter any frozen statement or transition.

2. **Compilation.** The oracle is the indicator of the two bank languages. The call clause supplies the canonical query and input/head positions; `vword_whole₁`, `tapeWord_bufferTape`, `bank_cleanRun`, and `CleanRun.mono` establish `CallOK`. The proof retains the scalar radius `B`, including the non-monotone-`sb` case. `compile_space` and `Fin.sum_univ_castSucc` produce the exact frozen space expression.

3. **Preimages.** The bank is `![length decider, bit decider]`. The proof uses the genuine-query membership lemma, the source decider's time on `f x`, and the indicator identity. It takes the prescribed radius `(cl + cb) * logSpace (2 * |x| + 2 + |bits (|f x| + 1)|) + 1`. Two instances of `log_poly_bound`, binary-length monotonicity, and elementary arithmetic give a constant multiple of `logSpace |x|`.

4. **Downward closure.** Unpack the reduction, rewrite the language as a preimage with `Set.ext`, and apply target 3, as prescribed.

5. **NL collapse.** Set antisymmetry uses target 4 for the forward inclusion and `LOGSPACE_subset_NL` for the reverse inclusion.

6. **Input-read fragment.** The proof inducts on the counter up to `min i |x|`, invoking `eq_run` with the counter as its first register, then `inc_run` when another input position is required. It handles equality and the right blank separately, then invokes `rewind_x` and `clr_run`. All configuration fields are restored as required by the frozen statement.

   A private instance of the existing table uses disjoint phase/exit labels and halting exit states. This recovers the stronger phase-membership trace needed by the contract, without assuming that the caller's label map is injective. The run is transported to arbitrary caller labels by the table's state-map compatibility. The four received sub-runs are cited, not re-proved. The head range depends on `|x|`, not on the requested `i`; this does not make storing a large index free.

The completed proofs cite no result from `ConfigGraph`, `Path`, or `ImmermanSzelepcsenyi`. The preimage engine cites nothing from `Reductions` and is independent of the unfilled identity theorem; the axiom log confirms that independence.

## New declarations

Every declaration below is private and fully proved, or a proof-only definition. There are no new public exports, instances, imports, or namespaces.

### `PreimageHost.lean`, namespace `Complexity.LogProg.OIS`

| Name | Role |
| --- | --- |
| `imageCfg` | Encode a source configuration on the host with an explicit index and phase. |
| `Represents` | Simulation-boundary invariant, including the live-state index equation. |
| `Safe` | Intermediate head bounds and canonical-call conditions. |
| `imageCfg_safe` | Encoded configurations satisfy `Safe` under source-head bounds. |
| `ask_step` | Execute the length-query node and preserve the encoded data. |
| `bit_step` | Execute the bit-query node and retain its answer in the phase. |
| `work_step` | Apply the frozen lifted action to the represented source tapes and output. |
| `index_view` | Identify the received register-fragment configuration with the encoding. |
| `index_fragment_safe` | Convert a received index-fragment trace into `Safe`. |
| `index_inc` | Instantiate the received increment proof on the last register. |
| `index_dec` | Instantiate the received decrement proof on the last register. |
| `zero_step` | Execute the frozen zero test on the canonical binary index. |
| `adjust_index` | Prove every clamped-move branch of the frozen phase table. |
| `represents_safe` | Derive the intermediate invariant at a represented boundary. |
| `represented_step` | Simulate one live source step, including calls and index adjustment. |
| `source_head_bounds` | Bound source heads using total visited-cell space at the final time. |

### `InputAccess.lean`, namespace `Complexity.LogProg`

| Name | Role |
| --- | --- |
| `readModel` | Proof-only instance of `readTr` with disjoint phase and exit labels. |
| `readAt` | Canonical boundary configuration with explicit counter and input position. |
| `readFrame` | The preserved tapes/output and permitted two-head range. |
| `readFrame_reg` | Convert a counter-fragment configuration to `readFrame`. |
| `readFrame_at` | Establish the frame at a routine boundary. |
| `read_eq` | Apply the received comparison, bounding both heads by the counter length. |
| `read_one` | Unfold one ordinary step of the proof-only table instance. |
| `read_cleanup` | Concatenate the received input rewind and counter clear. |
| `read_advance` | Compare, advance the input, and increment the counter for one loop round. |
| `read_finish` | Read the answer at `min i |x|` and complete cleanup. |
| `read_model_run` | Induct through the loop and append the finishing run. |
| `read_run_eq` | Identify the no-call register run with the ordinary machine run. |
| `read_model_phase` | Exclude an exit or halt strictly before the final live exit. |
| `read_action_map` | Show that the frozen table commutes with label replacement. |

## Freeze and status-text audit

`evidence/freeze-check.py`, run against the recorded base, verifies all twelve target signatures, all thirty other landed declarations, declaration order, unchanged imports, and unchanged remaining comment-stripped top-level commands. All new declarations are private and contain no admission. Its output is in `evidence/freeze.log`.

All original block comments were also checked byte-for-byte after applying only the following allowed status changes; see `evidence/status-text.log`:

| File | Flagged status edits |
| --- | --- |
| `InputAccess.lean` | The module bullet for `readIn_run` changes `sorried` to `proved`; its theorem tag changes `spec, fill pending` to `proved`. |
| `PreimageHost.lean` | The three main-result bullets change `sorried` to `proved`; the three target theorem tags change `spec, fill pending` to `proved`. |
| `Reductions.lean` | The main-results status label now says two phase-P4.4 statements proved and two remain sorried; the tags on targets 4 and 5 change to `proved`. |

No original attribution, definition, helper proof, sketch prose, or non-status docstring text changed. There are no removed declarations, restatements, signature changes, sketch appendices, Mathlib import additions, or TCSlib import additions. Targets 7–12 were kept unchanged to preserve the required fill order for continuation.

## Verification

All Lean elaboration checks used **only `scripts/lean_check_tree.sh`**. `lake build` was never run. `lake exe cache get` was used for the pinned dependencies.

| Check | Result | Evidence |
| --- | --- | --- |
| One-time bootstrap | Exact 92-module brief order; exit 0; 0 errors; 31 baseline sorry warnings | `evidence/bootstrap.log`, `evidence/ch34-b7-order.txt` |
| Final owned/downstream sweep | All 8 modules passed; 0 errors; fresh oleans | `final-sweep.log`, `evidence/final-sweep.sh` |
| Owned admission warnings | InputAccess 1, PreimageHost 0, QueryReshape 2, Reductions 2, Mult 1 | `final-sweep.log` |
| Downstream admission warnings | Path 2, ImmermanSzelepcsenyi 3, facade 0; exactly the base set | `final-sweep.log` |
| Pre-ship probe | Unchanged source, exit 0, 0 errors, no admission of its own | `evidence/B7StatementsProbe.lean`, `axioms.log` |
| Axiom prints | Six completed targets: Std; six remaining targets: Std + sorryAx | `axioms.log` |
| Campaign style lint | 0 FAIL, 0 WARN over 45 files | `evidence/lint.log` |
| Freeze and imports | Passed | `evidence/freeze.log`, `evidence/status-text.log` |
| Whitespace check | `git diff --check` passed | Delivery patch |
| Duplication screen | 0 new cross-file pairs; 5 justified in-file pairs, all below 90% | Both screen logs, quoted below |
| Patch and bundle | Patch replay equals delivery tree; bundle verifies | `evidence/patch-replay.log`, `evidence/bundle-verify.log` |

The final sweep is the suffix of the prescribed order starting at `Logspace/InputAccess`: InputAccess, PreimageHost, QueryReshape, Reductions, Path, ImmermanSzelepcsenyi, Mult, and the SpaceComplexity facade. The root `TCSlib` module was excluded as instructed. All nineteen out-of-scope baseline admissions were left untouched; five of them appear in the final downstream sweep.

The pre-ship probe was copied unchanged to the ignored `.lake/b7-verification/B7StatementsProbe.lean` so that the unchanged check script could elaborate it within Lean's repository-root restriction. Its inherited prose about all targets being sorried describes the old baseline; the actual printed axioms in `axioms.log` are authoritative for this delivery.

### Runtime details

Lean: `leanprover/lean4:v4.25.0`. Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The toolchain and package pins were not modified.

The execution environment exposed the current executable through `/proc/self/exe` while Lean's startup lookup through `/proc/<its-pid>/exe` failed. Checks therefore used a narrow `LD_PRELOAD` compatibility shim. Its complete source is `evidence/lean-self-path.c`: it redirects only that exact current-process lookup to `/proc/self/exe` and delegates all other `readlink` calls unchanged. It does not replace Lean, modify the kernel or proof checker, or suppress diagnostics. The campaign script itself is unchanged. A normal Lean installation should not need this shim.

The shim can be compiled, if that environment issue recurs, with:

```sh
cc -shared -fPIC -o lean-self-path.so lean-self-path.c -ldl
```

Use its absolute path in `LD_PRELOAD` when running the unchanged campaign script in that environment.

## Continuation

Resume at **target 7**. Targets 7–12 still have their original sketches and statements. No unproved private machine skeleton was added to the source tree.

The next construction must supply a single mode-parametrized, call-free program for the identity bit and length languages. The completed `readIn_run` is available for general input access. Validate aligned doubled pairs and the canonical tail, compare the query tail against a bounded counter while streaming, and compile against `Dbl.nilTM`. Do not copy the query index into workspace. The independent head bound in `readIn_run` does not discharge that storage obligation.

Then continue in the brief's order: target 8's single mode-parametrized ARM over the input-access bank, with the overflow check before accumulating the index and no canonicality restriction on `dropIdx`'s arbitrary payloads; target 9's four-oracle ARM with its polynomial cap, the zero-cap case, canonical inner tail, and `compQ_length_le` overflow bound; targets 10 and 11 by their short prescribed corollary routes; and target 12's multiplication ARM, including a proved carry/column invariant, canonical field validation, and excessive-result-length rejection.

`InputAccess.lean` currently has 541 lines. Reuse its completed private proof structure where appropriate, and respect the brief's approximately 1000-line limit. A split into a new source file would require escalation; no such split is included here.

## Duplication ledger

**new copies: none**

No privately copied received theorem body was introduced. The engine and reader instantiate the received fragments, compiler and bank proofs. The prescribed short corollary bodies for targets 4 and 5 follow the brief directly. Identified copied received proof material is 0 lines (0%) in each touched file; the pre-existing screen pairs do not involve these owned files.

The required text-level screen was run before edits and after the final source edits, over exactly the population specified in the brief. It changed from 192 declarations / 53 pairs / 14,788 reproduced characters to 227 declarations / 58 pairs / 15,630 reproduced characters. All 53 original pair rows are unchanged. There are no new cross-file pairs and no new pair at or above 90%.

The five new in-file rows reflect the common configuration fields or the assembly of distinct received sub-runs:

| New row in `InputAccess.lean` | Fraction | Justification |
| --- | ---: | --- |
| `readFrame` reproduces `readAt` | 66/107 = 62% | The frame existentially varies the same record's counter tape and two head positions; it is a predicate, while `readAt` constructs a boundary record. |
| `readIn_run` reproduces `read_one` | 81/135 = 60% | Both unfold an ordinary no-call step; the public theorem transports arbitrary labels over a whole trace, whereas `read_one` evaluates one model step. |
| `read_cleanup` reproduces `readFrame_at` | 86/156 = 55% | Both normalize the received register view; cleanup composes rewind and clear, and explicitly cites the boundary-frame lemma for the rewind trace. |
| `read_advance` reproduces `readFrame_at` | 86/156 = 55% | The increment endpoint uses the same boundary-record normalization; advance cites the frame lemma and proves a different state/counter transition. |
| `read_advance` reproduces `read_cleanup` | 523/993 = 53% | Both concatenate finite `rrun` fragments and convert their framed traces; one assembles equality/input-advance/increment, the other rewind/clear, with different endpoints and bounds. |

The full unedited outputs follow and are also included as separate evidence files.

### Before

```text
declarations screened: 192; copy pairs (target reproduces >= half of source): 53; reproduced text: 14,788 chars
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
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%
```

### After

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

## Archive verification and use

From the extracted archive directory, run `sha256sum -c SHA256SUMS`. The manifest covers every other archive file; it excludes itself.

Apply the format-patch series to the recorded base, or fetch the `fill/ch34-b7` ref from the included bundle into a repository containing that base. `git bundle verify` reports the required prerequisite explicitly. The patch series and bundle contain the same single delivery commit.

For a fresh verification checkout, first bootstrap the prescribed `briefs/orders/ch34-b7.txt` order using `scripts/lean_check_tree.sh`. To repeat the final suffix sweep, run `evidence/final-sweep.sh` from the repository root. To repeat the axiom/probe check, copy `evidence/B7StatementsProbe.lean` into `.lake/b7-verification/` and run:

```sh
bash scripts/lean_check_tree.sh .lake/b7-verification/B7StatementsProbe
```

This archive is ready for review and continuation. It does not meet the full B7 zero-admission completion gate until targets 7–12 are filled and checked.
