B2b continuation delivery — PARTIAL

**Neither target is closed without admissions: 0/2 fully proved.** This is the partial ZIP authorized by the brief's continuation-budget rule (ground rule 9). The sole remaining private admission is `b2b_host_contract`, declared at source line 740, with the `sorry` at line 762 and a preceding literal **Proof sketch**. Its composed setup, shared-round and global fixed-window proofs remain unfinished. No counterexample or incompatible library contract has been established; the stopping reason is the continuation budget, not a claim that the frozen statements are false.

| Target | Delivered state | Axioms |
|---|---|---|
| `Complexity.NP_subset_PSPACE` | Public packaging proof assembled around the admitted private host contract; not closed. | `propext, sorryAx, Classical.choice, Quot.sound` |
| `Complexity.SAT3_mem_PSPACE` | Corollary body is `NP_subset_PSPACE SAT3_mem_NP`; inherits the unfinished inclusion. | `propext, sorryAx, Classical.choice, Quot.sound` |

Fifteen supporting private theorems are proved and their collected axioms are all within `[propext, Classical.choice, Quot.sound]`; see `logs/axioms.log` and the reproducible `evidence/ProofAxioms.lean`. The proved-modulo set remains empty: no sorried library row was accepted as a permitted dependency. The complete-delivery zero-`sorryAx` gate is **not met**.

**Repository and scope.** Repository: `https://github.com/Shilun-Allan-Li/tcslib`. The actual fresh checkout used campaign branch `complexity/arora-barak-ch3-4` before the working branch was created.

- Base: `aed5b4ffe3b8ac2ad030ee383ba7e974de730d5a`.
- Working branch: `fill/ch34-b2b`.
- Delivery commit: `5137a0b7b0fd110fe60aaadb9766c5a3c18121c1`.
- Required `git merge-base --is-ancestor 2483ff81d2e20427bd193595295f3b1ef53b1a57 HEAD`: passed before work, and rechecked successfully against both the base and delivery head.
- An earlier isolated cached-checkout fallback lacked the required ancestor and was abandoned without edits; substantive work began only in the fresh campaign clone after its successful check.
- Only changed repository path: `TCSlib/Complexity/SpaceComplexity/Inclusions.lean`. No rebasing, push or PR.
- Patch: 703 insertions, 3 deletions. Both target signatures and the complete statements/proofs of `DTIME_subset_SPACE` and `P_subset_PSPACE` are byte-identical to the base. Original docstrings are retained; see `logs/freeze.log`.

**Imports, appendix and status.** Exactly the five sanctioned imports were added before bootstrap, under the flagged comment `B2b sanctioned imports (briefs/ch34-b2b.md)`: `Build.CounterLoop`, `Build.VirtualInput`, `Build.Seam`, `SpaceComplexity.Machines.Clean`, and `CircuitComplexity.MeyerTableau`. No other import was added. The flagged `Fill appendix (B2b)` identifies `counterLoopTM`, `phaseHostTM`, `cleanTM_run` and the copy-assembled virtual input. The module status text is deliberately unchanged because this is a partial delivery. New public declarations: **0**. Escalations for an unprovable statement or incompatible row: **none established**; the remaining composition obligations are explicitly open.

**Construction and continuation frontier.** The concrete test, loop body and outer host are defined. The four allowed glue machines are rewind, verdict reader, stationary anchor and final answer; all other machines assemble the prescribed library rows. There is one shared test, one rewind definition, one `counterLoopTM`, and a single polynomial ledger theorem. `b2b_hostedSource_run` is proved, including the fixed bank-radius trajectory, by composing the public rewind, clean, returning-embedding and R2 contracts. This is a proof about the prescribed hosted source, not a new virtual-input simulation or first-halt lemma.

The next fill must finish `b2b_host_contract` without weakening it or the targets:

1. Prove the S1-S5 setup configuration and trajectories using the existing clean/capture, virtual rewind, copy, overflow increment and native rewind rows. Use `b2b_clean_run` for identity/setup and `b2b_vhost_rewind` for S2.
2. Prove one shared test/round contract, used for every counted trial and the final continuation. Compose the framed copy with `b2b_buffer_concat`, lift `b2b_hostedSource_run` through `vhostEmitTM` and capture, and apply `b2b_verdict_trace`. Each public row's endpoint and no-earlier-exit clauses must supply `phaseHostTM_run` guards; use `b2b_dispatch_retag` between phases. On rejection, apply the framed clear and increment rows. The round must record no intermediate anchor/escape and fixed tape windows.
3. Choose the existential first-arrival durations classically, and instantiate `counterLoopTM_run_escape` or `counterLoopTM_run_done`. Consume their counter/body trajectory clauses. The completed arithmetic lemmas identify the orbit and the exact certificate quantifier; reuse the shared test for the final word.
4. Compose the setup, counter loop, final test and answer using the existing phase host. Establish a global physical-output invariant: all trials capture internally and only the final answer emits one bit.
5. Bound each trajectory in the fixed windows below; apply `Finset.card_le_card` and `Int.card_Icc` inline and sum over tapes. `b2b_ledger_bound` and `b2b_mem_PSPACE_of_ledger` already finish the polynomial arithmetic and PSPACE normalization. Do not use exponential total time to bound space.

No completed shared round lemma is claimed in this checkpoint. The remaining admission packages that missing composition so the continuation has a concrete typed machine and an exact proof goal.

**Question 5 obligations.** Each line distinguishes proved components from the missing discharging composition.

| Obligation | Current evidence and remaining discharging lemma |
|---|---|
| 1. Exact width, all certificates, overflow and width zero | `b2b_counter_value`, `b2b_certificate_orbit`, `b2b_verifies_iff` are proved; setup/round/loop execution is still inside open `b2b_host_contract`. Overflow is to be discharged by the **count**: `2^Q - 1` counted rounds plus the final continuation call. The setup's single overflow produces `0^Q`; no counted round overflows. At `Q=0` there are zero counted rounds and one call on `[]`. At `n=0`, `Q(0)=C`, which need not be zero. |
| 2. Preserve input/certificate and verify exactly `x ++ u` | `b2b_buffer_concat`, `b2b_hostedSource_run` and `b2b_vhost_rewind` are proved; framed embedding and shared-test composition in `b2b_host_contract` remain open. No new virtual-input transformer or boundary simulation is introduced. |
| 3. Internal one-bit capture; one final physical bit | `b2b_verdict_trace` and `b2b_answer_run` are proved, and test phases use silent capture; the global output invariant is still an obligation of `b2b_host_contract`. |
| 4. Reset scratch and heads between trials | `b2b_clean_run`, `b2b_clean_verifier` and `b2b_hostedSource_run` are proved; the recurring test/body configuration invariant, including buffer clear, remains in `b2b_host_contract`. No trial history is stored by the defined host. |
| 5. Fixed windows across all trials | `b2b_hostedSource_run` proves the bank-radius trajectory and `b2b_ledger_bound` proves polynomial arithmetic. The phase/loop global trajectory and interval-cardinality step in `b2b_host_contract` are still open. Per-call cardinality alone is not asserted to bound the union. |

The intended fixed windows remain exactly those in route H: `U` and counter `[-1,Q]`; `BUF` `[-1,n+Q]`; `CAP` `[0,1]`; verifier banks `[-s,s]` with `s=cV((n+Q)^e+1)`; identity banks `[-cI,cI]`; setup banks `[-cP(n+1),cP(n+1)]`. The open host contract uses their common enclosing radius

`W(n) = n + C(n+1)^c + cV((n+C(n+1)^c)^e+1) + cI + cP(n+1) + 1`

and ledger `K(2W(n)+1)`, where `K=b2b_tapeCount MV.k MI.k MP.k+1`. The proved `b2b_ledger_bound` bounds this by `D(n+1)^f` with `f=(c+1)(e+1)`. There is no factor equal to the number of certificates. Note 9's delivered statement remains polynomial space; no linear-space claim is made.

**All new source declarations.** There are **43 named private declarations plus 6 private instances = 49 new private source declarations**. Derived constructors, recursors and generated instance declarations are not counted separately. The campaign linter counts named declarations only, so it reports 4 public / 43 private. The four public declarations predate this fill.

| Source line | Private declaration | Role |
|---|---|---|
| 97 | `b2b_clean_run` | Proved general cleaned computation and source-space contract via cleanTM_run. |
| 118 | `b2b_clean_verifier` | Proved cleaned verifier contract from P_subset_PSPACE; specializes b2b_clean_run. |
| 130 | `B2bRewindState` | Three states of the sanctioned halting rewind glue. |
| 135 | `b2b_rewindTM` | The single rewind glue definition, using controlAction; only the halting variant. |
| 147 | `b2b_rewind_run` | Proved direct instance of public FinTM.rewind_heads; no rewind induction. |
| 157 | `b2b_vhost_rewind` | Proved use of vhostEmitTM_runFrom to restore a captured work-word head to zero without changing its buffer. |
| 177 | `B2bVerdictState` | States of the sanctioned two-step verdict reader. |
| 181 | `b2b_verdictTM` | Verdict glue using tapeAction; moves left, reads and erases the captured bit. |
| 197 | `b2b_verdict_trace` | Proved complete two-step verdict trace, including the frame and output. |
| 231 | `b2b_anchorTM` | The sanctioned stationary one-state anchor glue. |
| 236 | `b2b_answerTM` | The sanctioned final answer emitter built from emitAction [b]. |
| 241 | `b2b_answer_run` | Proved instance of emit_halts for the final answer. |
| 249 | `b2b_hostedSource` | The prescribed D: returning rewind; returning clean verifier; halting rewind, assembled with R2. |
| 261 | `b2b_embed_refl` | Proved identity embedding configuration equation using selected tape/head projections. |
| 279 | `b2b_hostedSource_run` | Proved D execution from arbitrary native position at least one: one bit, blank banks, origin bank heads, input head one, and fixed bank-head radius throughout. |
| 388 | `b2b_dispatch_retag` | Proved pure configuration retagging equation for a phase dispatch. |
| 397 | `b2b_counter_value` | Proved Nat.ofDigits value of the all-true counter word: 2^Q - 1. |
| 409 | `b2b_certificate_orbit` | Proved fixed-width increment orbit equals the public Meyer enumeration below overflow. |
| 419 | `b2b_verifies_iff` | Proved exact equivalence between enumerated candidates and the received fixed-length witness quantifier. |
| 437 | `b2b_buffer_concat` | Proved global bufferTape concatenation equation for the framed append copy. |
| 457 | `b2b_mem_PSPACE_of_ledger` | Proved normalization from a D(n+1)^f ledger to PSPACE via succ_pow_le. |
| 472 | `b2b_tapeCount` | The fixed body tape count: three word tapes plus verifier, identity and setup banks. |
| 475 | `b2b_wordTape` | Explicit U, BUF and CAP selection. |
| 479 | `b2b_bankEmb` | Explicit contiguous bank selection with Fin.ext/omega injectivity. |
| 489 | `b2b_callEmb` | Explicit virtual buffer/bank selection: buffer to BUF, banks to the verifier bank. |
| 502 | `b2b_singleEmb` | One-tape selection for setup virtual rewind. |
| 506 | `B2bTestPhase` | Tags for the six prescribed shared-test phases. |
| 510 | `b2b_testState` | Dependent state family of the shared test. |
| 520 | `anonymous test Fintype instance` | Private Fintype instance for the test phase state family. |
| 524 | `anonymous test DecidableEq instance` | Private DecidableEq instance for the test phase state family. |
| 528 | `b2b_testPhases` | The six prescribed embedded public rows, with disjoint banks. |
| 548 | `b2b_testRedirect` | The prescribed live-exit redirects inside the shared test. |
| 558 | `b2b_testTM` | Single shared phaseHostTM test definition, reused in the loop body and continuation. |
| 563 | `B2bBodyPhase` | Tags for test, clear and increment. |
| 567 | `b2b_bodyState` | Dependent body state family. |
| 572 | `anonymous body Fintype instance` | Private Fintype instance for the body phase state family. |
| 576 | `anonymous body DecidableEq instance` | Private DecidableEq instance for the body phase state family. |
| 581 | `b2b_bodyPhases` | The shared test, public clearTM and public incrementTM. |
| 589 | `b2b_bodyRedirect` | False verdict to clear to increment to anchor; true verdict is the body exit. |
| 597 | `b2b_bodyTM` | Prescribed body assembled only with phaseHostTM. |
| 602 | `B2bHostPhase` | Tags for S1-S5, counter loop, last test and the two answers. |
| 607 | `b2b_hostState` | Dependent outer-host state family. |
| 617 | `anonymous host Fintype instance` | Private Fintype instance for the host phase state family. |
| 621 | `anonymous host DecidableEq instance` | Private DecidableEq instance for the host phase state family. |
| 626 | `b2b_hostPhases` | S1-S5, the one counterLoopTM, the embedded shared test and final answer emitters. |
| 646 | `b2b_hostRedirect` | The exact route-F redirects, including loop exhaustion and escape. |
| 659 | `b2b_host` | FinTM packaging of the outer phaseHostTM assembly. |
| 671 | `b2b_ledger_bound` | Proved polynomial domination of the fixed common-radius space ledger; no factor 2^Q. |
| 740 | `b2b_host_contract` | OPEN: the only admitted private helper, with a Proof sketch; setup, shared round and global trajectory composition remain. |

**Duplication governance.** **new copies: none**. The full before and after outputs are quoted at the end of this report and also provided separately under `logs/`. There are no new cross-file pairs involving `Inclusions`. The only new in-file screen pair is:

```text
Inclusions.lean::b2b_callEmb  reproduces  Inclusions.lean::b2b_bankEmb: 67/102 = 66%
```

Justification: the two different explicit `Fin` selections share constructor and injectivity boilerplate (`Fin.ext`/`omega`); one is contiguous offset selection and one places the virtual buffer separately from its banks. This is a 66% text match, below the 90% copy threshold, and copies no existing theorem proof. No >=90% new pair needs factoring. The owned file contains zero copied existing proof bodies (0 bytes; 0% under the brief's copy classification). EXP's private enumerator, a second counter/loop host, new rewind induction, new first-halt lemma, new visited-interval lemma and new virtual-input proof are absent.

**Size and integrity.** `Inclusions.lean`: **815 lines, 40,907 bytes**; 0 new public and 49 new private source declarations as counted above. Source SHA-256: `181d01a58ebeded98af3e166f83a875091d8c89444c4467d3aaf69af1338cb81`. `git diff --check` passes and the committed working tree is clean. `evidence/private-declarations.json` provides the source-line inventory.

**Verification.** Lean 4.25.0; pinned mathlib commit `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Every Lean elaboration used `scripts/lean_check_tree.sh`; `lake build` was never run. `lake exe cache get` completed successfully for 7506 files (`logs/cache-get-isolated.log`). The required 112-module order was bootstrapped once with resumptions, not repeatedly rebuilt. The initial pass reached module 74, `MeyerMachineRun`, where Lean exited with SIGBUS while cache files were still being populated. After cache completion it was resumed from module 74; that pass reached the draft Inclusions errors. The edited Inclusions was then checked to success and modules 95-112 were completed. These transient failures are retained in `bootstrap.log` and `bootstrap-resume.log`; the successful tail is in `bootstrap-tail.log`. The final sweep is the authoritative check of the committed source and required downstream modules.

The execution environment required an executable-discovery workaround: `/proc/<self-pid>/exe` was inaccessible while `/proc/self/exe` worked. `environment/lean-self-path.c` redirects just that `readlink` path via `LD_PRELOAD`; it does not modify Lean, its kernel, source dependencies or proof checking. It was compiled locally with `cc -shared -fPIC -O2 -o lean-self-path.so lean-self-path.c -ldl`, and checks used `LD_PRELOAD=/absolute/path/lean-self-path.so bash scripts/lean_check_tree.sh MODULE`. Dependency package directories were copied into the clone from an existing matching pinned mathlib snapshot, then the prescribed cache fetch succeeded using an isolated cache directory after a shared-cache collision. No dependency source was edited.

Final sweep: exit 0, fresh oleans, zero errors. It intentionally does **not** meet the completed-fill zero-warning gate: Inclusions has exactly one remaining sorry warning. Downstream TQBF has its four unchanged base warnings; both facades have none. Full final sweep:

```text
>>> TCSlib/Complexity/SpaceComplexity/Inclusions
TCSlib/Complexity/SpaceComplexity/Inclusions.lean:740:16: warning: declaration uses 'sorry'
>>> TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE/TQBF.lean:160:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:222:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:274:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:282:8: warning: declaration uses 'sorry'
>>> TCSlib/Complexity/ClassPSPACE
>>> TCSlib/Complexity/SpaceComplexity
```

The unchanged maintainer pre-ship probe was copied to `.lake/b2b-probes/B2bProbe.lean` and re-run with the check script: exit 0, zero errors, and all 11 explicitly printed probe-helper axiom sets within the standard triple. `Build/Zone` and `ClassNP/Nondeterminism` were checked first because this probe imports them outside the prescribed 112-module closure. Their untouched warnings are recorded in `logs/probe-dependencies.log`. The probe's SAT3 example is conditional on the target; the probe does not establish that this partial target is admission-free.

Final target axiom prints (complete-delivery gate **fails**, as required to disclose for this partial):

```text
'Complexity.NP_subset_PSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.SAT3_mem_PSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The same axiom log verifies all 15 completed private theorem helpers against the standard triple and ends `Checked 15 private proved helpers: no sorryAx.` Lint (`python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`): **style_lint: 0 FAIL, 0 WARN over 45 files**. The 815-line size is an informational notice; this brief sets no size cap. Frozen declarations/import scope checks passed as recorded in `logs/freeze.log`.

**Archive and reproduction.** The ZIP includes this report, full owned source, one `git format-patch` patch, an incremental git bundle, sweep and axiom logs, the unchanged pre-ship probe, axiom-check source, both duplication screens, bootstrap evidence, environment workaround source, the brief/order reference, and `SHA256SUMS`. The bundle requires base `aed5b4ffe3b8ac2ad030ee383ba7e974de730d5a` and passes `git bundle verify` in the source repository. Either apply the patch on that base with `git am`, or fetch the bundled `refs/heads/fill/ch34-b2b` into a review branch. After unpacking, run `sha256sum -c SHA256SUMS` at the archive root.

To re-run the Lean evidence after integrating the patch, populate the pinned mathlib cache, bootstrap the reference order using `scripts/lean_check_tree.sh`, and use the same script on the four modules listed in the final sweep. Copy `evidence/ProofAxioms.lean` and `evidence/B2bProbe.lean` into `.lake/b2b-probes/`, then run the check script on `.lake/b2b-probes/ProofAxioms` and `.lake/b2b-probes/B2bProbe` (with the probe's two extra dependencies first). This checkpoint is for continuation, not for claiming the two admissions are eliminated.

**Before-screen output (verbatim).**

```text
declarations screened: 784; copy pairs (target reproduces >= half of source): 626; reproduced text: 173,944 chars
   Catalog.lean::f2_timed_branch_run  reproduces  Wrappers.lean::timed_branch_run: 1051/1051 = 100%
   Catalog.lean::f2_timedCondTM  reproduces  Wrappers.lean::timedCondTM: 802/802 = 100%
   Catalog.lean::f2_timed_control_init  reproduces  Wrappers.lean::timed_control_init: 470/470 = 100%
   Simulation.lean::timed_rewind  reproduces  EXP.lean::enumCont_rewind: 435/435 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   EXP.lean::enumCont_rewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   EXP.lean::enumCont_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  EXP.lean::enumCont_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::catalog_redirect_loop: 140/140 = 100%
   Catalog.lean::catalog_redirect_loop  reproduces  Wrappers.lean::redirect_loop: 140/140 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Wrappers.lean::timedBranchCfg  reproduces  Catalog.lean::f2_timedBranchCfg: 92/92 = 100%
   Catalog.lean::f2_timedBranchCfg  reproduces  Wrappers.lean::timedBranchCfg: 92/92 = 100%
   Wrappers.lean::timedControlCfg  reproduces  Catalog.lean::f2_timedControlCfg: 89/89 = 100%
   Catalog.lean::f2_timedControlCfg  reproduces  Wrappers.lean::timedControlCfg: 89/89 = 100%
   Wrappers.lean::redirectState  reproduces  Catalog.lean::catalog_redirectState: 78/78 = 100%
   Catalog.lean::catalog_redirectState  reproduces  Wrappers.lean::redirectState: 78/78 = 100%
   EXP.lean::enumCont_undoTM  reproduces  EXP.lean::enumCont_undoEntry: 74/74 = 100%
   MeyerTableau.lean::enumWord_zero  reproduces  EXP.lean::enumWord_zero: 73/73 = 100%
   EXP.lean::enumWord_zero  reproduces  MeyerTableau.lean::enumWord_zero: 73/73 = 100%
   Wrappers.lean::timedPadTM  reproduces  Catalog.lean::f2_timedPadTM: 72/72 = 100%
   Catalog.lean::f2_timedPadTM  reproduces  Wrappers.lean::timedPadTM: 72/72 = 100%
   Catalog.lean::catalog_redirectAction  reproduces  Wrappers.lean::redirectAction: 71/71 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Wrappers.lean::timedCondTM  reproduces  Catalog.lean::f2_timedCondTM: 802/805 = 100%
   Catalog.lean::f2_timedReadyCfg  reproduces  Wrappers.lean::timedReadyCfg: 136/137 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::catalog_redirectCfg  reproduces  Wrappers.lean::redirectCfg: 84/85 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_timed_start  reproduces  Wrappers.lean::timed_start: 1025/1049 = 98%
   Wrappers.lean::timed_control_init  reproduces  Catalog.lean::f2_timed_control_init: 470/482 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Wrappers.lean::timed_branch_run  reproduces  Catalog.lean::f2_timed_branch_run: 1051/1081 = 97%
   Wrappers.lean::timedReadyCfg  reproduces  Catalog.lean::f2_timedReadyCfg: 136/140 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Wrappers.lean::computesFunInTime_cond  reproduces  Catalog.lean::f2_cond_time: 621/641 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Wrappers.lean::timed_start  reproduces  Catalog.lean::f2_timed_start: 1025/1073 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::catalog_redirect_apply  reproduces  Wrappers.lean::redirect_apply: 175/187 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::f2_timed_capture  reproduces  Wrappers.lean::timed_capture: 314/338 = 93%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_timed_read  reproduces  Wrappers.lean::timed_read: 1692/1832 = 92%
   Catalog.lean::f2_cond_time  reproduces  Wrappers.lean::computesFunInTime_cond: 621/673 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  EXP.lean::enumCont_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Wrappers.lean::timed_capture  reproduces  Catalog.lean::f2_timed_capture: 314/347 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Wrappers.lean::redirectCfg  reproduces  Catalog.lean::catalog_redirectCfg: 84/93 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   Wrappers.lean::redirectAction  reproduces  Catalog.lean::catalog_redirectAction: 71/79 = 90%
   Catalog.lean::catalog_redirect_step  reproduces  Wrappers.lean::redirect_step: 826/921 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::catalog_redirect_run  reproduces  Wrappers.lean::redirect_run: 160/180 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_timed_read: 1692/1931 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Wrappers.lean::redirect_apply  reproduces  Catalog.lean::catalog_redirect_apply: 175/203 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/171 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Wrappers.lean::redirect_step  reproduces  Catalog.lean::catalog_redirect_step: 826/1041 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   EXP.lean::enumCont_undo_back  reproduces  EXP.lean::enumCont_undo_write: 542/686 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Wrappers.lean::redirect_run  reproduces  Catalog.lean::catalog_redirect_run: 160/204 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Wrappers.lean::emit_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   Wrappers.lean::capture_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   EXP.lean::a3_nonempty_run  reproduces  Seam.lean::seamRelease_step_right: 103/135 = 76%
   EXP.lean::a3_nonempty_run  reproduces  Seam.lean::seamComp_step_right: 103/135 = 76%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   EXP.lean::enumCont_return_run  reproduces  Catalog.lean::a2_mapSetup_run: 124/163 = 76%
   EXP.lean::enumCont_agree_run  reproduces  Catalog.lean::a2_mapSetup_run: 124/163 = 76%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::a2_mapSetup_run: 124/163 = 76%
   EXP.lean::enumCont_undo_back  reproduces  EXP.lean::enumCont_undo_empty: 584/770 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Wrappers.lean::emit_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/171 = 75%
   Wrappers.lean::capture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/171 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   EXP.lean::enumCont_body_reject  reproduces  EXP.lean::enumCont_body_check: 458/611 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_return_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_log_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_agree_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_absorb  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::a3_nonempty_run  reproduces  Catalog.lean::f2_splitEmbed_run: 140/188 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Clean.lean::cleanTM_run  reproduces  CleanSweep.lean::PB_ccfg: 94/128 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   EXP.lean::enumCont_return_run  reproduces  UniversalStartup.lean::universalCapture_run: 124/169 = 73%
   EXP.lean::enumCont_agree_run  reproduces  UniversalStartup.lean::universalCapture_run: 124/169 = 73%
   EXP.lean::a3_run_guarded  reproduces  UniversalStartup.lean::universalCapture_run: 124/169 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   EXP.lean::a3_nonempty_computes  reproduces  EXP.lean::a3_nonempty_nil: 108/148 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   EXP.lean::enumCont_return_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 124/171 = 73%
   EXP.lean::enumCont_agree_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 124/171 = 73%
   EXP.lean::a3_run_guarded  reproduces  Simulation.lean::bufferedFirstCfg_run: 124/171 = 73%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   EXP.lean::enumCont_return_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 121/168 = 72%
   EXP.lean::enumCont_agree_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 121/168 = 72%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamCompTM_runFrom_left: 121/168 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   Wrappers.lean::emit_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Wrappers.lean::capture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::goR_run: 1095/1548 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   EXP.lean::enumCont_undo_back  reproduces  EXP.lean::enumCont_log_apply: 531/762 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   CleanSweep.lean::back_run  reproduces  CleanSweep.lean::goR_run: 1077/1548 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   MeyerTableau.lean::wstep_some_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 79/114 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   EXP.lean::a3_run_guarded  reproduces  EXP.lean::enumCont_agree_run: 203/294 = 69%
   EXP.lean::enumCont_sparse_append  reproduces  Simulation.lean::bufferTape_append: 218/316 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   EXP.lean::enumCont_pad_words  reproduces  EXP.lean::enumCont_pad_init: 95/138 = 69%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::emit_run: 430/626 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   CleanSweep.lean::goR_run  reproduces  CleanSweep.lean::back_run: 1077/1580 = 68%
   EXP.lean::enumCont_undo_run  reproduces  EXP.lean::enumCont_return_run: 235/345 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   EXP.lean::enumCont_first_anchor  reproduces  EXP.lean::enumCont_halt_transfer: 264/388 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::back_run: 1058/1580 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   EXP.lean::enumCont_log_run  reproduces  Catalog.lean::a2_mapSetup_run: 109/163 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   EXP.lean::enumCont_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   EXP.lean::enumCont_first_halt  reproduces  UniversalStartup.lean::universal_live_before: 79/121 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   EXP.lean::enumCont_log_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 109/168 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   EXP.lean::enumCont_log_run  reproduces  UniversalStartup.lean::universalCapture_run: 109/169 = 64%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   EXP.lean::enumCont_log_apply  reproduces  Catalog.lean::a2_map_move: 233/362 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   EXP.lean::enumCont_log_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 109/171 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   EXP.lean::enumCont_log_words  reproduces  EXP.lean::enumCont_round_seam: 306/482 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   EXP.lean::enumCont_round_seam  reproduces  Catalog.lean::a2_map_move: 228/362 = 63%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamComp_step_left: 136/216 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_cond_ledger  reproduces  Wrappers.lean::timed_start: 655/1049 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   EXP.lean::enumCont_undo_empty  reproduces  EXP.lean::enumCont_undo_write: 425/686 = 62%
   EXP.lean::enumCont_body_reject  reproduces  EXP.lean::enumCont_body_accept: 210/339 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   EXP.lean::enumCont_concat_native  reproduces  EXP.lean::enumCont_concat_candidate: 676/1096 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Wrappers.lean::captureCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 129/212 = 61%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::capture_run: 430/708 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   EXP.lean::enumInc_spec  reproduces  EXP.lean::enumValue_lt: 87/144 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Wrappers.lean::timed_branch_run  reproduces  EXP.lean::a3_nonempty_run: 141/237 = 59%
   Catalog.lean::f2_timed_branch_run  reproduces  EXP.lean::a3_nonempty_run: 141/237 = 59%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::f2_splitCount_run  reproduces  EXP.lean::enumCont_return_run: 205/345 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_splitEmbed_run  reproduces  EXP.lean::a3_nonempty_run: 140/237 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   EXP.lean::enumCont_undo_empty  reproduces  Catalog.lean::a2_map_move: 212/362 = 59%
   EXP.lean::enumCont_undo_back  reproduces  Catalog.lean::a2_map_move: 212/362 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   EXP.lean::enumCont_sparse_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 69/118 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   EXP.lean::enumCont_undo_write  reproduces  Catalog.lean::a2_map_move: 210/362 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  EXP.lean::a3_nonempty_run: 136/237 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Catalog.lean::f2_loopBodyCfg  reproduces  Wrappers.lean::captureCfg: 129/227 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   EXP.lean::enumCont_pad_run  reproduces  EXP.lean::a3_nonempty_run: 134/237 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  EXP.lean::enumCont_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Wrappers.lean::emit_run  reproduces  EXP.lean::enumCont_return_run: 194/345 = 56%
   Wrappers.lean::capture_run  reproduces  EXP.lean::enumCont_return_run: 194/345 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_control_heads: 95/169 = 56%
   EXP.lean::a3_shift_scan  reproduces  Catalog.lean::f2_idTM_run: 434/773 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Simulation.lean::bufferTape_append  reproduces  EXP.lean::enumCont_sparse_append: 218/390 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::f2_idTM_run  reproduces  EXP.lean::a3_shift_scan: 434/782 = 55%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   EXP.lean::enumCont_agree_run  reproduces  EXP.lean::a3_run_guarded: 203/367 = 55%
   EXP.lean::enumCont_undo_write  reproduces  EXP.lean::enumCont_undo_empty: 425/770 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  EXP.lean::enumCont_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   EXP.lean::enumCont_log_run  reproduces  EXP.lean::enumCont_absorb: 103/189 = 54%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   EXP.lean::enumCont_log_apply  reproduces  EXP.lean::enumCont_undo_write: 373/686 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   EXP.lean::enumCont_log_run  reproduces  Wrappers.lean::redirect_loop: 76/140 = 54%
   EXP.lean::enumCont_log_run  reproduces  Catalog.lean::catalog_redirect_loop: 76/140 = 54%
   EXP.lean::enumCont_absorb  reproduces  Wrappers.lean::redirect_loop: 76/140 = 54%
   EXP.lean::enumCont_absorb  reproduces  Catalog.lean::catalog_redirect_loop: 76/140 = 54%
   CleanSweep.lean::cleanTM  reproduces  Clean.lean::simSt: 76/140 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   EXP.lean::enumCont_first_anchor  reproduces  EXP.lean::enumCont_first_halt: 141/260 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   EXP.lean::enumCont_return_run  reproduces  EXP.lean::enumCont_agree_run: 159/294 = 54%
   EXP.lean::enumCont_body_check  reproduces  EXP.lean::enumCont_body_accept: 183/339 = 54%
   EXP.lean::enumCont_agree_run  reproduces  EXP.lean::enumCont_absorb: 102/189 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   MeyerTableau.lean::RW_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   MeyerTableau.lean::RI_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Catalog.lean::f2_splitStep_orbit  reproduces  EXP.lean::enumCont_orbit: 94/175 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_return_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_return_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_agree_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_agree_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   EXP.lean::a3_run_guarded  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Wrappers.lean::capture_run  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   EXP.lean::enumCont_return_run  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   EXP.lean::a3_run_guarded  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   Catalog.lean::f2_splitCount_run  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_splitCount_run  reproduces  EXP.lean::enumCont_agree_run: 156/294 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Wrappers.lean::emit_run  reproduces  EXP.lean::enumCont_absorb: 100/189 = 53%
   Catalog.lean::a2_mapSetup_stationary  reproduces  EXP.lean::enumCont_absorb: 100/189 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   EXP.lean::enumCont_halt_transfer  reproduces  EXP.lean::enumCont_first_anchor: 264/501 = 53%
   MeyerTableau.lean::incFixed_enumWord  reproduces  MeyerTableau.lean::ctrVal_enumWord: 98/186 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   EXP.lean::enumCont_concat_candidate  reproduces  EXP.lean::enumCont_concat_native: 676/1285 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   EXP.lean::enumCont_body_round_guarded  reproduces  EXP.lean::enumCont_body_start_guarded: 248/476 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   EXP.lean::enumCont_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Wrappers.lean::captureCfg  reproduces  Wrappers.lean::emitCfg: 61/119 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Wrappers.lean::emit_run  reproduces  EXP.lean::enumCont_agree_run: 150/294 = 51%
   Wrappers.lean::capture_run  reproduces  EXP.lean::enumCont_agree_run: 150/294 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   EXP.lean::enumCont_round_seam  reproduces  EXP.lean::enumCont_log_words: 306/602 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Wrappers.lean::redirect_loop: 71/140 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   EXP.lean::enumCont_log_words  reproduces  Catalog.lean::a2_map_move: 183/362 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::a2_mapVirtual  reproduces  VirtualInput.lean::vhostCfg: 91/181 = 50%
   EXP.lean::enumCont_log_apply  reproduces  EXP.lean::enumCont_round_seam: 242/482 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
```

**After-screen output (verbatim).**

```text
declarations screened: 817; copy pairs (target reproduces >= half of source): 627; reproduced text: 174,011 chars
   Catalog.lean::f2_timed_branch_run  reproduces  Wrappers.lean::timed_branch_run: 1051/1051 = 100%
   Catalog.lean::f2_timedCondTM  reproduces  Wrappers.lean::timedCondTM: 802/802 = 100%
   Catalog.lean::f2_timed_control_init  reproduces  Wrappers.lean::timed_control_init: 470/470 = 100%
   Simulation.lean::timed_rewind  reproduces  EXP.lean::enumCont_rewind: 435/435 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   EXP.lean::enumCont_rewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   EXP.lean::enumCont_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  EXP.lean::enumCont_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::catalog_redirect_loop: 140/140 = 100%
   Catalog.lean::catalog_redirect_loop  reproduces  Wrappers.lean::redirect_loop: 140/140 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Wrappers.lean::timedBranchCfg  reproduces  Catalog.lean::f2_timedBranchCfg: 92/92 = 100%
   Catalog.lean::f2_timedBranchCfg  reproduces  Wrappers.lean::timedBranchCfg: 92/92 = 100%
   Wrappers.lean::timedControlCfg  reproduces  Catalog.lean::f2_timedControlCfg: 89/89 = 100%
   Catalog.lean::f2_timedControlCfg  reproduces  Wrappers.lean::timedControlCfg: 89/89 = 100%
   Wrappers.lean::redirectState  reproduces  Catalog.lean::catalog_redirectState: 78/78 = 100%
   Catalog.lean::catalog_redirectState  reproduces  Wrappers.lean::redirectState: 78/78 = 100%
   EXP.lean::enumCont_undoTM  reproduces  EXP.lean::enumCont_undoEntry: 74/74 = 100%
   MeyerTableau.lean::enumWord_zero  reproduces  EXP.lean::enumWord_zero: 73/73 = 100%
   EXP.lean::enumWord_zero  reproduces  MeyerTableau.lean::enumWord_zero: 73/73 = 100%
   Wrappers.lean::timedPadTM  reproduces  Catalog.lean::f2_timedPadTM: 72/72 = 100%
   Catalog.lean::f2_timedPadTM  reproduces  Wrappers.lean::timedPadTM: 72/72 = 100%
   Catalog.lean::catalog_redirectAction  reproduces  Wrappers.lean::redirectAction: 71/71 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Wrappers.lean::timedCondTM  reproduces  Catalog.lean::f2_timedCondTM: 802/805 = 100%
   Catalog.lean::f2_timedReadyCfg  reproduces  Wrappers.lean::timedReadyCfg: 136/137 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::catalog_redirectCfg  reproduces  Wrappers.lean::redirectCfg: 84/85 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_timed_start  reproduces  Wrappers.lean::timed_start: 1025/1049 = 98%
   Wrappers.lean::timed_control_init  reproduces  Catalog.lean::f2_timed_control_init: 470/482 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Wrappers.lean::timed_branch_run  reproduces  Catalog.lean::f2_timed_branch_run: 1051/1081 = 97%
   Wrappers.lean::timedReadyCfg  reproduces  Catalog.lean::f2_timedReadyCfg: 136/140 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Wrappers.lean::computesFunInTime_cond  reproduces  Catalog.lean::f2_cond_time: 621/641 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Wrappers.lean::timed_start  reproduces  Catalog.lean::f2_timed_start: 1025/1073 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::catalog_redirect_apply  reproduces  Wrappers.lean::redirect_apply: 175/187 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::f2_timed_capture  reproduces  Wrappers.lean::timed_capture: 314/338 = 93%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_timed_read  reproduces  Wrappers.lean::timed_read: 1692/1832 = 92%
   Catalog.lean::f2_cond_time  reproduces  Wrappers.lean::computesFunInTime_cond: 621/673 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  EXP.lean::enumCont_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Wrappers.lean::timed_capture  reproduces  Catalog.lean::f2_timed_capture: 314/347 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Wrappers.lean::redirectCfg  reproduces  Catalog.lean::catalog_redirectCfg: 84/93 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   Wrappers.lean::redirectAction  reproduces  Catalog.lean::catalog_redirectAction: 71/79 = 90%
   Catalog.lean::catalog_redirect_step  reproduces  Wrappers.lean::redirect_step: 826/921 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::catalog_redirect_run  reproduces  Wrappers.lean::redirect_run: 160/180 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_timed_read: 1692/1931 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Wrappers.lean::redirect_apply  reproduces  Catalog.lean::catalog_redirect_apply: 175/203 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/171 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Wrappers.lean::redirect_step  reproduces  Catalog.lean::catalog_redirect_step: 826/1041 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   EXP.lean::enumCont_undo_back  reproduces  EXP.lean::enumCont_undo_write: 542/686 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Wrappers.lean::redirect_run  reproduces  Catalog.lean::catalog_redirect_run: 160/204 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Wrappers.lean::emit_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   Wrappers.lean::capture_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   EXP.lean::a3_nonempty_run  reproduces  Seam.lean::seamRelease_step_right: 103/135 = 76%
   EXP.lean::a3_nonempty_run  reproduces  Seam.lean::seamComp_step_right: 103/135 = 76%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   EXP.lean::enumCont_return_run  reproduces  Catalog.lean::a2_mapSetup_run: 124/163 = 76%
   EXP.lean::enumCont_agree_run  reproduces  Catalog.lean::a2_mapSetup_run: 124/163 = 76%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::a2_mapSetup_run: 124/163 = 76%
   EXP.lean::enumCont_undo_back  reproduces  EXP.lean::enumCont_undo_empty: 584/770 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Wrappers.lean::emit_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/171 = 75%
   Wrappers.lean::capture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/171 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   EXP.lean::enumCont_body_reject  reproduces  EXP.lean::enumCont_body_check: 458/611 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_return_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_log_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_agree_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::enumCont_absorb  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   EXP.lean::a3_nonempty_run  reproduces  Catalog.lean::f2_splitEmbed_run: 140/188 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Clean.lean::cleanTM_run  reproduces  CleanSweep.lean::PB_ccfg: 94/128 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   EXP.lean::enumCont_return_run  reproduces  UniversalStartup.lean::universalCapture_run: 124/169 = 73%
   EXP.lean::enumCont_agree_run  reproduces  UniversalStartup.lean::universalCapture_run: 124/169 = 73%
   EXP.lean::a3_run_guarded  reproduces  UniversalStartup.lean::universalCapture_run: 124/169 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   EXP.lean::a3_nonempty_computes  reproduces  EXP.lean::a3_nonempty_nil: 108/148 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   EXP.lean::enumCont_return_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 124/171 = 73%
   EXP.lean::enumCont_agree_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 124/171 = 73%
   EXP.lean::a3_run_guarded  reproduces  Simulation.lean::bufferedFirstCfg_run: 124/171 = 73%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   EXP.lean::enumCont_return_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 121/168 = 72%
   EXP.lean::enumCont_agree_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 121/168 = 72%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamCompTM_runFrom_left: 121/168 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   Wrappers.lean::emit_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Wrappers.lean::capture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::goR_run: 1095/1548 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   EXP.lean::enumCont_undo_back  reproduces  EXP.lean::enumCont_log_apply: 531/762 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   CleanSweep.lean::back_run  reproduces  CleanSweep.lean::goR_run: 1077/1548 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   MeyerTableau.lean::wstep_some_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 79/114 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   EXP.lean::a3_run_guarded  reproduces  EXP.lean::enumCont_agree_run: 203/294 = 69%
   EXP.lean::enumCont_sparse_append  reproduces  Simulation.lean::bufferTape_append: 218/316 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   EXP.lean::enumCont_pad_words  reproduces  EXP.lean::enumCont_pad_init: 95/138 = 69%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::emit_run: 430/626 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   CleanSweep.lean::goR_run  reproduces  CleanSweep.lean::back_run: 1077/1580 = 68%
   EXP.lean::enumCont_undo_run  reproduces  EXP.lean::enumCont_return_run: 235/345 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   EXP.lean::enumCont_first_anchor  reproduces  EXP.lean::enumCont_halt_transfer: 264/388 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::back_run: 1058/1580 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   EXP.lean::enumCont_log_run  reproduces  Catalog.lean::a2_mapSetup_run: 109/163 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   EXP.lean::enumCont_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Inclusions.lean::b2b_callEmb  reproduces  Inclusions.lean::b2b_bankEmb: 67/102 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   EXP.lean::enumCont_first_halt  reproduces  UniversalStartup.lean::universal_live_before: 79/121 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   EXP.lean::enumCont_log_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 109/168 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   EXP.lean::enumCont_log_run  reproduces  UniversalStartup.lean::universalCapture_run: 109/169 = 64%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   EXP.lean::enumCont_log_apply  reproduces  Catalog.lean::a2_map_move: 233/362 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   EXP.lean::enumCont_log_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 109/171 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   EXP.lean::enumCont_log_words  reproduces  EXP.lean::enumCont_round_seam: 306/482 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   EXP.lean::enumCont_round_seam  reproduces  Catalog.lean::a2_map_move: 228/362 = 63%
   EXP.lean::a3_run_guarded  reproduces  Seam.lean::seamComp_step_left: 136/216 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_cond_ledger  reproduces  Wrappers.lean::timed_start: 655/1049 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   EXP.lean::enumCont_undo_empty  reproduces  EXP.lean::enumCont_undo_write: 425/686 = 62%
   EXP.lean::enumCont_body_reject  reproduces  EXP.lean::enumCont_body_accept: 210/339 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   EXP.lean::enumCont_concat_native  reproduces  EXP.lean::enumCont_concat_candidate: 676/1096 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Wrappers.lean::captureCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 129/212 = 61%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::capture_run: 430/708 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   EXP.lean::enumInc_spec  reproduces  EXP.lean::enumValue_lt: 87/144 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Wrappers.lean::timed_branch_run  reproduces  EXP.lean::a3_nonempty_run: 141/237 = 59%
   Catalog.lean::f2_timed_branch_run  reproduces  EXP.lean::a3_nonempty_run: 141/237 = 59%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::f2_splitCount_run  reproduces  EXP.lean::enumCont_return_run: 205/345 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_splitEmbed_run  reproduces  EXP.lean::a3_nonempty_run: 140/237 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   EXP.lean::enumCont_undo_empty  reproduces  Catalog.lean::a2_map_move: 212/362 = 59%
   EXP.lean::enumCont_undo_back  reproduces  Catalog.lean::a2_map_move: 212/362 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   EXP.lean::enumCont_sparse_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 69/118 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   EXP.lean::enumCont_undo_write  reproduces  Catalog.lean::a2_map_move: 210/362 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  EXP.lean::a3_nonempty_run: 136/237 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Catalog.lean::f2_loopBodyCfg  reproduces  Wrappers.lean::captureCfg: 129/227 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   EXP.lean::enumCont_pad_run  reproduces  EXP.lean::a3_nonempty_run: 134/237 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  EXP.lean::enumCont_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Wrappers.lean::emit_run  reproduces  EXP.lean::enumCont_return_run: 194/345 = 56%
   Wrappers.lean::capture_run  reproduces  EXP.lean::enumCont_return_run: 194/345 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_control_heads: 95/169 = 56%
   EXP.lean::a3_shift_scan  reproduces  Catalog.lean::f2_idTM_run: 434/773 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Simulation.lean::bufferTape_append  reproduces  EXP.lean::enumCont_sparse_append: 218/390 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::f2_idTM_run  reproduces  EXP.lean::a3_shift_scan: 434/782 = 55%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   EXP.lean::enumCont_agree_run  reproduces  EXP.lean::a3_run_guarded: 203/367 = 55%
   EXP.lean::enumCont_undo_write  reproduces  EXP.lean::enumCont_undo_empty: 425/770 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  EXP.lean::enumCont_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   EXP.lean::enumCont_log_run  reproduces  EXP.lean::enumCont_absorb: 103/189 = 54%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   EXP.lean::enumCont_log_apply  reproduces  EXP.lean::enumCont_undo_write: 373/686 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   EXP.lean::enumCont_log_run  reproduces  Wrappers.lean::redirect_loop: 76/140 = 54%
   EXP.lean::enumCont_log_run  reproduces  Catalog.lean::catalog_redirect_loop: 76/140 = 54%
   EXP.lean::enumCont_absorb  reproduces  Wrappers.lean::redirect_loop: 76/140 = 54%
   EXP.lean::enumCont_absorb  reproduces  Catalog.lean::catalog_redirect_loop: 76/140 = 54%
   CleanSweep.lean::cleanTM  reproduces  Clean.lean::simSt: 76/140 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   EXP.lean::enumCont_first_anchor  reproduces  EXP.lean::enumCont_first_halt: 141/260 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   EXP.lean::enumCont_return_run  reproduces  EXP.lean::enumCont_agree_run: 159/294 = 54%
   EXP.lean::enumCont_body_check  reproduces  EXP.lean::enumCont_body_accept: 183/339 = 54%
   EXP.lean::enumCont_agree_run  reproduces  EXP.lean::enumCont_absorb: 102/189 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   MeyerTableau.lean::RW_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   MeyerTableau.lean::RI_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Catalog.lean::f2_splitStep_orbit  reproduces  EXP.lean::enumCont_orbit: 94/175 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_return_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_return_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_agree_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   EXP.lean::enumCont_agree_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   EXP.lean::a3_run_guarded  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   EXP.lean::a3_run_guarded  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Wrappers.lean::capture_run  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   EXP.lean::enumCont_return_run  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   EXP.lean::a3_run_guarded  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   Catalog.lean::f2_splitCount_run  reproduces  EXP.lean::enumCont_absorb: 101/189 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_splitCount_run  reproduces  EXP.lean::enumCont_agree_run: 156/294 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Wrappers.lean::emit_run  reproduces  EXP.lean::enumCont_absorb: 100/189 = 53%
   Catalog.lean::a2_mapSetup_stationary  reproduces  EXP.lean::enumCont_absorb: 100/189 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   EXP.lean::enumCont_halt_transfer  reproduces  EXP.lean::enumCont_first_anchor: 264/501 = 53%
   MeyerTableau.lean::incFixed_enumWord  reproduces  MeyerTableau.lean::ctrVal_enumWord: 98/186 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   EXP.lean::enumCont_concat_candidate  reproduces  EXP.lean::enumCont_concat_native: 676/1285 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   EXP.lean::enumCont_body_round_guarded  reproduces  EXP.lean::enumCont_body_start_guarded: 248/476 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   EXP.lean::enumCont_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Wrappers.lean::captureCfg  reproduces  Wrappers.lean::emitCfg: 61/119 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Wrappers.lean::emit_run  reproduces  EXP.lean::enumCont_agree_run: 150/294 = 51%
   Wrappers.lean::capture_run  reproduces  EXP.lean::enumCont_agree_run: 150/294 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   EXP.lean::enumCont_round_seam  reproduces  EXP.lean::enumCont_log_words: 306/602 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Wrappers.lean::redirect_loop: 71/140 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   EXP.lean::enumCont_log_words  reproduces  Catalog.lean::a2_map_move: 183/362 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::a2_mapVirtual  reproduces  VirtualInput.lean::vhostCfg: 91/181 = 50%
   EXP.lean::enumCont_log_apply  reproduces  EXP.lean::enumCont_round_seam: 242/482 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
```
