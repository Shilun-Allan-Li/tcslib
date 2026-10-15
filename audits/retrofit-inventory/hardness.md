# Retrofit inventory — `CookLevin/Hardness.lean` (commissioned report, verbatim)

*Maintainer provenance note: produced 2026-10-09 by a commissioned read-only
inventory agent at HEAD `36bb6255`; source-text liveness analysis (comment
stripping, reference graph by token matching, reachability from the public
theorems) — the kernel walker was not run. Feeds plan §4d. The report follows
verbatim.*

---

# Hardness.lean private-declaration inventory and retrofit plan

**File:** `/Users/seyoonr/phd_experiments/tcslib/TCSlib/Complexity/CookLevin/Hardness.lean` (8,904 lines, branch `complexity/arora-barak-ch3-4`, HEAD `36bb6255`). Nothing was modified.

**Method.** I stripped all comments from the source, detected every top-level declaration, and built a reference graph by token-matching against the file's own declaration names. Liveness is reachability from the 5 public theorems. Every private is assigned to exactly one family (the script reported 0 unassigned). I could not build or run the kernel walker, so "dead" here means dead in the source text.

## Headline findings

1. **The file has 553 privates, not ~538.** That is 618 at A5 close minus 65 deleted at E5. By kind: 361 lemma, 186 def, 4 abbrev, 1 structure (`CLFieldCode`), 1 inductive (`CLTemplateKind`).
2. **Under the strict-simplification bar, very little can be replaced today.** Only 5 privates pass now: `clFresh*` via R2, plus `clCompute_comp` via the public composition row. 63 more are R1/R2/catalog-shaped but blocked.
3. **The main blocker is a gap in R1's public API.** `Build/Embed.lean` exports no lemma giving the contents or head of a *selected* tape in `embedEmitCfg` / `embedSilentCfg`. The facts that would provide this, `embedSlot_selected` and `embedSlot_unselected`, are private (Embed.lean:128, :142). The public `embedEmitTM_frame` covers only unselected tapes, and `embedEmitTM_visitedByTapeHead` gives only visited sets.
   - Every frame-identification lemma in Hardness needs those fields. `clSlotCfg` alone occurs 93 times.
   - So no R1 consumer in this file can be proved from the public API.
   - The fix belongs in Embed.lean, not here: add public `embedEmitCfg` (and silent-flavor) field lemmas for selected tapes.
   - No file in TCSlib uses `embed*`, `seam*`, `transferTM`, `copyTM`, `clearTM`, `compareTM` or `incrementTM` yet. Hardness would be the first consumer.
4. **Two library docstrings overclaim what they generalize.**
   - Embed.lean says R1 is the "generic form" of `clBank*`. It is not: `clBankTM` is a *simultaneous product* of l counters (`State := Fin l → Option (Fin 4)`, cost 2W+2 regardless of l). R1 relocates one routine.
   - Catalog.lean says its copy and compare rows promote the `clCopy*` / `clCmp*` shapes. They match in cost only:
     - `clCopyTM` appends `pairEncode w []` (doubled bits plus `01`) at the record head, not at the origin.
     - `clCmpTM` tests a four-word binary cross-sum `a+b = c+d`, not two-word equality.

## 1. Public surface and file structure

**Public declarations (5):**

| Decl | Lines | Role |
|---|---|---|
| `NPHard.polyTimeReducible` | 76–85 | Hardness transfers forward along `≤ₚ` (this is the fifth theorem) |
| `SAT_NPHard` | 8752–8880 | [AB09, Lemma 2.11]; proof is `clA5Reduction hL` |
| `SAT_NPComplete` | 8882–8887 | `⟨SAT_mem_NP, SAT_NPHard⟩` |
| `SAT3_NPHard` | 8889–8896 | `SAT_NPHard.polyTimeReducible SAT_reducible_SAT3` |
| `SAT3_NPComplete` | 8898–8902 | `⟨SAT3_mem_NP, SAT3_NPHard⟩` |

**Phases.** Batch boundaries are confirmed from `audits/ch2-epoch4-agent-reports/batchA*.md` (counts at batch close: 77, 52, 150, 176, 163).

| Phase | Lines | Privates now | Contents |
|---|---|---|---|
| Header, module doc, first public | 1–86 | 0 | |
| A: snapshot encoding and pure layer | 87–605 | 48 | emission algebra 94–180; packing, verifier, budget 182–236; Claim-2.13 templates, product snapshot code, six-family tableau 238–533; cursor orbit and `clEmitter_of_body` 522–605 |
| A2: native preparation, reference simulation of the oblivious verifier | 606–1259 | 38 | NP verifier 609–620; function adapters 622–689; fill 691–751; header 753–790; reference simulator 792–893; dead clock runner 895–918; binary counter 920–1258 |
| A3: trajectory (tracker, recorder, comparator, reader) | 1260–3333 | 133 | bank 1260–1434; tracking 1436–1707; copier 1709–1917; slot relocation 1919–1999; row copier 2001–2216; pure counts 2218–2298; recorder 2299–2772; comparator 2774–3084; fields and reader 3105–3332 |
| A4: packed-records producer | 3334–6262 | 171 | utilities 3334–3378; wipe 3380–3509; fresh 3511–3584; row loader 3586–3815; input copier 3817–3939; prepare 3941–4053; header layout 4055–4159; record host 4161–4289; matcher 4291–4693; last-visit 4695–4783; replay 4785–4883; composition, output, prepared 4884–5063; query 5065–5163; outputs and budgets 5164–5547; search and visit rows 5549–5795; repeat host and size envelopes 5796–6160; packed producer 6162–6261 |
| A5: controller | 6263–6773 | — | halt, pad and stop adapters; cyclic 5-module host; clean contracts and startup |
| A5: output identity | 6775–8339 | (139 for 6263–8339) | word toolkit; stored data, cursor, fuel, round; `clA5Output_of_nativeChunk` 7356; bounded decode; fragment and emit selector; `clA5OutputIdentity` 8333 |
| A5: equisatisfiability | 8340–8750 | 24 | ends with `clA5Reduction` 8740–8750 |
| Public theorems | 8752–8904 | 0 | |

## 2. All 553 privates by role family

Line totals include each declaration's docstring.

**KEEP (Cook–Levin-specific): 260 decls, 3,292 lines**

| Fam | # | Lines | Members / role |
|---|---|---|---|
| A | 10 | 94–180 | `clLastRound`, `clGroups`, `clGroups_length`, `clFragment`, `clFragment_append`, `clChunk`, `clChunks_before`, `clChunks_serialize`, `clGroups_index`, `clGroups_serialize`. Ordered emission algebra. |
| B | 3 | 191, 216, 612 | `clObliviousVerifier`, `clLoop_polyBound`, `clNPVerifier`. Verifier normalization and budget. |
| C | 35 | 184–533 | e.g. `clPack`, `clTemplate*`, `CLFieldCode`, `clFieldCode`, `clSymbol*`, `clBlockEncode`, `clStateSlice`/`clInputSlice`/`clWorkSlice`, `clBlock_*`, `clBlockDecode*`, `CLTemplateKind`, `clPredicate`, `clWire`, `clGroup`, `clInputGroup`, `clWorkGroup`, `clTableauGroups`, `clTableau`, `clTableau_chunks`, `clPrev_spec`, `clCursor_orbit`. Snapshot code, templates, tableau. |
| D | 1 | 543–605 | `clEmitter_of_body`. Already cites public `exists_emitLoopTM`. |
| E | 5 | 625–689 | `clNative_linear`, `clNative_map`, `clNative_pair`, `clNative_append`, `clNative_unary`. Already thin wrappers over catalog rows. |
| G | 2 | 758–790 | `clPrepHeader`, `clPrepHeader_native` |
| H | 3 | 796–893 | `clRefCfg`, `clRefAction`, `clRef_apply`. Virtual-input reference simulation (stage s2). |
| K1 | 9 | 1439–1508 | `clMoves`, `clPositions`, `clMoves_correct`, `clSelect`, `clAdvance`, `clSigned`, `clSigned_advance`, `clAdvance_bound`, `clSigned_eq`. Pure movement arithmetic. |
| P | 13 | 2221–2298, 3088, 3319 | `clElapsed_width`, `clTag`, `clTag_valid`, `clMove_inj`, `clMoves_tag`, `clCounts`, `clCounts_succ`, `clCounts_bound`, `clCounts_positions`, `clRecFields`, `clRecords`, `clCounts_schedule`, `clRecords_length` |
| S1 | 4 | 3105–3129 | `clFields`, `clPair_append`, `clFields_append`, `clRowPrefix_fields`. Field-format specification. |
| AA | 11 | 4057–4159 | `clNative_fields`, `clHeaderTail`, `clHeaderField`, their `_native` lemmas, `clRecWords`, `clHeaderKeep`, `clHeaderLayout`, `clHeaderLayout_native`, `clHeaderLayout_exact`, `clRecordArgument_native` |
| AC2 | 7 | 4294–4693 | `clMatchWords`, `clRows`, `clRows_add`, `clRows_split`, `clRows_records`, `clMatchFlag`, `clMatchFlag_schedule` |
| AD | 8 | 4697–4783 | `clVisitCode`, `clLastCode`, `clLastCode_native` (already cites `stripLast`), `clLastMarker_step`, `clLastIndex`, `clLastIndex_marker`, `clLastIndex_max`, `clLastCode_prev` |
| AH | 22 | 5067–5547 | e.g. `clQueryWords`, `clQueryFlagsTM`, `clQueryFlags_compute`, `clQueryCode_machine`, `clRecordOutputTM`, `clRecordOutput_compute`/`_quadratic`, `clNative_image`, `clRecords_native`, `clCountOutputTM`, `clQuery_budget`. Producer assembly and ledgers. |
| AI | 16 | 5551–5795 | e.g. `clSearchTarget`, `clSearch_native`, `clPrev_native`, `clVisitRow*`, `clNative_cleanCall` (cites `exists_installCallTM`), `clVisitStep*`, `clVisitRows` |
| AK | 5 | 6037–6105 | `clFields_size`, `clVisitCode_size`, `clVisitRow_size`, `clVisitRows_size`, `clVisitState_size` |
| AL | 6 | 6164–6261 | `clProducerHorizon`, `clProducerClock_native`, `clVisitRows_native`, `clPackedRecords`, `clPackedRecords_native`, `clPackedRecords_machine` |
| AP | 11 | 6536–6773 | `CLA5Clean`, `clA5_bridge_bound`, `clA5Clean_install`, `clA5Clean_emit`, `clA5Copy_clean`, `clA5Packed_install`, `clA5Pack`, `clA5Cursor_install`, `clA5Modules`, `clA5Modules_bound`, `clA5Startup` |
| AS | 65 | 7116–8342 | e.g. `clA5Template_native`, `clA5Group_native`, `clA5Stored*`, `clA5Next*`, `clA5Fuel`, `clA5Round`, `clA5Output_of_nativeChunk`, `clA5Tail_*`, `clA5Field_*`, `clA5Count*`, `clA5InputPos*`, `clA5Visit*`, `clA5InputFragment*`, `clA5WorkFragment*`, `clA5GroupAt*`, `clA5Cursor*`, index decls, `clA5WorkChoice*`, `clA5Fragment*`, `clA5Emit*`, `clA5OutputIdentity`. Emission selector and output identity. |
| AT | 24 | 8345–8750 | e.g. `clA5Block`, `clA5Meaning`, `clA5Group_eval`, `clA5Tableau_eval`, `clA5Reconstruct`, `clA5Certificate`, `clA5Run_output`, `clA5NoFalse`, `clA5Decider_accept`, `clA5TraceAssignment`, `clA5Sound`, `clA5Complete`, `clA5Equisat`, `clA5Reduction`. Equisatisfiability. |

**LEAVE (looks like §12 machinery but fails the bar, or has no §12 counterpart): 219 decls, 3,764 lines**

| Fam | # | Lines | Members / why it fails |
|---|---|---|---|
| F | 3 | 693–751 | `clFillTM`, `clFill_run`, `clNative_fill`. No catalog row computes `replicate \|x\| b`. Confirmed LIVE. |
| I | 19 | 921–1258 | e.g. `clCountInc`, `clCountTM`, `clCountTape`, `clCountCfg`, `clCount_carry`, `clCount_rewind`, `clCount_run`, `clCount_idle`, `clCountTape_eq`, `clCount_width`. Different semantics from `incrementTM`: `clCountInc` extends the word on overflow (Nat.bits successor, `clCountInc_bits`), while `incrementTM` is fixed-width and wraps. |
| J | 11 | 1264–1434 | `clBankPart`, `clBankTM`, `clBankCfg`, `clBank_part`, `clBank_step`, `clBank_run`, `clBankStart`, `clBank_component`, `clBank_finish`, `clBank_idle`, `clBank_first`. Parallel product, not R1. Running the counters in sequence would change the 2W+2 ledger that `clTrack_round` and `clRec_cost_bound` depend on. |
| K2 | 6 | 1513–1707 | `clTrackTM`, `clTrackCfg`, `clTrack_source`, `clTrack_frame`, `clTrack_dispatch`, `clTrack_round`. The round loops back to its own anchor. |
| L | 12 | 1711–1917 | `clBuffer_append_bit`, `clTwo`, `clCopyTM`, `clCopyCfg`, `clCopy_write`, `clCopy_pair`, `clCopy_forward`, `clCopy_separator`, `clCopy_rewind`, `clCopy_run`, `clCopy_idle`, `clCopy_first`. Doubled-bit append at the record head, not `copyTM` semantics. |
| O | 10 | 2017–2216 | `clRowTM`, `clRowCfg`, `clRow_frame`, `clRow_field`, `clRowPrefix`, `clRow_prefix_run`, `clRow_stored`, `clRow_idle`, `clRow_first`, `clRowPrefix_length`. Indexed loop over l fields. |
| Q | 15 | 2301–2772 | `clRecState`, `clRecTM`, `clRecCfg`, `clRec_row_frame`, `clRec_row_inactive`, `clRec_copy`, `clRec_tick`, `clRec_stop`, `clRec_track_frame`, `clRec_track_inactive`, `clRec_advance`, `clRec_prefix`, `clRec_complete`, `clRec_prepared`, `clRec_cost_bound`. Five-phase controller with a cycle; seams are non-canonical (record head at its length, clock head at t, virtual-input buffer head at inputPos−1). |
| R | 27 | 2775–3084 | e.g. `clBit`, `clNum`, `clNum_bits`, `clAddColumn`, `clCmpUpdate`, `clCmpOrbit`, `clCmpVerdict`, `clCmpTM`, `clCmpCfg`, `clCmp_forward`, `clCmp_rewind`, `clCmp_run`, `clCmp_first`. Four-word cross-sum test, not equality. |
| S2 | 7 | 3145–3314 | `clReadTM`, `clReadCfg`, `clRead_pair`, `clRead_forward`, `clRead_separator`, `clRead_rewind`, `clRead_run`. Reads at a stream cursor; the catalog's pair rows are function-level only. |
| T | 1 | 3337–3363 | `clFirst`. Generic first-return cut; no public counterpart. |
| W | 11 | 3601–3815 | `clLoadTM`, `clLoadCfg`, `clLoad_frame`, `clLoad_field`, `clLoadWords`, `clLoadWords_step`, `clLoad_split`, `clLoad_prefix`, `clLoad_complete`, `clLoad_idle`, `clLoad_first`. Indexed loop. |
| Y | 7 | 3819–3939 | `clInputTM`, `clInputCfg`, `clInput_forward`, `clInput_backward`, `clInput_run`, `clInput_idle`, `clInput_first`. Copies input to a tape; there is no catalog counterpart (candidate for promotion). |
| AC1 | 14 | 4334–4679 | `clMatchState`, `clMatchTM`, `clMatchCfg`, `clMatch_tick`, `clMatch_stop`, `clMatch_load_frame`, `clMatch_load`, `clMatch_cmp_frame`, `clMatch_commit`, `clMatch_compare`, `clMatch_round`, `clPriorRow`, `clMatch_prefix`, `clMatch_complete`. Cyclic search loop. |
| AE | 6 | 4787–4883, 5364 | `clReplayTM`, `clReplayCfg`, `clReplay_back`, `clReplay_forward`, `clReplay_run`, `clReplay_from`. No counterpart (promotion candidate). |
| AJ | 12 | 5798–6160 | `clRepeatTM`, `clRepeatCfg`, `clRepeat_frame`, `clRepeat_call`, `clRepeat_round`, `clRepeat_complete`, `clRepeatWords`, `clRepeat_initial`, `clRepeatOutputTM`, `clRepeatOutput_compute`, `clRepeat_budget`, `clRepeatArgument_native`. The iteration count N(x) depends on the data; `exists_loopTM` / `exists_loopFindTM` need binary fuel R(\|x\|) that depends only on input length. |
| AN | 7 | 6271–6560 | `clA5_call_first_halt`, `clA5StopTM`, `clA5StopCfg`, `clA5Stop_step`, `clA5_live_prefix`, `clA5Stop_clean`, `clA5Clean_stop`. Converts a live exit into a halt for the `emit_run` host. `seamReleaseTM` is the analog, but the host has a cycle. |
| AO | 10 | 6339–6635 | `clA5Pad_seam`, `CLA5HostState`, `clA5HostNext`, `clA5HostEntry`, `clA5HostRet`, `clA5HostTM`, `clA5Host_seam`, `clA5Host_call`, `clA5_guard_add`, `clA5Host_clean`. The host cycles 3→4→anchor; R2 has no cycle combinator. |
| AQ | 39 | 6776–8292 | e.g. `clA5_pt_const`, `clA5_pt_cond`, `clA5_pt_eq` (these 3 already wrap catalog rows), `clA5MapTM`, `clA5Map_run`, `clA5_pt_tail`, `clA5_pt_head`, `clA5Iter_native`, `clA5Drop_native`, `clA5Div_native`, `clA5Mod_native`, `clA5Decode*`, `clA5EqNum_native`. Finite transducers and unary arithmetic; no catalog rows exist. |
| AR | 2 | 7430–7527 | `clA5CompareTM`, `clA5Compare_compute`. Halting-verdict wrapper around the cross-sum comparator. |

**REPLACE: passes the bar today (5 decls, 92 lines)**

| Fam | Members | Facility |
|---|---|---|
| V (3513–3584) | `clFreshTM`, `clFresh_run`, `clFresh_idle`, `clFresh_first` | R2 `seamCompTM` + `seamCompTM_run_ofCfg` |
| AF (4887–4901) | `clCompute_comp` | `FinTM.bufferedCompTM_computesInTime` (Composition.lean:355) |

**REPLACE: flagged LEAVE because blocked (63 decls, 854 lines)**

| Fam | # | Lines | Members | Facility |
|---|---|---|---|---|
| M | 7 | 1581, 1926–1999, 2588, 3367 | `clLeft_until`, `clSlotAction`, `clSlotCfg`, `clSlot_apply`, `clSlot_run`, `clSlot_release`, `clMap_run` | R1 |
| N | 27 | 2003–4905 | e.g. `clRowIndex`/`Select`/`_inverse`, `clRecTrack*`, `clRecRow*`, `clRecClockIndex`, `clLeft_ne_right`, `clRight_ne_left`, `clLoadIndex`/`Select`/`_inverse`, `clPrepareIndex`/`Select`, `clRecordSelect`/`Index`/`_inverse`, `clMatchLoad*`, `clMatchCmp*`, `clOneSelect` | R1 `Fin m ↪ Fin k` embeddings |
| AM | 5 | 6289–6336 | `clA5PadAction`, `clA5PadTM`, `clA5PadCfg`, `clA5Pad_apply`, `clA5Pad_run` | R1 `embedEmitTM` |
| U | 8 | 3382–3509 | `clErase_last`, `clWipeTM`, `clWipeCfg`, `clWipe_forward`, `clWipe_backward`, `clWipe_run`, `clWipe_idle`, `clWipe_first` | Catalog `clearTM` |
| Z | 5 | 3949–4053 | `clPrepareTM`, `clPrepare_start`, `clPrepare_complete`, `clPrepare_idle`, `clPrepare_first` | R2 + R1 |
| AB | 4 | 4178–4289 | `clRecordTM`, `clRecordCfg`, `clRecord_prepare_frame`, `clRecord_complete` | R2 + R1 |
| AG | 7 | 4909–5063, 5382 | `clOutputTM`, `clOutput_compute`, `clPreparedTM`, `clPreparedCfg`, `clPrepared_run`, `clPrepared_idle`, `clOutputAt_compute` | R2 + R1 |

**DEAD-CANDIDATE: 6 decls, 118 lines.** Evidence is from the comment-stripped source.

| Decl | Defined | Only references |
|---|---|---|
| `clRefClockTM` | 899 | 916 (inside `clRefClockCfg`) |
| `clRefClockCfg` | 914 | none |
| `clCount_first` | 1151 | 1218 (inside `clRefCount_first`) |
| `clRefCountTM` | 1188 | 1209, 1213, 1219 (inside `clRefCount_first`) |
| `clRefCount_first` | 1205 | none in code; one docstring mention at 1242 (`clCount_width`) |
| `clReadFields` | 3133 | 3137 (its own recursion) |

- These form three closed clusters. Nothing that a public theorem reaches cites any of them.
- E5 kept the first four as "kernel-dead, demoted on textual grounds" (`audits/evidence/ch2-epoch34/e5-dedup-inventory.md:218-223`). The only textual citations are inside the cluster and the docstring.
- `clRefClockCfg` and `clReadFields` appear in neither E5 list. That is a gap in the E5 record; re-run the kernel walker before deleting them.

**Prior guidance, checked against the source:**
- `clFill*` is LIVE. Path: `SAT_NPHard → clA5Reduction → clA5OutputIdentity → clA5Output_of_nativeChunk → clA5Fuel → clPackedRecords_native → clPrepHeader_native → clNative_fill → clFillTM`. `clNative_fill` is also used by `clVisitRow_native`.
- `clCertificateCall` and `clTrack_schedule` were dead at source and are already deleted (E5 inventory lines 154 and 214; zero hits anywhere in TCSlib).
- The "11 generated kernel artifacts" are **absent from Hardness.lean**. Its certified kernel surface is exactly the 5 source publics (`kernel-surface-inventory.md:111-117`), and the file has no `deriving`, `instance` or attributes.
  - The artifacts live in Nondeterminism (`stepWith.eq_1`), EXP (`solveSplitWith.eq_1`) and SAT (`WidthAtMost`/`fallback`/`numVars.eq_1` plus the 7-member `instDecidableEqSatStreamState` family).
  - The inventory implies 8+7 = 15 artifacts before E5 and 5+7 = 12 after, not 11. Worth flagging to whoever owns that count.
- The known "~82 classic-family" prefix count is exactly 82 (clCount 28, clCmp 20, clBank 11, clCopy 10, clRead 8, clSlot 5). By role it is mixed: the `clCount*` prefix includes 5 pure-spec decls, 3 output-assembly decls and 1 dead decl.

## 3. Facility mapping and seam analysis for each REPLACE family

- **V `clFresh*` → R2 (passes).**
  - `clFreshTM` already has `seamCompTM`'s shape, up to unfolding: state `Fin 3 ⊕ clReadTM.State`, dispatch `FinTM.controlAction 0 (some (.inr entry))`, left branch `Action.mapState Sum.inl`.
  - Hardness's `.mapState Sum.inl` / `.mapState Sum.inr` seams match the R2′ `seamCompTM_run_ofCfg` statement exactly. The stream head is displaced, which the general-configuration variant handles.
  - No glue is needed. Saves about 20 lines; `clMap_run` call sites drop from 9 to 7. `clFresh_idle` / `clFresh_first` stay, because `clRead_run` has no first-return cut.
- **AF `clCompute_comp` → composition row (passes).** It is canonical at the function level: `bufferedCompTM_computesInTime` plus `output_length_le` and `mono`. Saves about 15 lines.
- **M / N → R1 (LEAVE).**
  - The seams are fine: R1 frames are general.
  - Blocker 1 is the missing selected-tape field lemmas described above.
  - Blocker 2: all 13 `clSlot_run` sites are *guarded* agreement inside multi-phase or cyclic hosts, while R1's transformers are closed and unguarded. `clMap_run` would have to be re-proved on its own as the glue.
  - Once the Embed API exists: drop the 4 core decls and turn the 27 index/select decls into about 9 embeddings, roughly −160 lines. `clSlot_release` and `clLeft_until` stay; `clLeft_until` is a guarded version of the public `FinTM.leftCfg_run`.
- **AM A5 padding → R1 (LEAVE).** The seams are canonical (`Cfg.ofWords` / `stateWord`), but the glue lemma `clA5Pad_seam` needs selected-tape fields, so it hits the same blocker. With the API: about −40 lines.
- **U wipe → catalog `clearTM` (LEAVE).**
  - The semantics and cost (2\|w\|+2, with a built-in first-return cut) match.
  - The seam is non-canonical: the stream tape's head sits at cursor s, and `clearTM_run` is stated only at `Cfg.ofWords`. Fixing that needs the R1 embedding, which is blocked.
  - The input head p is generic but is always 1 at external call sites (`clLoadCfg x 1`, 3969–4452), so p would have to be specialized to 1.
  - Switching to `SweepPhase` states would change about 40 literal states (`.inl 0`, …) in 3949–5063.
  - With the API: about −90 lines.
- **Z / AB / AG → R2 + R1 (LEAVE).**
  - The gluing matches R2′. The relocated phase does not: clInput onto the last tape, clRecTM, A onto the first A.k tapes, replay onto tape i.
  - Without R1, each relocated phase needs a standalone `clSlotAction` machine, and the endpoint shape changes into `(clSlotCfg … id …).mapState Sum.inr`. That ripples into the consumers of `clPreparedCfg` / `clRecordCfg`, so the net gain is about zero.
  - With the API: about −40 to −60 lines.

**Simplifications outside §12, all strict:**
- `clBuffer_append_bit` (1711, one use at 1757) is `(FinTM.bufferTape_append w b).symm`.
- `clA5_pt_unaryLength` (6896, 10 uses) duplicates `clNative_fill true`.
- `clCountTape` duplicates `FinTM.bufferTape` (that is exactly what `clCountTape_eq` proves).

**Already compliant:** Hardness already cites 13 catalog function rows, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM`, `emit_run` / `emitAction` and `bufferedCompTM`.

## 4. Summary

| Class | Decls | Lines (blocks) |
|---|---|---|
| KEEP | 260 | 3,292 |
| LEAVE | 219 | 3,764 |
| REPLACE, passes now (V R2, AF composition) | 5 | 92 |
| REPLACE, flagged LEAVE (R1 M+N+AM 39; CATALOG U 8; R2 Z+AB+AG 16) | 63 | 854 |
| DEAD | 6 | 118 |
| **Total** | **553** | **8,120** |

**Line impact:**
- Doable now: −9 decls (6 dead, `clCompute_comp`, `clBuffer_append_bit`, `clA5_pt_unaryLength`), about −170 lines.
- Possible only after Embed.lean exports selected-tape lemmas: about −34 more decls, about −300 to −350 more lines.
- Even the best case removes only about 6% of the file.

**Suggested two-batch split.** Run them in order; the public surface (76–85 and 8752–8902) stays byte-identical throughout.

- **Batch 1, lines 1–3818** (A, A2, A3, and A4 up to the end of `clLoad_first`):
  - Delete X (895–918, 1147–1239 cluster, 3131–3143) and fix the `clCount_width` docstring at 1241–1243.
  - Replace `clBuffer_append_bit`.
  - Apply R2 to `clFresh` (3511–3584). Its state type is unchanged, so the downstream literals stay valid.
  - If the Embed API has landed: migrate M, N and U (decls ≤3818) and the 5 `clSlot_run` sites at 2074, 2452, 2636, 3375, 3657. Keep `clSlot_run` alive for batch 2. U's `SweepPhase` ripple reaches 3949–5063, so either update those literals here or defer U to batch 2.
- **Batch 2, lines 3819–8904** (rest of A4, A5, equisatisfiability):
  - Replace `clCompute_comp` (users at 5160, 5314).
  - Rename `clA5_pt_unaryLength` to `clNative_fill true`.
  - If the Embed API has landed: Z/AB/AG, N (decls >3818), AM, and the remaining 8 `clSlot_run` sites (3971, 4271, 4446, 4532, 4962, 5032, 5418, 5881). Then delete the `clSlot` core.

**Prerequisite outside this file:** public selected-tape field lemmas for `embedEmitCfg` / `embedSilentCfg` in `TCSlib/Complexity/TuringMachine/Build/Embed.lean`. Without them, every R1 item in this plan stays LEAVE.
