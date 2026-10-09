# Retrofit inventory — `Build/Primitives.lean` (commissioned report, verbatim)

*Maintainer provenance note: produced 2026-10-09 by a commissioned read-only
inventory agent at HEAD `af3952a3`; source-text liveness analysis (token
matching with comments stripped, transitive closure from the public
declarations) — no Lean build run. Feeds plan §4d. The report follows
verbatim.*

---

# Retrofit inventory: `Build/Primitives.lean` (all 318 private declarations)

**File:** `/Users/seyoonr/phd_experiments/tcslib/TCSlib/Complexity/TuringMachine/Build/Primitives.lean`. I read it at HEAD `af3952a3`. The file was last changed in `84b79daf`, and its working tree is clean.

**How the inventory was built.** I enumerated every declaration from the source text. There are 336 in total: 318 private and 18 public, with zero `sorry`s (the word "admitted" appears only in comments).
- References between declarations are token matches over the source with comments removed, so a name mentioned only in a docstring does not count as a use.
- Liveness is the transitive closure from the 18 public theorems.
- The 6 private `instance`s have no textual uses. They are still live, because `FinTM` has `[Fintype State]` and `[DecidableEq State]` fields (`TuringMachine/Finite.lean:128-136`).
- Token matching can only overstate liveness, never understate it, so the DEAD set below is sound.
- I did not run a Lean build; this is a source-text analysis.

---

## 0. Main findings (read these first)

1. **The "engine room" premise does not hold at the import level.**
   - `Build/Catalog.lean` does not import Primitives. It imports only `Mathlib.Data.Nat.Size`, `Mathlib.Tactic.DeriveFintype`, `Build.Loop` and `Encoding`.
   - Instead it holds its own copies of these privates, under an `f2_` prefix. `Catalog.lean:1305-1307` says these are "F2 local witness copies from Composition.lean and Build/Primitives.lean", unchanged except for the prefix.
   - **150 Primitives privates have an `f2_` twin in Catalog.** 147 are identical once the prefix, whitespace and comments are ignored. The other 3 (`splitSolve_of_body`, `splitSolve_source`, `splitSolve_closed`) differ only in that the Catalog versions add a space bound.
   - So `pairDupTM`, `pairValidTM`, `pairExtractTM`, `scanCfg` and the rest are the *originals* of code that is now duplicated. Catalog's public rows rest on `f2_pairDupTM` and friends, not on these.
2. **The named R1 target `emitterBank*` is dead code.** It is not referenced by any public theorem. Deleting it is strictly simpler than rewriting it against R1. 62 privates (about 1,227 lines) are dead in total: 59 leftover components from the earlier emitter batch, plus 3 orphan lemmas from the split-search section.
3. **Two clean catalog replacements exist, both at canonical `Cfg.ofWords` seams:**
   - `emitterCompare*` (8 privates) → `Turing.compareTM`
   - `emitterP2Erase*` (6 privates) → `Turing.clearTM`
4. **R1 cannot replace the live `emitterP2*` relocation layer from Embed's public API alone.**
   - Every frame lemma needs to know what the transported configuration holds on the *selected* tapes.
   - Embed exports no lemma about selected tapes: `embedSlot` and `embedSlot_selected` are private (`Embed.lean:124-151`), and the public `embedEmitTM_frame` covers only unselected tapes.
   - The host is also a single product controller, not a standalone `embedEmitTM ι M`.
   - Classification: LEAVE.
5. **R2 cannot replace either body controller.**
   - `seamCompTM` has exactly one exit state and one entry state; no branching combinator exists.
   - Both bodies branch at two points, and each round starts and ends at the same anchor.
   - Classification: LEAVE.
6. **Two exact duplicates of public `Encoding.lean` lemmas** are already within Primitives' imports:
   - `catalogPair_inverse` ≡ `Turing.eq_pairEncode_of_pairDecode` (`Encoding.lean:231`)
   - `catalogPair_length` ≡ `Turing.length_pairEncode` (`Encoding.lean:192`)
   - These are not §12 replacements, but swapping in the public lemma is strictly simpler.

---

## 1. Public surface and file structure

### 1a. The 18 public declarations

All live in `namespace Turing.FinTM` and all have the shape `∃ M c, M.ComputesFunInTime f T`. "Twin" means Catalog has a `_spaceUsed` row whose first part states the identical time contract.

| # | Declaration (line) | Role | Catalog twin |
|---|---|---|---|
| 1 | `computesFunInTime_prepend` (2122) | P3: computes `w ++ x` | yes |
| 2 | `computesFunInTime_lengthBits` (2137) | P4: `Nat.bits` of the input length, via `Complexity.timeConstructible_id` (no privates) | yes |
| 3 | `computesFunInTime_polyUnary` (2159) | P5 unary: `replicate (C(n+1)^e) true` | yes |
| 4 | `computesFunInTime_polyBits` (2183) | P5 binary: built from rows 3 and 2 (no privates) | yes |
| 5 | `computesFunInTime_pairEncodeFixed` (2220) | P6 encoder: a special case of row 1 | yes |
| 6 | `computesFunInTime_pairFst` (2235) | P6 extractor, first component | yes |
| 7 | `computesFunInTime_pairSnd` (2254) | P6 extractor, second component | yes |
| 8 | `computesFunInTime_pairValid` (2271) | P6 validity test | yes |
| 9 | `computesFunInTime_pairConcat` (2287) | P13 | yes |
| 10 | `computesFunInTime_pairDup` (2308) | P14 | yes |
| 11 | `computesFunInTime_pairMapSnd` (2747) | threaded map | yes, but needs extra space hypotheses `hgs`/`hSg` |
| 12 | `computesFunInTime_pairLenCheck` (2783) | P8, threaded form | yes |
| 13 | `computesFunInTime_stripLast` (2844) | marker strip, threaded form | yes |
| 14 | `computesFunInTime_splitSolve` (4393) | P15 split search | yes |
| 15 | `computesFunInTime_incFixed` (4414) | P9 fixed-width increment | yes |
| 16 | `computesFunInTime_splitSolveWith` (7399) | E4′ width-parametric split search | none (space rows deferred, decision 12.3) |
| 17 | `computesFunInTime_unaryToken` (7553) | stream row | none |
| 18 | `computesFunInTime_appendBit` (7622) | stream row | none |

### 1b. Section map

- **L1–121:** imports, module docstring (L67–110 carry a stale "admitted" status), and the batch-P4 closure note. `namespace` opens at L123.
- **L125–982:** P3 prefix, zero-tape scan kit, P14 duplicate, P9 increment, P6 validity, and the shared P6/P13 extractor.
- **L980–1408:** P5 unary polynomial generator.
- **L1409–1757:** P8 length checker (`pairCountTM`) and the input-rewind helper.
- **L1758–2110:** marker-strip machinery, pair-grammar lemmas, payload composition.
- **L2112–2312:** public rows 1–10.
- **L2313–2913:** threaded map (`pairMapTM`), then public rows 11–13.
- **L2914–4418:** split-search body and closure, then public rows 14–15.
- **L4419–5955:** emitter batch P. This holds the E4′ loop bridge and the earlier batch's components, which are now mostly dead.
- **L5956–7409:** emitter P2: relocation layer, phase machines, tape layout, body controller, closure, then public row 16.
- **L7410–7635:** stream machines and public rows 17–18. `end` at L7636.

---

## 2. Private declarations by family

Notation:
- Line ranges include docstrings; "interleaved" means the family is split across the given ranges.
- "Reached by" names the public rows whose proofs depend on the family (abbreviations: pre = prepend, pEF = pairEncodeFixed, sS = splitSolve, sSW = splitSolveWith, and so on).
- **DUP-f2** means a byte-identical `f2_` copy exists in `Catalog.lean`.

### A. Original machines for the catalog rows (the brief's "engine room")

| Family | # | Lines (~) | Role | Reached by | Class |
|---|---|---|---|---|---|
| F01 prefix | 5 | 129–211 (~83) | Emit a fixed word, then copy the input (no work tapes) | pre, pEF, sS (constant source) | KEEP, DUP-f2 |
| F02 scan kit | 7 | 212–268, 371–440, 553–567 | Input-scan configurations and copy/scan invariants (no work tapes) | 11 rows, including the stream rows | KEEP, DUP-f2 |
| F03 pairDup | 3 | 270–370 (~101) | P14 machine | dup | KEEP, DUP-f2 |
| F04 incFixed | 3 | 442–552 (~111) | P9 string-function machine | inc | KEEP, DUP-f2. **Borderline:** Catalog's `incrementTM` increments a tape word in place; it is not an input→output machine, so it cannot replace this |
| F05 pairValid | 4 | 569–663 (~95) | Validity scanner | val | KEEP, DUP-f2 |
| F06 pairExtract | 12 | 664–982 (~319) | Shared buffered parser | fst, snd, cat, map, lenC, strip | KEEP, DUP-f2 (also needed by the non-projectable `pairMapSnd`) |
| F07 polyUnary | 20 | 983–1408 (~426) | P5 nested-loop generator | pU, pB, lenC, sS (`catalogPolyTape` also sSW) | KEEP, DUP-f2 |
| F08 pairLenCheck | 11 | 1409–1757, excluding 1649–1677 (~320) | Capture, rewind, parse, count down | lenC | KEEP, DUP-f2. Already uses the public W1 `captureAction`/`capture_run`; the later phases read input and emit, so R1's `embedSilentRetTM` would not be simpler |
| F09 input rewind | 1 | 1649–1677 | Rewind the input head (built on public `rewind_scan`) | map, lenC, sS, sSW | KEEP, DUP-f2. No catalog routine moves the input head |
| F10 stripLast | 14 | 1758–2061, interleaved (~280) | Copy, trim and replay, plus a true-bit scanner | strip (`catalogBuffer_erase` also sSW) | KEEP, DUP-f2 |
| F11 pair grammar | 4 | 2013–2110, 2658–2664 (~80) | List lemmas and payload composition | map, strip | 2 swap to public Encoding lemmas (finding 6); 2 KEEP (no twin) |
| F12 pairMap | 14 | 2313–2731 (~413) | Threaded-map controller | map | KEEP. No twin (Catalog uses a different `a2_` implementation); not projectable (§3) |
| F13 split orbit | 9 | 2914–3005 (~92) | Candidate step, orbit, `find?` bridge, bounds | sS; 4 members also sSW | KEEP, DUP-f2 (1 member dead) |
| F14 split position/scratch | 5 | 3006–3050 | Saturated input position; partially cleared scratch tape | sS, sSW | KEEP, DUP-f2 |
| F15 split restore | 9 | 3051–3222, 3355–3403 (~222) | Append to candidate, clear all scratch tapes in parallel, rewind; first-entry cut | sS, sSW (P2 advance phase) | KEEP, DUP-f2. **Borderline:** the parallel k-tape clear is fused with the append and the rewind; `clearTM` is single-tape and §12 has no k-fold seam composition |
| F16 split counted simulation | 7 | 3224–3324, 3404–3438 (~137) | Run the source on tapes 1..k; each emitted bit advances the input head instead of printing | sS | **LEAVE (R1-shaped)**: R1 offers only "capture to a tape" or "forward to output", not this emission mode. DUP-f2; 1 member dead |
| F17 `splitPoly_loop_end` | 1 | 3326–3354 | Generator loop endpoint | sS | KEEP, DUP-f2 |
| F18 split prepare | 8 | 3439–3584 (~146) | Write unary length copies to all scratch tapes in parallel | sS | KEEP, DUP-f2 (1 member dead) |
| F19 split glue | 6 | 3585–3652, 3754–3767, 4048–4075 (~106) | Anchor-exclusion traces; state-embedding lockstep and cut | sS; the four `splitSafe*` also sSW | **LEAVE (R2-shaped)**, DUP-f2 |
| F20 split body | 12 | 3654–4206, interleaved (~356) | Multi-phase round controller | sS | KEEP, DUP-f2 (this is where R2 would have to apply; see §4) |
| F21 split emit | 6 | 3667–3686, 3911–4046 (~154) | Emit the native split (doubling and copying, input → output) | sS, sSW | KEEP, DUP-f2 |
| F22 split closure | 6 | 4201–4366 (~166) | Close via the public `exists_loopFindTM` | sS | KEEP; Catalog twins differ only by the added space bound |

Members:
- **F01:** `catalogPrefixTM`, `catalogPrefixCfg`, `catalogPrefixTM_emit`, `catalogPrefixTM_copy`, `catalogPrefixTM_computes`.
- **F02:** `scanCfg`, `scanCfg_read`, `scanCopy_run`, `scanCopy_finish`, `scanCopy_suffix`, `scanTrues_run`, `scanStep_right`.
- **F03:** `pairDupTM`, `pairDup_double`, `pairDup_computes`.
- **F04:** `incFixed_cases`, `incFixedTM`, `incFixed_computes`.
- **F05:** `pairValidTM`, `pairValid_block`, `pairValid_run`, `pairValid_computes`.
- **F06:** `pairExtractTM`, `extractCfg`, `extractCfg_read`, `extract_first`, `extract_block`, `extract_rewind`, `extract_replay`, `extract_replay_finish`, `extract_suffix`, `extract_finish`, `extract_run`, `pairExtract_computes`.
- **F07 (20):** `CatalogPolyControl`, `catalogPolyControlFintype`, `catalogPolyControlDecidableEq`, `catalogPolyTape`, `catalogPolyMove`, `catalogPolyUnaryTM`, `catalogPolyCfg`, `catalogPolyMove_apply`, `catalogPoly_emit`, `catalogPoly_rewind`, `catalogPoly_advance`, `catalogPolyCost`, `catalogPoly_loop`, `catalogPolyTape_write`, `catalogPolyCost_le`, `catalogPolyCopyCfg`, `catalogPoly_copy`, `catalogPoly_setup`, `catalogPoly_start`, `catalogPoly_unary_computes`.
- **F08:** `lenAction`, `pairCountTM`, `lenCfg`, `lenCfg_read`, `lenAction_apply`, `lenSuffix_run`, `lenParse_first`, `lenParse_block`, `lenParse_run`, `lenStart`, `pairCount_computes`.
- **F09:** `catalogRewind`.
- **F10:** `rawStripTM`, `stripCfg`, `catalogBuffer_erase`, `rawStrip_copy`, `rawStrip_rewind`, `rawStrip_replay`, `rawStrip_finish`, `rawStrip_erase`, `rawStrip_trim`, `rawStrip_computes`, `anyTrueTM`, `anyTrue_run`, `anyTrue_computes`, `catalogMarker_cases`.
- **F11:** `catalogPair_inverse` and `catalogPair_length` (swap to public lemmas); `catalogPayload_length` and `catalogPayload_computes` (KEEP; the latter uses the public `bufferedCompTM`, `bufferedComp_start`, `bufferedSecondCfg_run`).
- **F12:** `mapAction`, `pairMapTM`, `mapCfg`, `mapAction_apply`, `mapBuffer_rewind`, `mapStart`, `mapCfg_read`, `mapParse_first`, `mapParse_block`, `mapValidate`, `mapPrefix_replay`, `mapPayload_replay`, `mapPayload_finish`, `pairMap_computes`.
- **F13:** `splitStep`, `splitAccept`, `splitStep_inv`, `splitStep_orbit`, `catalogFind_congr`, `splitFind_eq`, `splitFind_none` (DEAD), `splitLoop_result`, `splitLoop_bound`.
- **F14:** `splitPos`, `splitPos_read`, `splitPos_succ`, `splitScratch`, `splitScratch_erase`.
- **F15:** `splitRestoreTM`, `splitRestoreScan`, `splitRestore_scan`, `splitRestoreClean`, `splitRestore_append`, `splitRestore_rewind`, `splitRestore_run`, `catalogFirstEntry`, `splitRestore_first`.
- **F16:** `splitCountAction`, `splitCountCfg`, `splitCount_over`, `splitCount_apply`, `splitCount_run`, `splitCount_accept`, `splitCount_firstHalt` (DEAD).
- **F17:** `splitPoly_loop_end`.
- **F18:** `splitPrepareTM`, `splitPrepareScan`, `splitPrepare_scan`, `splitPrepareReady`, `splitPrepare_extra`, `splitPrepare_rewind`, `splitPrepare_run`, `splitPrepare_first` (DEAD).
- **F19:** `splitSafe`, `splitSafe_add`, `splitEmbed_cut`, `splitEmbed_run`, `splitSafe_one`, `splitSafe_join`.
- **F20:** `splitRewindTM`, `SplitBodyState`, `splitBodyStateFintype`, `splitBodyStateDecidableEq`, `splitBodyTM`, `splitBank`, `splitBody_start`, `splitBody_prepare`, `splitBody_count`, `splitBody_rewind`, `splitBody_restore`, `splitBody_round`.
- **F21:** `splitEmitTM`, `splitEmitCfg`, `splitEmit_double`, `splitEmit_separator`, `splitEmit_suffix`, `splitEmit_run`.
- **F22:** `splitSolve_of_body`, `splitSource_poly`, `splitSource_constant`, `splitBody_envelope`, `splitSolve_source`, `splitSolve_closed`.

### B. Emitter batch P (L4419–5955)

| Family | # | Lines (~) | Role | Class |
|---|---|---|---|---|
| F23 emitterSplit | 5 | 4441–4549 (~109) | Loop bridge for the width-parametric search, via public `exists_loopFindTM` and `computesFunInTime_lengthBits` | KEEP (sSW) |
| F24a eval | 6 | 4550–4679 (~130) | Captured evaluator built on `bufferedCompTM` | **DEAD** |
| F24b clear | 13 | 4822–5054, 5448–5481 (~266) | Interval cleaner for visited cells | **DEAD** |
| F24c track | 18 | 5054–5390 (~337) | Visited-interval tracker | **DEAD** |
| F24d bank | 11 | 5493–5690 (~198) | Whole-bank simultaneous cleaner | **DEAD** (this is the backlog's named R1 target) |
| F24e right | 9 | 5691–5863 (~173) | Halt-to-live return adapter | **DEAD** |
| F24f eval closers | 2 | 5864–5960 (~74) | Ends of the old evaluation chain | **DEAD** |
| F25a compare | 8 | 4680–4821, 5415–5447 (~175) | Two-tape whole-word comparison, heads restored, verdict kept in control state | **REPLACE-CATALOG** (`Turing.compareTM`) |
| F25b first entry | 1 | 5391–5414 | Cut a run at its least visit to a stopping state | KEEP. In-file generalization of `catalogFirstEntry`; no public §12 equivalent |
| F25c width arithmetic | 3 | 5482–5491, 5906–5928 | `Nat.bits` injectivity, the width equation, the evaluation budget | KEEP (the public `LogProg.bits_injective` lives in SpaceComplexity, outside Primitives' imports) |

Members:
- **F23:** `emitterSplitAccept`, `emitterSplit_find`, `emitterSplit_result`, `emitterSplit_loop_bound`, `emitterSplit_of_body`.
- **F24a:** `emitterIdleTM`, `emitterEvalTM`, `emitterEvalCfg`, `emitter_eval_run`, `emitter_eval_initial`, `emitter_eval_first`.
- **F24b:** `emitterInterval`, `emitterCleared`, `emitter_cleared_step`, `emitterClearTM`, `emitterClearCfg`, `emitter_clear_left`, `emitter_cleared_zero`, `emitter_cleared_all`, `emitter_clear_scan`, `emitter_origin_erase`, `emitter_clear_origin`, `emitter_clear_run`, `emitter_clear_first`.
- **F24c (18):** `emitterSpan`, `emitter_span_extend`, `emitterSlots`, `emitterTrackTM`, `emitterTrackCfg`, `emitterTrackMid`, `emitter_track_action`, `emitter_track_stamp`, `emitterLo`, `emitterHi`, `emitter_track_extent`, `emitter_track_support`, `emitter_span_zero`, `emitter_track_initial`, `emitter_track_run`, `emitter_track_computes`, `emitter_span_interval`, `emitter_track_clearable`.
- **F24d:** `emitterBankSymbols`, `emitterBankPart`, `emitterBankTM`, `emitterBankCfg`, `emitterBank_part`, `emitterBank_step`, `emitterBank_run`, `emitterClear_fixed`, `emitterBank_clear`, `emitterBank_fixed`, `emitterBank_first`.
- **F24e:** `emitterRightTM`, `emitterRightCfg`, `emitter_right_step`, `emitter_right_run`, `emitterRightScan`, `emitter_right_scan`, `emitter_right_finish`, `emitter_right_endpoint`, `emitter_right_computes`.
- **F24f:** `emitter_prepared_eval_first`, `emitter_width_eval_first`.
- **F25a:** `emitter_take_succ_eq`, `emitterCompareTM`, `emitterCompareCfg`, `emitter_compare_nonblank`, `emitter_compare_scan`, `emitter_compare_rewind`, `emitter_compare_run`, `emitter_compare_first`.
- **F25b:** `emitter_first_entry`.
- **F25c:** `emitter_bits_injective`, `emitter_binary_check`, `emitter_width_budget`.

### C. Emitter P2 (L5956–7409) and the stream machines

| Family | # | Lines (~) | Role | Class |
|---|---|---|---|---|
| F26a P2 relocation | 4 | 5961–6037 (~77) | Move an action or configuration onto selected host tapes, map its states, step-by-step lockstep | **LEAVE (R1-shaped)** |
| F26b P2 layout | 24 | 6513–6734 (~222) | Tape layout (candidate, width bank, length bank), tape selections and their inverses, frame identities | **LEAVE (R1-shaped)** |
| F27a P2 erase | 6 | 6038–6150 (~113) | Clear one word on one tape at a canonical seam | **REPLACE-CATALOG** (`Turing.clearTM`) |
| F27b P2 prepare | 8 | 6151–6433 (~276) | Copy the candidate, copy the input suffix, set the past-end flag, rewind | KEEP. The candidate copy (copyTM-like) is interleaved with input motion and the flag, so it cannot be split at canonical seams |
| F28 P2 glue | 6 | 6328–7210, interleaved (~121) | Concatenating phases, dispatch steps, execute-first calls | **LEAVE (R2-shaped)** |
| F29 P2 body | 20 | 6735–7378 (~609) | 11-phase controller, the round theorem, closure (uses the public `exists_installCallTM`) | KEEP (R2 note in §4) |
| F30 stream | 7 | 7410–7612 (~169) | Unary-token and append-bit machines (no work tapes) | KEEP (no catalog row; P16–P18 space rows deferred) |

Members:
- **F26a:** `emitterP2Action`, `emitterP2Cfg`, `emitterP2_apply`, `emitterP2_relocate_run`.
- **F26b (24):** `emitterP2Words`, `emitterP2LeftIndex`, `emitterP2LeftSelect`, `emitterP2RightIndex`, `emitterP2RightSelect`, `emitterP2_left_inverse`, `emitterP2_right_inverse`, `emitterP2_left_frame`, `emitterP2_right_frame`, `emitterP2_words_clean`, `emitterP2OneSelect`, `emitterP2_one_inverse`, `emitterP2_one_frame`, `emitterP2SmallIndex`, `emitterP2SmallSelect`, `emitterP2_small_inverse`, `emitterP2_small_frame`, `emitterP2PairIndex`, `emitterP2PairSelect`, `emitterP2_pair_inverse`, `emitterP2_pair_frame`, `emitterP2_update_left`, `emitterP2_update_right`, `emitterP2_update_candidate`.
- **F27a:** `emitterP2EraseTM`, `emitterP2EraseCfg`, `emitterP2_erase_scan`, `emitterP2_erase_back`, `emitterP2_erase_run`, `emitterP2_erase_first`.
- **F27b:** `emitterP2PrepareTM`, `emitterP2PrepareCfg`, `emitterP2_prepare_candidate`, `emitterP2_prepare_suffix`, `emitterP2_prepare_rewind_candidate`, `emitterP2_prepare_rewind_suffix`, `emitterP2_prepare_run`, `emitterP2_prepare_first`.
- **F28:** `emitterP2_join`, `emitterP2_segment`, `emitterP2_call_segment`, `emitterP2_control`, `emitterP2_after`, `emitterP2_strict_join`.
- **F29 (20):** `EmitterP2State`, `emitterP2StateFintype`, `emitterP2StateDecidableEq`, `emitterP2BodyTM`, `emitterP2_body_start`, `emitterP2_body_prepare`, `emitterP2_body_width`, `emitterP2_body_length`, `emitterP2_body_compare`, `emitterP2_body_erase_left`, `emitterP2_body_erase_right`, `emitterP2_advance_initial`, `emitterP2_stateWord_one`, `emitterP2_body_advance`, `emitterP2_emit_initial`, `emitterP2_body_emit`, `emitterP2_body_test`, `emitterP2_body_finish`, `emitterP2_body_round`, `emitterP2_closed`.
- **F30:** `emitterTokenTM`, `emitterToken_double`, `emitterToken_separator`, `emitterToken_run`, `emitterToken_length`, `emitterAppendTM`, `emitterAppend_run`.

The prefix count matches the brief's "~77": 10 names start with `emitterBank` and 67 with `emitterP2`, plus `EmitterP2State`. By role, though, only the 28 in F26 are relocation code; the rest are phase machines, glue and the body controller.

### Evidence for the DEAD set (62)

These declarations have no references from any other declaration in the file:
- `emitter_eval_initial`, `emitter_clear_first`, `emitterBank_first`, `emitter_width_eval_first`
- `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first`

Every other DEAD member is referenced only from inside the dead set. For example:
- `emitterClearTM` is used only by `emitterClearCfg`, the `emitter_clear_*` lemmas, the `emitterBank*` members and `emitterClear_fixed`.
- `emitterTrackTM` is used only by the `emitter_track_*` lemmas and the two eval closers.
- `emitter_eval_first` is used only by `emitter_prepared_eval_first`.

These are private, so no other file can use them. Mentions elsewhere are docstring-only (`Embed.lean:31,65,187,619`; `CookLevin/Hardness.lean:1262`). This matches `audits/emitter-fill-findings.md:193`: "The predecessor's unused bank helpers remain proved components". The 3 split orphans likely have dead `f2_` twins in Catalog too; I did not check that file's liveness.

---

## 3. What "engine room" means here

The originals the brief names (F01–F10, F13–F22) are KEEP under the brief's rule. But none of them carries weight for the catalog: they are live only because Primitives' own public rows use them. That opens two ways to remove the duplication:

**(a) Project the rows from Catalog now.**
- The first part of each `_spaceUsed` row is statement-identical to Primitives' row for: prepend, polyUnary, pairFst, pairSnd, pairValid, pairConcat, pairDup, pairLenCheck, stripLast, splitSolve and incFixed.
- Each of those 11 proofs becomes a 2–3-line projection from its twin.
- This frees **100 privates (~2,402 lines)**. 47 twins stay live, because `pairMapSnd`, `splitSolveWith` and the stream rows still need them: the scan core, F06, `catalogPolyTape`, `catalogRewind`, `catalogBuffer_erase`, `catalogPair_inverse`, and the split orbit/position/restore/emit/safe pieces.
- It needs `import TCSlib.Complexity.TuringMachine.Build.Catalog` in Primitives. That creates no import cycle, and none of Catalog's public names (`transferTM`, `copyTM`, `clearTM`, `compareTM`, `incrementTM`, `SweepPhase`, `FlagPhase`, `capture_visitedByTapeHead`) is defined anywhere else.
- `pairMapSnd` cannot be projected: Catalog's row needs a space bound for an arbitrary machine, and the only time-to-space lemma (`f2_space_of_time`) is private to Catalog.

**(b) Or wait for the planned per-theme split** and remove the duplication then.

There is also an option independent of Catalog. `computesFunInTime_splitSolve` follows from `computesFunInTime_splitSolveWith` plus `computesFunInTime_polyBits`, because `solveSplitWith (fun i => C*(i+1)^e)` unfolds to `solveSplit C e` by definition (`Convention.lean:125-133`). The only work is the bound `c(n+1)(b(n+2)^(e+1)+n+2) ≤ K(n+1)^(e+2)`. This frees 38 privates (~909 lines): all of F16–F18, F20, F22 and parts of F13. Those 38 are a subset of the 100 in option (a).

---

## 4. The REPLACE-* candidates and their seams

**REPLACE-CATALOG F25a → `Turing.compareTM 2 0 1`. Seam is canonical.**
- Start and end match exactly: `emitterCompareCfg w u v 1 0 true 0` is the configuration `Cfg.ofWords .run ![u,v]` (input head at 1, work heads at 0, empty output), and the endpoint is `Cfg.ofWords (.done (decide (u = v))) ![u,v]`. The only call site uses input position 1 (`emitterP2_body_compare`).
- Cost fits: `compareTM_run` gives `T ≤ 2·min+2 ≤ 2(max+1)`, and its first-return cut `∀ t<T, ∀ v, state ≠ done v` has exactly the shape needed.
- The positivity fact `0 < t` that `_first` provides is thrown away by its caller.
- Glue:
  - change `EmitterP2State.compare` to carry a `FlagPhase` state;
  - update the `emitterP2BodyTM` compare case;
  - restate `emitterP2_pair_frame` with a `Cfg.ofWords` source;
  - update the state literals in body_compare, body_test and body_round.

**REPLACE-CATALOG F27a → `Turing.clearTM 1 0`. Seam is canonical.**
- `emitterP2EraseCfg w u 0 0` already *is* `Cfg.ofWords 0 (fun _ => u)` by definition; `emitterP2_body_erase_left` uses `change` to that form.
- `clearTM_run` gives `T ≤ 2|u|+2`, the cut, and the endpoint `Cfg.ofWords .done (update w 0 [])`. One lemma is needed: on `Fin 1`, updating every entry to `[]` gives the all-`[]` function.
- Glue: `eraseLeft`/`eraseRight` carry a `SweepPhase` state; the two body cases change; two `hframe` lemmas are restated.
- `catalogBuffer_erase` stays live through F10.
- This also removes the stale `emitterP2EraseCfg` docstring already flagged in the backlog.

**R1 candidates.**
- **F26a/F26b (28): LEAVE.** These are what Embed's own docstring calls the generic form of `embedEmitCfg`. But:
  - (i) there is no public lemma for selected tapes, so none of the frame identities used by the 7 body phase lemmas can be re-proved;
  - (ii) the host is a product controller, so a state-embedding lockstep lemma (the job of `emitterP2_relocate_run`/`splitEmbed_run`) is still needed on top of `embedEmitTM_runFrom`;
  - (iii) switching to `Fin m ↪ Fin (k+l+1)` trades the left-inverse proofs for injectivity proofs one for one, so nothing is saved.
  - Point (i) would go away with an additive public lemma in `Embed.lean` (selected-tape projections of `embedEmitCfg`, or an `ofWords` transport lemma). That changes Embed's public surface, not Primitives', so it is your call.
- **F16 (6 live): LEAVE.** Its emission mode is not one R1 offers.
- **F24d: delete, do not port** (dead).

**R2 candidates.**
- **F19 + F28 (12) and the two body controllers F20/F29: LEAVE.**
- `splitBodyTM` branches after its rewind phase (to emit or to restore). Its count and rewind seams are not canonical (the input head is at `splitPos`, and the rewind starts from an arbitrary configuration). Each round starts and ends at the same anchor. Rebuilding it would need `seamCompTM_run_ofCfg` plus `seamReleaseTM` plus a branching combinator that does not exist.
- `emitterP2BodyTM` has canonical seams throughout (`Cfg.ofWords … (emitterP2Words …)`). But it branches twice (at the end of prepare on the `over` flag, and at the end of eraseRight on `ok`), carries the verdict in its state through both erase phases, and runs its execute-first calls inside the product controller. `emitterP2_call_segment` is in fact the case Seam.lean cites as the motivation for `seamReleaseTM`, but that adapter wraps a whole standalone machine, so it is not a drop-in replacement.

**Other borderline cases (all KEEP).**
- `catalogBuffer_erase` duplicates the public `bufferTape_erase_last` (`SpaceComplexity/Machines/FragDec.lean:96`), which is outside Primitives' imports; importing it would invert the layering.
- `emitter_first_entry` is an in-file generalization of `catalogFirstEntry`. Once F25a and F27a are replaced, each has one remaining caller, so they could be merged.
- The comment blocks at L67–110, L4419–4439 and L5956–5959 describe now-dead families and an "admitted" status that no longer holds; they need comment-only edits.

---

## 5. Summary

| Class | Privates | ~Lines (docstring-inclusive) | Notes |
|---|---|---|---|
| DEAD-CANDIDATE | 62 | 1,227 | 59 from the earlier emitter batch (F24a–f), 3 split orphans |
| REPLACE-CATALOG | 14 | 288 removed, about +15–30 glue | `compareTM`, `clearTM`; canonical seams; needs the Catalog import |
| REPLACE (public Encoding lemma, not §12) | 2 | 30 | `eq_pairEncode_of_pairDecode`, `length_pairEncode` |
| REPLACE-R1 | 0 | — | 34 R1-shaped privates are LEAVE (F26: 28; F16: 6) |
| REPLACE-R2 | 0 | — | 12 R2-shaped privates are LEAVE (F19, F28) |
| LEAVE (R-shaped, simplification bar fails) | 46 | 642 (415 R1-shaped + 227 R2-shaped) | — |
| KEEP | 194 | 4,775 | 134 of these have `f2_` twins (DUP-f2); 60 do not |
| **Total** | **318** | **≈6,962 private** | Public declarations ≈547 lines; header ≈122 |

**Estimated impact:**
- **Conservative pass** (DEAD + REPLACE-CATALOG + the two Encoding swaps): −78 privates, about −1,520 lines net. The file goes from 7,636 to about 6,100 lines.
- **Adding option (a)** (project 11 rows from Catalog): a further −100 privates and about −2,370 lines net. That leaves 140 privates in a file of about 3,700 lines.
- **Or, instead of (a)**, the splitSolve-via-splitSolveWith route: −38 privates (~909 lines), with no new import.

All counts and lines are computed from the source text. Line spans include each declaration's docstring; module-note blocks between declarations are attributed to the declaration before them.
