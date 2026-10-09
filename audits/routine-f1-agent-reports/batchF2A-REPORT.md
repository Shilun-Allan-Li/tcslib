# F2 / Batch A — partial delivery, 17 of 19 targets

**This is not a zero-sorry completion.** It invokes ground rule 7 (continuation budget) of the supplied brief. The first 17 targets in the prescribed risk order are proved and checked. Exactly two original `sorry` bodies remain, and no new private helper is admitted.

## Repository and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required starting branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `ead9abf1cf0d5441da438d22399a9e9b9257fdf5`.
- Working/delivery branch: `fill/s12-f2-A`.
- Delivery commit: `e2cf86eafbb9af925a29963802453e9ead638bbd`.
- Only changed tracked path: `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`.
- No push, PR, rebase, or `lake build` was performed.
- All 72 original source declarations retain their order. All original signatures, docstrings, imports, option headers, and non-target bodies (including all F1 helpers/proofs) are unchanged. The proof bodies of 17 targets and 306 new private source declarations are the only changes.

## Exact remaining frontier

1. `Turing.FinTM.exists_loopTM_spaceUsed` — unchanged original `sorry`, risk-order item 18. The six-step ledger in the brief is still owed. The local copies of the received loop controller and its phase contracts are now available as `f2_loopHost`, `f2_loopHost_body_capture`, `f2_loopHost_prepare`, `f2_loopHost_round`, and their companion declarations. `f2_loopHost_contracts`, `f2_segment_heads`, and `f2_seamed_space` already prove the reusable-seam time-window space argument used by split search. They do **not** constitute a claim that the required `hstartSpace` / `hroundSpace` / `hFspace` ledger has been discharged. Continue by bounding source body positions from the space hypotheses, projecting those positions through each captured call, retaining the fuel bank bound, and combining the fixed-width counter/capture and flag intervals. No multiply-by-round-count space argument is acceptable.
2. `Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed` — unchanged original `sorry`, risk-order item 19, still last. No new forwarding controller has been installed. The named construction obligations remain: validating buffer stage; encoded-prefix emission stage; forwarding payload simulation with both virtual-input boundary clamps, including empty payload; their seam; malformed-input rejection; coefficient-one source-bank trajectory containment; and halted-tail bounds. Do not reuse the refuted captured-output `pairMapTM` witness.

New private helpers remaining `sorry`: **none**. The axiom log prints all 19 targets; exactly the two entries above contain `sorryAx`.

## Verification

- Stock Lean `4.25.0` (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), as pinned in `lean-toolchain`.
- Mathlib pin: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; manifest unchanged.
- Setup used `lake exe cache get` only. The final cache retrieval obtained and decompressed all 7506 requested files.
- Ran the prescribed 65-module order. Its first facade attempt reported the anticipated missing `Build/Embed.olean`. Individually checked `Build/Embed`, `Build/Seam`, `NDCodes`, `Formulas/QBF`, and `Formulas/QBFEncoding`, then resumed from the facade through the final module. All resumed checks passed. Supplemental bootstrap output can contain tool-output truncation markers; the final owned-file/facade evidence is in `final-sweep.log`.
- Final edited-file check: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`, exit 0, fresh `.olean`, **0 error diagnostics and 2 documented sorry warnings**.
- Final facade: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`, exit 0, fresh `.olean`, **0 errors and 0 local sorry warnings**. A facade import does not erase the two documented Catalog admissions.
- All 17 completed target axiom footprints are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Both remaining targets have `sorryAx`, as expected for this partial. See `axioms.log` and `verification/axioms.lean`.
- Statement/body/order freeze audit: PASS; see `verification/owned-file-audit.json`.
- `git diff --check`: PASS.
- Scoped campaign style checker: 0 FAIL, 1 WARN (9404-line file). The supplied brief explicitly forbids splitting this owned file; reopening inaccessible private witnesses and retaining all F1 material accounts for the size. No public helper surface was added.

### Environment note

This execution environment could not resolve the stock binaries' `/proc/<current numeric pid>/exe` lookup. An external `LD_PRELOAD` shim maps only that exact self-process path to `/proc/self/exe`, leaving other calls unchanged. `environment/self_exe.c` is included for reproducibility; it was compiled outside the repository. It does not alter Lean proof terms, the kernel, toolchain sources, or repository files. The Lean checks used the stock pinned binary with this path shim. No `native_decide`, proof axiom, unsafe proof escape, or additional admission was introduced.

## Per-target audit route and proved bound

The quotations below are the matching rows of `audits/routine-infra-findings.md`, “Catalog Part 2: 21/21”. They remain binding together with the later R4/R5 repairs and answer-5 ledger. Bounds below concern the same chosen machine in both conjuncts, at every horizon.

### 1. `computesFunInTime_id_spaceUsed` — PROVED

> **Supported, same witness family.** Identity has linear time and a constant whole-run work-space bound, with the same existential machine in both clauses. The original `idTM` has zero work tapes, hence space exactly zero at all times.

Witness `f2_idTM`; time `n+1`, work space exactly `0` at every horizon. Chosen `c=1`.

### 2. `computesFunInTime_const_spaceUsed` — PROVED

> **Supported, same witness family.** A fixed output word has linear-in-input time allowance and constant work space. The original zero-work-tape finite emission chain satisfies both, with the constant chosen after the fixed word.

Witness `f2_constTM w`; fixed emission chain, time `(w.length+1)(n+1)`, work space exactly `0`.

### 3. `computesFunInTime_prepend_spaceUsed` — PROVED

> **Supported, same witness family.** Prepending the fixed word has linear time and constant whole-run work space. The actual `catalogPrefixTM` has zero work tapes, a stronger property than the sketch's no-work-head-movement claim.

Witness `f2_catalogPrefixTM w`; time `(w.length+1)(n+1)`, work space exactly `0`.

### 4. `computesFunInTime_pairEncodeFixed_spaceUsed` — PROVED

> **Supported, same witness family.** Pairing a fixed first component with the input takes linear time and constant work space. The fixed doubled prefix plus separator is exactly a prepend instance, so zero work tapes suffice.

Prepend the doubled fixed prefix and separator. Both clauses use the same zero-work-tape witness; the prepend constant covers time and space.

### 5. `computesFunInTime_pairValid_spaceUsed` — PROVED

> **Supported, same witness family.** Emit a singleton grammar-validity bit in linear time and constant work space. `pairValidTM` has no work tapes; alignment and the pending bit live in finite control.

Witness `f2_pairValidTM`; time `n+1`, work space exactly `0`, `c=1`.

### 6. `computesFunInTime_pairDup_spaceUsed` — PROVED

> **Supported, same witness family.** Emit `pairEncode x x` in linear time with constant work space. `pairDupTM` rereads the bounded read-only input and has zero work tapes.

Witness `f2_pairDupTM`; time `4(n+1)`, work space exactly `0`, `c=4`.

### 7. `computesFunInTime_incFixed_spaceUsed` — PROVED

> **Supported, same witness family.** Emit the same-width successor, or `[]` on overflow, in linear time and constant work space. This is the original zero-work-tape transducer using input scans and a finite carry flag, not the new in-place work-tape routine.

Witness `f2_incFixedTM`; time `3(n+1)`, work space exactly `0`, `c=3`.

### 8. `computesFunInTime_pairFst_spaceUsed` — PROVED

> **Supported, same witness family.** Emit the decoded first component, or empty output on parse failure, in linear time and linear work space. The actual parser buffers at most half the original input before replay; malformed input may leave a partial buffer but never a larger visited span.

Witness `f2_pairExtractTM true false`; received sharp time `5(n+1)`. All-time visited sets are contained in the stopped prefix, of at most `5(n+1)+1` cells on its one tape. Both stated clauses use `c=6`.

### 9. `computesFunInTime_pairSnd_spaceUsed` — PROVED

> **Supported, same witness family.** Emit the decoded second component, or empty output on parse failure, with the same bounds. The shared `pairExtractTM false true` still buffers the first component and traverses that buffer before copying the suffix; those visits remain linear in input length.

Witness `f2_pairExtractTM false true`; the same sharp-time/visited-prefix argument, including malformed inputs, gives `c=6` for time and linear space.

### 10. `computesFunInTime_pairConcat_spaceUsed` — PROVED

> **Supported, same witness family.** On a valid pair emit the concatenated components, otherwise `[]`, with linear time and work space. `pairExtractTM true true` uses the same bounded prefix buffer, then streams the second component.

Witness `f2_pairExtractTM true true`; the same grammar-validating buffer and stopped-prefix argument gives `c=6`.

### 11. `computesFunInTime_polyUnary_spaceUsed` — PROVED

> **Supported, same witness family.** Unary `C(n+1)^e` is emitted within `c(n+1)^(e+1)` time and `c(n+1)` work space. For positive exponent, the fixed number of loop tapes each holds a side-length `n+1` bank and revisits it; output is uncharged physical output. Exponent zero uses the fixed emission chain.

Exponent zero uses the constant family. For `e=d+1`, the received nested-loop generator uses `d+1` banks. `f2_polyHeads`, `f2_poly_step`, and `f2_poly_space` contain every trajectory in a fixed interval and prove space `5(d+1)(n+1)`; the coefficient `C+10(d+1)+4` covers both clauses.

### 12. `computesFunInTime_polyBits_spaceUsed` — PROVED

> **Supported with the R5 case split.** Binary polynomial value has the old time allowance and work space at most `c(C(n+1)^e+1)`. For positive coefficient and exponent, the unary intermediate, linear loop banks, and binary counter all fit that value bound. A zero coefficient requires the constant-empty family; exponent zero is another fixed-value instance.

R5 is implemented before the buffered route: `C=0` and `e=0` use constant-output machines. For positive `C,e`, compose the received unary generator with the direct counter. The sharper generator time is degree `e`, so the stopped all-time footprint is bounded by a constant times `C(n+1)^e+1`. The frozen degree `e+1` time clause is retained.

### 13. `computesFunInTime_lengthBits_spaceUsed` — PROVED

> **Supported by a direct construction; original witness's sharp space unchecked.** The machine must output binary input length in linear time using `O(Nat.size n+1)` visited cells. A variable-width binary counter can return its head after each carry and advance the input once per increment; the sum of carry lengths is bounded by `∑_{j≥1} floor(n/2^j)≤n`, so total time is linear, and the counter occupies only its bit width plus boundary cells. The attached old proof delegates to `Complexity.timeConstructible_id`; its source is not attached, so that particular witness is not certified here.

Direct variable-width counter `f2_counterTM`, with `c=5`: time `5(n+1)`, space `5(Nat.size n+1)`. The potential identity for carries gives the linear counting budget; `f2_counter_count_space`, `f2_counter_heads`, and `f2_counter_space` include intermediate carries, output, and the stationary tail. No use of the existential sharp witness `timeConstructible_id`.

### 14. `computesFunInTime_pairLenCheck_spaceUsed` — PROVED

> **Supported, same witness family.** Decide the original first-component polynomial length test, rejecting malformed pairs, with time `c(n+1)^(e+1)` and space `c((n+1)^e+n+1)`. The parser/composition banks have linear spans and the captured unary output has length at most `C(n+1)^e`; the fixed coefficient `C` is absorbed in `c`. This bound deliberately keeps the linear term, including `C=0` and `e=0`.

The received `f2_pairCountTM` captures a generator composed with the received first-component extractor. `f2_unary_sharp` and the grammar length bound give actual time `K((n+1)^e+n+1)`; the stopped all-time trajectory therefore fits the stated space envelope. One enlarged coefficient gives the frozen degree `e+1` time clause and space `c((n+1)^e+n+1)`.

### 15. `computesFunInTime_stripLast_spaceUsed` — PROVED

> **Supported, same witness family; R8 corrects its description.** On a valid pair, strip the second component before its last `true` and re-encode the pair; reject if no such marker exists. The guard's extraction/composition uses linear banks, `rawStripTM` buffers the original input once, and the timed conditional keeps these disjoint finite banks; their total span is linear. The quadratic time contract is retained even though the attached construction proves a stronger intermediate bound.

The received raw buffer, guard, composition, and timed-conditional family are assembled in `f2_strip_linear`. Its actual bound is `a(n+1)`, before the original quadratic weakening. `f2_space_of_time` then proves linear all-time space for that same machine. The target uses `c=a+M.k(a+1)`.

### 16. `computesFunInTime_splitSolve_spaceUsed` — PROVED

> **Supported, same witness family at the requested loose bound.** The least valid split, or empty failure, keeps time degree `e+2` while using space degree `e+1`. Each actual source/body segment has time `O((n+1)^(e+1))`, hence at most that many head moves per tape from its origin; canonical round returns confine the union of reused spans to a fixed multiple of that bound. Fuel and the accepted output buffer also fit it, and the result-bearing loop reuses its banks rather than allocating a new bank per candidate.

The received source, prepare/count/restore/emit body, and result-bearing loop are reopened locally. `f2_loopHost_contracts` additionally exposes bounded canonical seams and a bounded exhaustion terminal. `f2_segment_heads` confines all rounds and halted tails to one fixed interval; `f2_seamed_space` includes startup. Instantiation by `f2_splitSolve_of_body` retains time degree `e+2` and space degree `e+1`, with no factor for the number of candidates in space.

### 17. `computesFunInTime_cond_spaceUsed` — PROVED

> **Supported, same witness family.** A conditional retains the old time clause and uses at most `sD(n)+max(s₁(n),s₂(n))+c` work space. The attached timed controller keeps the decider bank, the selected branch bank, and idle branch-origin cells disjoint; only one output bit is captured from the decider. Input rewind is uncharged input-head motion, and no monotonicity is needed because both branches see the same input.

Witness `f2_timedCondTM D M₁ M₂`. `f2_cond_ledger` gives a decider-source prefix and a selected-branch prefix at every host horizon; back/read and rewind only repeat endpoints. `f2_branch_space` counts the unselected origins exactly and `f2_cond_space` charges two capture-head cells. `c=7+M₁.k+M₂.k` covers time and the exact coefficient-one bound `sD(n)+max(s₁(n),s₂(n))+c`.

### 18. `exists_loopTM_spaceUsed` — PENDING

> `Loop:2519` | None: `c(T n+1)(R n+2)` | Add `S,hFspace,hstartSpace,hroundSpace`; `space ≤ c(S n+T n+1)`

No proved export in this partial. Target bound remains `c(S(n)+T(n)+1)` with the inherited time clause; see the exact frontier above.

### 19. `computesFunInTime_pairMapSnd_spaceUsed` — PENDING

> **Supported as an existential target, but not by the documented old witness (R4).** It retains the original linear-plus-`Tg` time and adds `Sg(n)+c(n+1)` space, assuming monotonicity of both budgets and all-time payload space. A controller can first validate and buffer the pair, output the encoded first component, and simulate `Mg` on a buffered second component while forwarding its output. Source work-head trajectories remain unchanged, giving coefficient 1 on `Sg`, and the input buffer/administration costs only `O(n+1)`; this construction must replace the capture-all-output sketch.

No proved controller in this partial. Target bound remains `Sg(n)+c(n+1)` with time `c(n+1+Tg(n))`; see the exact frontier above.

## Proof-route details for audit

`f2_space_of_time` is an actual all-time trajectory proof: every later head position is identified with the halted endpoint, the entire visited image is included in the finite time-prefix image, that image has at most `T+1` positions per tape, and the finite tape sum is taken. It is used only where a sharper received time bound already fits the required space envelope (extractors, positive polynomial bits, length checker, and raw stripping). It does not infer an all-time bound from a final configuration alone. The direct counter, reusable unary banks, split-search seams, and conditional source banks have their separate trajectory invariants.

Private copies of received witnesses consistently use the `f2_` prefix. The transition tables are copied from the received Composition, Primitives, Wrappers, Loop, and explicit direct-counter implementation; they are not replacements commissioned outside the brief. Only local proof interfaces are strengthened where the space evidence needs additional data. The counter copies the explicit implementation and its amortized arithmetic, without using the opaque `timeConstructible_id` existential. The only commissioned new controller is the final forwarding summit, which is explicitly not yet constructed.

R5 is discharged in `computesFunInTime_polyBits_spaceUsed`: the `C=0` and `e=0` branches use the constant-output family before the positive buffered route. The linear administrative term is retained for the length checker, including these boundary cases. R8 is reflected by `f2_strip_linear`; its quadratic public time allowance is merely weakening of the actual linear intermediate.

For split search, the result-bearing loop is needed. `f2_exists_loopFind_space` uses the received finding host and its canonical seams, not the decision-only loop theorem. Completed fuel head positions are bounded at the first halt; all other canonical seam heads are zero. Each actual bounded segment therefore lies in a common interval. Accepted payload capture and replay are included in that segment's proved duration, and the terminal's stationary suffix is explicitly covered. Thus the number of candidates multiplies time but never the space interval.

For W3, `f2_cond_ledger` supplies finite source-prefix indices at every host time. The decider-bank image is contained in its source image up to its time budget, and the selected-branch image in its source image up to the host horizon. `f2_branch_space` adds exactly the idle branch's origin cells. The capture bank visits only positions zero and one, and native input rewind is uncharged.

## Requested shared lemmas

No shared-file change is required to use this partial. Useful future projections, currently private here, are `f2_rewind_heads`, `f2_cond_ledger` / `f2_cond_space`, and the canonical-seam head clauses of `f2_loopHost_contracts`. They are requests for later serial integration only; no source outside the owned file was edited, including the queued Wrappers projection.

## Escalations

None: no frozen statement is claimed unprovable. This is a continuation-budget frontier, not a repaired or weakened specification.

## New private declaration inventory

Every new source declaration is listed below in file order. Compiler-generated constructors, recursors, and derived instance internals inherit the private scope of their listed source declaration. All listed lemmas have checked proofs; none is admitted.

| # | Kind | Name |
|---:|---|---|
| 1 | def | `f2_idTM` |
| 2 | lemma | `f2_idTM_run` |
| 3 | def | `f2_constTM` |
| 4 | def | `f2_catalogPrefixTM` |
| 5 | def | `f2_catalogPrefixCfg` |
| 6 | lemma | `f2_catalogPrefixTM_emit` |
| 7 | lemma | `f2_catalogPrefixTM_copy` |
| 8 | lemma | `f2_catalogPrefixTM_computes` |
| 9 | def | `f2_scanCfg` |
| 10 | lemma | `f2_scanCfg_read` |
| 11 | lemma | `f2_scanCopy_run` |
| 12 | lemma | `f2_scanCopy_finish` |
| 13 | def | `f2_pairDupTM` |
| 14 | lemma | `f2_pairDup_double` |
| 15 | lemma | `f2_pairDup_computes` |
| 16 | lemma | `f2_scanCopy_suffix` |
| 17 | lemma | `f2_scanTrues_run` |
| 18 | lemma | `f2_incFixed_cases` |
| 19 | def | `f2_incFixedTM` |
| 20 | lemma | `f2_incFixed_computes` |
| 21 | lemma | `f2_scanStep_right` |
| 22 | def | `f2_pairValidTM` |
| 23 | lemma | `f2_pairValid_block` |
| 24 | lemma | `f2_pairValid_run` |
| 25 | lemma | `f2_pairValid_computes` |
| 26 | def | `f2_pairExtractTM` |
| 27 | def | `f2_extractCfg` |
| 28 | lemma | `f2_extractCfg_read` |
| 29 | lemma | `f2_extract_first` |
| 30 | lemma | `f2_extract_block` |
| 31 | lemma | `f2_extract_rewind` |
| 32 | lemma | `f2_extract_replay` |
| 33 | lemma | `f2_extract_replay_finish` |
| 34 | lemma | `f2_extract_suffix` |
| 35 | lemma | `f2_extract_finish` |
| 36 | lemma | `f2_extract_run` |
| 37 | lemma | `f2_pairExtract_computes` |
| 38 | inductive | `f2_CatalogPolyControl` |
| 39 | instance | `f2_catalogPolyControlFintype` |
| 40 | instance | `f2_catalogPolyControlDecidableEq` |
| 41 | def | `f2_catalogPolyTape` |
| 42 | def | `f2_catalogPolyMove` |
| 43 | def | `f2_catalogPolyUnaryTM` |
| 44 | def | `f2_catalogPolyCfg` |
| 45 | lemma | `f2_catalogPolyMove_apply` |
| 46 | lemma | `f2_catalogPoly_emit` |
| 47 | lemma | `f2_catalogPoly_rewind` |
| 48 | lemma | `f2_catalogPoly_advance` |
| 49 | def | `f2_catalogPolyCost` |
| 50 | lemma | `f2_catalogPoly_loop` |
| 51 | lemma | `f2_catalogPolyTape_write` |
| 52 | lemma | `f2_catalogPolyCost_le` |
| 53 | def | `f2_catalogPolyCopyCfg` |
| 54 | lemma | `f2_catalogPoly_copy` |
| 55 | lemma | `f2_catalogPoly_setup` |
| 56 | lemma | `f2_catalogPoly_start` |
| 57 | lemma | `f2_catalogPoly_unary_computes` |
| 58 | def | `f2_polyHeads` |
| 59 | lemma | `f2_polyHeads_bounds` |
| 60 | lemma | `f2_poly_step` |
| 61 | lemma | `f2_head_steps` |
| 62 | lemma | `f2_poly_space` |
| 63 | def | `f2_counterInc` |
| 64 | def | `f2_counterCarry` |
| 65 | lemma | `f2_counterInc_potential` |
| 66 | lemma | `f2_counterInc_bits` |
| 67 | lemma | `f2_counterInc_length` |
| 68 | def | `f2_counterBump` |
| 69 | def | `f2_counterTM` |
| 70 | def | `f2_counterTape` |
| 71 | def | `f2_counterCfg` |
| 72 | lemma | `f2_counterTape_read` |
| 73 | lemma | `f2_counterTape_write` |
| 74 | lemma | `f2_counter_carry_step` |
| 75 | lemma | `f2_counter_carry` |
| 76 | lemma | `f2_counter_rewind` |
| 77 | lemma | `f2_counter_start` |
| 78 | lemma | `f2_counter_increment` |
| 79 | lemma | `f2_counter_count` |
| 80 | lemma | `f2_counter_emit_run` |
| 81 | lemma | `f2_counter_emit` |
| 82 | lemma | `f2_counter_computes` |
| 83 | lemma | `f2_counter_count_space` |
| 84 | lemma | `f2_counter_heads` |
| 85 | lemma | `f2_counter_space` |
| 86 | def | `f2_lenAction` |
| 87 | def | `f2_pairCountTM` |
| 88 | def | `f2_lenCfg` |
| 89 | lemma | `f2_lenCfg_read` |
| 90 | lemma | `f2_lenAction_apply` |
| 91 | lemma | `f2_lenSuffix_run` |
| 92 | lemma | `f2_lenParse_first` |
| 93 | lemma | `f2_lenParse_block` |
| 94 | lemma | `f2_lenParse_run` |
| 95 | lemma | `f2_catalogRewind` |
| 96 | lemma | `f2_lenStart` |
| 97 | lemma | `f2_pairCount_computes` |
| 98 | lemma | `f2_catalogPair_inverse` |
| 99 | lemma | `f2_space_of_time` |
| 100 | lemma | `f2_unary_sharp` |
| 101 | lemma | `f2_first_length` |
| 102 | def | `f2_rawStripTM` |
| 103 | def | `f2_stripCfg` |
| 104 | lemma | `f2_catalogBuffer_erase` |
| 105 | lemma | `f2_rawStrip_copy` |
| 106 | lemma | `f2_rawStrip_rewind` |
| 107 | lemma | `f2_rawStrip_replay` |
| 108 | lemma | `f2_rawStrip_finish` |
| 109 | lemma | `f2_rawStrip_erase` |
| 110 | lemma | `f2_rawStrip_trim` |
| 111 | lemma | `f2_rawStrip_computes` |
| 112 | def | `f2_anyTrueTM` |
| 113 | lemma | `f2_anyTrue_run` |
| 114 | lemma | `f2_anyTrue_computes` |
| 115 | lemma | `f2_catalogMarker_cases` |
| 116 | lemma | `f2_strip_linear` |
| 117 | lemma | `f2_loop_live_prefix` |
| 118 | lemma | `f2_loop_silent_prefix` |
| 119 | lemma | `f2_loop_first_halt` |
| 120 | lemma | `f2_loop_orbit_inv` |
| 121 | lemma | `f2_loop_fuel_width` |
| 122 | lemma | `f2_loop_input_move_le` |
| 123 | lemma | `f2_loop_input_run_le` |
| 124 | lemma | `f2_loop_output_length_le` |
| 125 | lemma | `f2_loop_rewind_bounded` |
| 126 | def | `f2_loopDebit` |
| 127 | def | `f2_loopBorrowPos` |
| 128 | lemma | `f2_loopBorrowPos_le` |
| 129 | lemma | `f2_loopDebit_length` |
| 130 | def | `f2_loopValue` |
| 131 | lemma | `f2_loopValue_bits` |
| 132 | lemma | `f2_loopDebit_value` |
| 133 | lemma | `f2_loopDebit_success` |
| 134 | lemma | `f2_loopDebit_iterate_length` |
| 135 | lemma | `f2_loopDebit_iterate_value` |
| 136 | lemma | `f2_loopBuffer_read` |
| 137 | lemma | `f2_loopBuffer_write` |
| 138 | def | `f2_loopDebitTM` |
| 139 | def | `f2_loopDebitCfg` |
| 140 | lemma | `f2_loopBorrow_step` |
| 141 | lemma | `f2_loopBorrow_run` |
| 142 | lemma | `f2_loopBorrow_rewind` |
| 143 | lemma | `f2_loopBorrow_correct` |
| 144 | def | `f2_loopBodyTM` |
| 145 | def | `f2_loopBodyCfg` |
| 146 | lemma | `f2_loopBody_stop` |
| 147 | lemma | `f2_loopBody_step` |
| 148 | lemma | `f2_loopBody_run` |
| 149 | lemma | `f2_loopBody_capture` |
| 150 | abbrev | `f2_LoopHostState` |
| 151 | def | `f2_loopFuelSource` |
| 152 | def | `f2_loopBodySource` |
| 153 | def | `f2_loopControlAction` |
| 154 | def | `f2_loopHost` |
| 155 | lemma | `f2_loopHost_body_capture` |
| 156 | lemma | `f2_loopHost_fuel_capture` |
| 157 | lemma | `f2_loopHost_init` |
| 158 | lemma | `f2_loopControl_idle` |
| 159 | lemma | `f2_loopHost_input_rewind` |
| 160 | def | `f2_loopFrame` |
| 161 | def | `f2_loopWrite` |
| 162 | lemma | `f2_loopControl_apply` |
| 163 | def | `f2_loopReplayTM` |
| 164 | def | `f2_loopReplayCfg` |
| 165 | lemma | `f2_loopReplay_step` |
| 166 | lemma | `f2_loopReplay_run` |
| 167 | lemma | `f2_loopControl_payload` |
| 168 | lemma | `f2_loopHost_replay` |
| 169 | def | `f2_loopFuelCfg` |
| 170 | lemma | `f2_loopFuel_run` |
| 171 | lemma | `f2_loopFuel_init` |
| 172 | lemma | `f2_loopFrame_payload` |
| 173 | lemma | `f2_loopFrame_counter` |
| 174 | lemma | `f2_loopHost_fuel_rewind` |
| 175 | def | `f2_loopCopyTape` |
| 176 | lemma | `f2_loopCopy_read` |
| 177 | lemma | `f2_loopCopy_erase` |
| 178 | lemma | `f2_loopCopy_initial` |
| 179 | lemma | `f2_loopCopy_final` |
| 180 | lemma | `f2_loopHost_fuel_copy` |
| 181 | lemma | `f2_loopHost_fuel_return` |
| 182 | lemma | `f2_loopHost_fuel_setup` |
| 183 | def | `f2_loopFuelCaptured` |
| 184 | def | `f2_loopReady` |
| 185 | lemma | `f2_loopFuelCaptured_frame` |
| 186 | lemma | `f2_loopHost_prepare` |
| 187 | def | `f2_loopBodyPadded` |
| 188 | def | `f2_loopCall` |
| 189 | lemma | `f2_loopBodySource_run` |
| 190 | lemma | `f2_loopHost_anchor_return` |
| 191 | lemma | `f2_loopReady_call` |
| 192 | lemma | `f2_loopHost_release` |
| 193 | lemma | `f2_loopHost_start` |
| 194 | lemma | `f2_loopHost_halt_return` |
| 195 | lemma | `f2_loopCall_frame` |
| 196 | lemma | `f2_loopCall_reframe` |
| 197 | lemma | `f2_loopHost_borrow_step` |
| 198 | lemma | `f2_loopHost_borrow_run` |
| 199 | lemma | `f2_loopHost_borrow_rewind` |
| 200 | lemma | `f2_loopHost_borrow` |
| 201 | lemma | `f2_loopFrame_flag` |
| 202 | lemma | `f2_loopFlag_clear` |
| 203 | lemma | `f2_loopHost_reject` |
| 204 | lemma | `f2_loopHost_payload_rewind` |
| 205 | lemma | `f2_loopHost_frame_replay` |
| 206 | lemma | `f2_loopHost_accept` |
| 207 | lemma | `f2_loopHost_round` |
| 208 | lemma | `f2_loopCall_heads` |
| 209 | def | `f2_loopHost_bound` |
| 210 | lemma | `f2_loopHost_contracts` |
| 211 | lemma | `f2_loop_find_run` |
| 212 | lemma | `f2_segment_heads` |
| 213 | lemma | `f2_space_radius` |
| 214 | lemma | `f2_seamed_space` |
| 215 | lemma | `f2_exists_loopFind_space` |
| 216 | def | `f2_splitStep` |
| 217 | def | `f2_splitAccept` |
| 218 | lemma | `f2_splitStep_inv` |
| 219 | lemma | `f2_splitStep_orbit` |
| 220 | lemma | `f2_catalogFind_congr` |
| 221 | lemma | `f2_splitFind_eq` |
| 222 | lemma | `f2_splitFind_none` |
| 223 | lemma | `f2_splitLoop_result` |
| 224 | lemma | `f2_splitLoop_bound` |
| 225 | def | `f2_splitPos` |
| 226 | lemma | `f2_splitPos_read` |
| 227 | lemma | `f2_splitPos_succ` |
| 228 | def | `f2_splitScratch` |
| 229 | lemma | `f2_splitScratch_erase` |
| 230 | def | `f2_splitRestoreTM` |
| 231 | def | `f2_splitRestoreScan` |
| 232 | lemma | `f2_splitRestore_scan` |
| 233 | def | `f2_splitRestoreClean` |
| 234 | lemma | `f2_splitRestore_append` |
| 235 | lemma | `f2_splitRestore_rewind` |
| 236 | lemma | `f2_splitRestore_run` |
| 237 | def | `f2_splitCountAction` |
| 238 | def | `f2_splitCountCfg` |
| 239 | lemma | `f2_splitCount_over` |
| 240 | lemma | `f2_splitCount_apply` |
| 241 | lemma | `f2_splitCount_run` |
| 242 | lemma | `f2_splitPoly_loop_end` |
| 243 | lemma | `f2_catalogFirstEntry` |
| 244 | lemma | `f2_splitRestore_first` |
| 245 | lemma | `f2_splitCount_accept` |
| 246 | lemma | `f2_splitCount_firstHalt` |
| 247 | def | `f2_splitPrepareTM` |
| 248 | def | `f2_splitPrepareScan` |
| 249 | lemma | `f2_splitPrepare_scan` |
| 250 | def | `f2_splitPrepareReady` |
| 251 | lemma | `f2_splitPrepare_extra` |
| 252 | lemma | `f2_splitPrepare_rewind` |
| 253 | lemma | `f2_splitPrepare_run` |
| 254 | lemma | `f2_splitPrepare_first` |
| 255 | def | `f2_splitSafe` |
| 256 | lemma | `f2_splitSafe_add` |
| 257 | lemma | `f2_splitEmbed_cut` |
| 258 | def | `f2_splitRewindTM` |
| 259 | def | `f2_splitEmitTM` |
| 260 | inductive | `f2_SplitBodyState` |
| 261 | instance | `f2_splitBodyStateFintype` |
| 262 | instance | `f2_splitBodyStateDecidableEq` |
| 263 | def | `f2_splitBodyTM` |
| 264 | def | `f2_splitBank` |
| 265 | lemma | `f2_splitBody_start` |
| 266 | lemma | `f2_splitEmbed_run` |
| 267 | lemma | `f2_splitBody_prepare` |
| 268 | lemma | `f2_splitBody_count` |
| 269 | lemma | `f2_splitBody_rewind` |
| 270 | lemma | `f2_splitBody_restore` |
| 271 | def | `f2_splitEmitCfg` |
| 272 | lemma | `f2_splitEmit_double` |
| 273 | lemma | `f2_splitEmit_separator` |
| 274 | lemma | `f2_splitEmit_suffix` |
| 275 | lemma | `f2_splitEmit_run` |
| 276 | lemma | `f2_splitSafe_one` |
| 277 | lemma | `f2_splitSafe_join` |
| 278 | lemma | `f2_splitBody_round` |
| 279 | lemma | `f2_splitSolve_of_body` |
| 280 | lemma | `f2_splitSource_poly` |
| 281 | lemma | `f2_splitSource_constant` |
| 282 | lemma | `f2_splitBody_envelope` |
| 283 | lemma | `f2_splitSolve_source` |
| 284 | lemma | `f2_splitSolve_closed` |
| 285 | def | `f2_timedPadTM` |
| 286 | def | `f2_timedCondTM` |
| 287 | def | `f2_timedBranchCfg` |
| 288 | def | `f2_timedControlCfg` |
| 289 | lemma | `f2_timed_capture` |
| 290 | lemma | `f2_timed_control_init` |
| 291 | lemma | `f2_timed_branch_run` |
| 292 | def | `f2_timedReadyCfg` |
| 293 | lemma | `f2_timed_read` |
| 294 | lemma | `f2_timed_start` |
| 295 | lemma | `f2_cond_time` |
| 296 | lemma | `f2_rewind_scan_heads` |
| 297 | lemma | `f2_rewind_heads` |
| 298 | def | `f2_finSumEquiv` |
| 299 | lemma | `f2_sum_add` |
| 300 | lemma | `f2_branch_space` |
| 301 | def | `f2_condHeads` |
| 302 | lemma | `f2_control_heads` |
| 303 | lemma | `f2_branch_heads` |
| 304 | lemma | `f2_read_heads` |
| 305 | lemma | `f2_cond_ledger` |
| 306 | lemma | `f2_cond_space` |

## Final sweep tail

```text
PASS TCSlib/Complexity/ClassNP/Transducer
CHECK TCSlib/Complexity/ClassNP/CounterProgPolyTime
PASS TCSlib/Complexity/ClassNP/CounterProgPolyTime
CHECK TCSlib/Complexity/ClassNP/PClosure
PASS TCSlib/Complexity/ClassNP/PClosure
CHECK TCSlib/Complexity/ClassNP/ExpPoly
PASS TCSlib/Complexity/ClassNP/ExpPoly
CHECK TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP

FINAL SUMMARY
Catalog: PASS, exit 0, fresh .olean, 0 errors, 2 documented sorry warnings.
TuringMachine facade: PASS, exit 0, fresh .olean, 0 errors, 0 local sorry warnings.
Remaining bootstrap modules: PASS.
Completed target axiom prints: 17/17 standard triple only; 0 sorryAx.
Unfinished target axiom prints: exactly 2 with sorryAx; this is a partial delivery.
```

## Package contents and application

- `REPORT.md`: this report, explicit remaining frontier, matching audit rows, and complete helper inventory.
- `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`: full modified source.
- `patches/0001-Fill-17-catalog-space-rows-retain-loop-and-forwardin.patch`: format-patch against the recorded base, preserving the agent author.
- `fill-s12-f2-A.bundle`: incremental Git bundle containing branch `fill/s12-f2-A`; it requires the recorded base commit.
- `final-sweep.log`, `axioms.log`, and `verification/`: final evidence and supplemental bootstrap/freeze/style records.
- `environment/self_exe.c`: external execution-environment compatibility shim source.
- `SHA256SUMS`: SHA-256 of every other packaged file, using paths relative to the archive root.

Apply the patch with `git am` from the recorded base, or import the bundle in a repository containing that base. Package verification checks that applying the patch to the base index reconstructs the exact delivery tree and that the bundle is valid. No remote write is part of this delivery.
