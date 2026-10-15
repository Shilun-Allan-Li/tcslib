# Retrofit inventory — `Build/Loop.lean` (commissioned report, verbatim)

*Maintainer provenance note: produced 2026-10-09 by a commissioned read-only
inventory agent at HEAD `af3952a3` (file unchanged since earlier that day);
source-text liveness analysis (token matching with comments stripped,
transitive closure from the public declarations) — no kernel walker run.
Feeds plan §4d. The report follows verbatim.*

---

# Retrofit inventory: privates in `TCSlib/Complexity/TuringMachine/Build/Loop.lean`

**Bottom line.** Only two families can be acted on under the strict-simplification bar:
- **8 dead declarations** (about 160 lines).
- **One 3-declaration family (H4).** It re-derives a forwarding lemma the file avoided because it was unproved at the time. That lemma, `Turing.emit_run` in Wrappers, is now proved.

The other 87 declarations whose role matches R1, R2 or the catalog have to be left alone. They all fail on structure:
- the hosts are single, hand-built transition tables (not composites);
- the decision/find loop runs the body again every round, which R2 cannot express;
- the phase boundaries are not `Cfg.ofWords`-shaped.

## How the inventory was built

- Every declaration was taken from the source with a Python regex over `^(private )?(noncomputable )?(def|theorem|lemma|abbrev|structure|inductive|instance) <name>`. Two docstring lines that start with the word "lemma" (5497, 5506) were excluded.
- **Result: 222 declarations = 214 private + 8 public.** `grep -c '^private '` gives 215; the extra hit is the docstring line 2703, not a declaration.
- A partition of the 214 into 33 families was checked by script: every private appears exactly once.
- References were computed by token matching on bodies with comments stripped, then taken transitively from the 8 publics.
- Catalog copies were matched by name (`f2_<name>`, `a2_<name>`) and compared text-for-text after removing the prefix.

## 1. Public declarations and file layout

| # | Line | Public declaration | Role | Privates reached (transitively) |
|---|---|---|---|---|
| 1 | 122 | `Turing.stateWord` | Seam word assignment: state on tape 0, other tapes blank | 0 |
| 2 | 140 | `Turing.loop_run` | Frozen summation lemma (empty-output terminal); nothing in the file uses it | 0 |
| 3 | 2392 | `Turing.FinTM.exists_loopCfgTM` | Configuration-level loop: startup, per-round accept-or-advance segments, halted `[false]` terminal | 85 |
| 4 | 2519 | `exists_loopTM` | Decision loop, budget `c(T+1)(R+2)` (proved via #3 and `loop_halted_run`) | 86 |
| 5 | 2633 | `exists_loopFindTM` | Find loop: first accepting payload, or `[]` | 86 |
| 6 | 5508 | `exists_emitLoopTM` | Emitting loop: concatenation of per-round chunks | 82 |
| 7 | 5645 | `exists_installCallTM` | Clean call, install mode: `Cfg.ofWords` seam to `Cfg.ofWords` seam, first return, `0 < C.k` | 91 |
| 8 | 5691 | `exists_emitCallTM` | Clean call, emit mode: argument kept, `f arg` sent to output | 91 |

The privates form three independent clusters:
- **Core decision/find loop**: 95 privates. #3–#5 use all except the 8 dead ones; #6 shares 54 of them.
- **`emCall*`**: 91 privates, used only by #7 and #8. They use no core privates.
- **`emLoop*`**: 28 privates, used only by #6.

**File layout**
- 1–14: header, imports (Convention, Wrappers, Composition, Mathlib).
- 16–116: module docstring.
- 118–177: `namespace Turing` (`stateWord`, `loop_run`).
- 179–5713: `namespace Turing.FinTM`.
  - 181–322: run/trace utilities.
  - 324–437: debit arithmetic and buffer helpers.
  - 439–563: standalone debit machine (dead).
  - 565–717: stop-at-anchor body wrapper.
  - 719–836: host state and controller (`loopHost`).
  - 838–2187: host phase lemmas.
  - 2188–2359: `loopHost_bound` and `loopHost_contracts`.
  - 2361–2697: publics #3–#5 and the two summation lemmas.
  - 2699–4605: `/-! ### Clean-call phase machinery` (`emCall*`; stray sub-comment at 3356).
  - 4607–5595: `/-! ### Forwarding loop controller` (`emLoop*`) and #6.
  - 5597–5711: publics #7 and #8.

## 2. Private families

Line counts include docstrings. All families have 16 or fewer members, so every member is listed.

### Core loop — 95 privates, lines 181–2614

**F1. Run/trace utilities** — 9 members, 181–322, about 134 lines.
- Members: `loop_live_prefix` 182, `loop_silent_prefix` 193, `loop_first_halt` 207, `loop_orbit_inv` 230, `loop_fuel_width` 240, `loop_input_move_le` 247, `loop_input_run_le` 261, `loop_output_length_le` 277, `loop_rewind_bounded` 294.
- Role: generic run facts — live prefix, first-halt cut, orbit invariant, fuel width, input/output displacement bounds, bounded input rewind.
- **KEEP** (8). `loop_silent_prefix` is **DEAD**.
- Not replaceable: §12 has no lemmas of this kind. `loop_rewind_bounded` already wraps the public `rewind_scan`; `loop_fuel_width` cites the public `output_length_le`.

**F2. Fixed-width debit arithmetic** — 10 members, 324–411, about 79 lines.
- Members: `loopDebit` 326, `loopBorrowPos` 332, `loopBorrowPos_le` 337, `loopDebit_length` 343, `loopValue` 349, `loopValue_bits` 354, `loopDebit_value` 365, `loopDebit_success` 379, `loopDebit_iterate_length` 390, `loopDebit_iterate_value` 400.
- **KEEP.** The catalog has `incFixed`/`incrementTM` (increment) but no decrement.

**F3. Buffer read/write helpers** — 2 members, 413–437.
- Members: `loopBuffer_read` 414, `loopBuffer_write` 422.
- **KEEP.**

**F4. Standalone one-tape debit machine** — 6 members, 439–563, about 125 lines.
- Members: `loopDebitTM` 443, `loopDebitCfg` 459, `loopBorrow_step` 466, `loopBorrow_run` 492, `loopBorrow_rewind` 517, `loopBorrow_correct` 551.
- Its own docstring says it "privately re-derives the counter template".
- **DEAD.** The members refer only to each other. `loopBorrow_correct` has no referrers; its only other mention is the historical docstring at 2205. The host performs the borrow itself in F13.

**F5. Stop-at-anchor body wrapper** — 6 members, 565–717, about 148 lines.
- Members: `loopBodyTM` 569, `loopBodyCfg` 592, `loopBody_stop` 604, `loopBody_step` 622, `loopBody_run` 669, `loopBody_capture` 697.
- Role: a release bit forces one action at the anchor; the next anchor entry halts the body; a one-cell flag tape records "returned to anchor" versus "genuine halt".
- **Role matches R2 (`seamReleaseTM` plus exit dispatch) → LEAVE** (5 members).
- `loopBody_capture` is **DEAD**: no referrers, superseded by `loopHost_body_capture` through `loopBodySource`.

**F6. Host state and controller definitions** — 3 members, 719–836.
- Members: `LoopHostState` 720, `loopControlAction` 739, `loopHost` 763 (14-phase controller).
- **KEEP.**

**F7. Relocation and capture glue (R1-shaped)** — 12 members, about 116 lines.
- Members: `loopFuelSource` 724, `loopBodySource` 732, `loopHost_body_capture` 840, `loopHost_fuel_capture` 854, `loopHost_init` 866, `loopFuelCfg` 1076, `loopFuel_run` 1085, `loopFuel_init` 1098, `loopFuelCaptured` 1368, `loopBodyPadded` 1486, `loopCall` 1496, `loopBodySource_run` 1506.
- Role: move the fuel machine onto the right tape block and the stopped body onto the left block (public `rightAction`/`leftAction`, `rightCfg_run`/`leftCfg_run` from Simulation.lean), with output captured via the public `captureAction`/`capture_run`.
- **Role matches R1 → LEAVE.**

**F7b. Relocated layout versus controller frame identities** — 4 members, about 152 lines.
- Members: `loopFuelCaptured_frame` 1387, `loopReady_call` 1562, `loopCall_frame` 1679, `loopCall_reframe` 1706.
- Role: tape-block bookkeeping that matches relocated configurations against `loopFrame`.
- **Role matches R1 (`embedSilentCfg` frame parameters) → LEAVE.**

**F8. Controller frame algebra** — 9 members, about 115 lines.
- Members: `loopControl_idle` 875, `loopFrame` 900, `loopWrite` 920, `loopControl_apply` 927, `loopFrame_payload` 1115, `loopFrame_counter` 1125, `loopFrame_flag` 1881, `loopFlag_clear` 1890, `loopControl_payload` 1019.
- **KEEP.**

**F9. Payload replay (find mode)** — 7 members, about 173 lines.
- Members: `loopReplayTM` 963, `loopReplayCfg` 973, `loopReplay_step` 979, `loopReplay_run` 1003, `loopHost_replay` 1039, `loopHost_payload_rewind` 1973, `loopHost_frame_replay` 2026.
- **KEEP.** No catalog row emits a tape's contents to the output. `loopHost_replay` already relocates with a single `rightCfg_run` citation.

**F10. Fuel setup, phases 0–3 (capture tape to counter)** — 9 members, 1133–1365, about 225 lines.
- Members: `loopHost_fuel_rewind` 1137, `loopCopyTape` 1187, `loopCopy_read` 1191, `loopCopy_erase` 1196, `loopCopy_initial` 1209, `loopCopy_final` 1217, `loopHost_fuel_copy` 1231, `loopHost_fuel_return` 1282, `loopHost_fuel_setup` 1337.
- **Role matches the catalog's `transferTM` → LEAVE.**

**F11. Startup, prepare, release** — 5 members, about 116 lines.
- Members: `loopHost_input_rewind` 883, `loopHost_prepare` 1446, `loopReady` 1375, `loopHost_release` 1601, `loopHost_start` 1632.
- **KEEP.** Borderline: this is a linear chain of phases (R2-shaped), but its boundaries are not canonical, so it would be LEAVE anyway.

**F12. Body-call returns** — 2 members, 1515–1675.
- Members: `loopHost_anchor_return` 1521, `loopHost_halt_return` 1652.
- **Role matches R2 (first-return cut) → LEAVE.**

**F13. In-host borrow and reject** — 5 members, 1736–1967, about 213 lines.
- Members: `loopHost_borrow_step` 1738, `loopHost_borrow_run` 1776, `loopHost_borrow_rewind` 1809, `loopHost_borrow` 1859, `loopHost_reject` 1901.
- **KEEP** (debit logic).

**F14. Accept, round, bound, contracts** — 4 members, 2056–2359, about 302 lines.
- Members: `loopHost_accept` 2061, `loopHost_round` 2127, `loopHost_bound` 2190, `loopHost_contracts` 2214.
- **KEEP.** These are the implementation behind #3–#5.

**F15. Summation** — 2 members.
- Members: `loop_halted_run` 2445 (used by #4), `loop_find_run` 2584 (used by #5).
- **KEEP.** R2 provides no summation over loop rounds.

### Clean call (`emCall*`) — 91 privates, lines 2707–4605

**G1. Captured evaluation on a virtual input** — 6 members, 2707–2835.
- Members: `emCallIdleTM` 2709, `emCallEvalTM` 2717, `emCallEvalCfg` 2730, `emCall_eval_run` 2741, `emCall_eval_initial` 2767, `emCall_eval_first` 2800.
- **KEEP.** The virtual input comes from `bufferedCompTM`'s second phase. Embed.lean's own header puts this out of R1's scope (R1 does not "alter the source input word").

**G2. Marked-interval cleaner** — 12 members, 2837–3067, about 220 lines.
- Members: `emCallInterval` 2839, `emCallCleared` 2844, `emCall_cleared_step` 2848, `emCallClearTM` 2862, `emCallClearCfg` 2881, `emCall_clear_left` 2890, `emCall_cleared_zero` 2939, `emCall_cleared_all` 2946, `emCall_clear_scan` 2958, `emCall_origin_erase` 2985, `emCall_clear_origin` 3000, `emCall_clear_run` 3033.
- **Role matches the catalog's `clearTM` → LEAVE.**

**G3. Visited-interval tracker** — 16 members, 3069–3358, about 275 lines.
- Members: `emCallSpan` 3071, `emCall_span_extend` 3076, `emCallSlots` 3089, `emCallTrackTM` 3096, `emCallTrackCfg` 3118, `emCallTrackMid` 3127, `emCall_track_action` 3137, `emCall_track_stamp` 3174, `emCallLo` 3200, `emCallHi` 3206, `emCall_track_extent` 3213, `emCall_track_support` 3235, `emCall_span_zero` 3263, `emCall_track_initial` 3275, `emCall_track_run` 3302, `emCall_track_computes` 3348.
- **KEEP.** R1's space lemmas are proof-level statements, not marker tapes written by a machine.

**G4. Tracker-to-cleaner bridge and first-entry cut** — 4 members, 3360–3466.
- Members: `emCall_span_interval` 3362, `emCall_track_clearable` 3377, `emCall_first_entry` 3415, `emCall_clear_first` 3439.
- **KEEP.** `seamCompTM` takes a cut as a hypothesis; nothing in §12 produces one.

**G5. Right-boundary normalizer** — 9 members, 3468–3639, about 164 lines.
- Members: `emCallRightTM` 3471, `emCallRightCfg` 3487, `emCall_right_step` 3494, `emCall_right_run` 3507, `emCallRightScan` 3520, `emCall_right_scan` 3529, `emCall_right_finish` 3571, `emCall_right_endpoint` 3601, `emCall_right_computes` 3627.
- **KEEP, borderline.** The `.inl` branch is `embedEmitRetTM` with the identity selection (halt-to-live), followed by an input-head scan. Rebuilding it as R1′ plus `seamCompTM` adds a dispatch step and is a rewrite, not a simplification.

**G6. Prepared-evaluation composite** — 1 member: `emCall_prepared_eval_first` 3651.
- **KEEP.**

**G7. Generic relocation core** — 4 members, 3683–3758, about 73 lines.
- Members: `emCallAction` 3685, `emCallCfg` 3694, `emCall_apply` 3705, `emCall_relocate_run` 3722.
- This is the R1 core in disguise: a partial inverse `select` plays the role of `embedSlot`; `emCall_apply` corresponds to `embedSilent_apply`; `emCall_relocate_run` corresponds to `embedEmitTM_runFrom`, plus a state embedding and a guard.
- **Role matches R1 → LEAVE.**

**G8. Two-tape finalizer** — 8 members, 3760–4040, about 274 lines.
- Members: `emCallFinishTM` 3763, `emCallFinishCfg` 3794, `emCall_erase_last` 3801, `emCall_finish_arg` 3815, `emCall_finish_rewind` 3864, `emCall_finish_transfer` 3903, `emCall_finish_erase` 3953, `emCall_finish_run` 3994.
- **Role matches the catalog's `clearTM`/`transferTM` → LEAVE.**

**G9a. Layout and selection algebra** — 13 members, 4052–4222, about 135 lines.
- Members: `emCallTripleIndex` 4053, `emCallTripleSelect` 4064, `emCall_triple_inverse` 4072, `emCallPairIndex` 4080, `emCallPairSelect` 4085, `emCall_pair_inverse` 4092, `emCallLayout` 4123, `emCall_layout_cases` 4130, `emCall_layout_triple` 4157, `emCall_layout_pair` 4185, `emCall_triple_pair` 4193, `emCall_triple_other` 4203, `emCall_pair_triple` 4217.
- These play the role of R1's `embedSlot_selected`/`embedSlot_unselected`, but those are **private** in Embed.lean, so they could not be cited even in principle.
- **Role matches R1 → LEAVE.**

**G9b. Frame transport identities** — 8 members, 4224–4497, about 183 lines.
- Members: `emCallFrame` 4226, `emCallBankFrame` 4234, `emCall_bank_initial` 4249, `emCall_bank_final` 4287, `emCall_prepare_initial` 4382, `emCall_prepare_final` 4395, `emCall_finish_initial` 4451, `emCall_finish_final` 4478.
- **Role matches R1 → LEAVE.**

**G9c. Controller and phase sequencing** — 10 members, 4042–4605, about 216 lines.
- Members: `emCallSource` 4044, `emCallState` 4049, `emCallTM` 4101, `emCall_bank_step` 4331, `emCall_banks_run` 4362, `emCall_prepare_run` 4422, `emCall_finalize_run` 4501, `emCall_complete` 4532, `emCall_exit_fixed` 4560, `emCall_first` 4581.
- Each phase ends with a silent dispatch (`controlAction 0`), which is `seamCompTM`'s dispatch step.
- **Role matches R2 → LEAVE.** `emCall_exit_fixed`/`emCall_first` supply the public first-return clause and stay regardless.

### Forwarding loop (`emLoop*`) — 28 privates, lines 4609–5466

**H1. Output-prefix commutation** — 2 members: `emLoop_step_prefix` 4611, `emLoop_run_prefix` 4630.
- **KEEP.**

**H2. Forwarding host definition** — 1 member: `emLoopHost` 4643.
- Its body branch uses `emitAction`; every other state falls through to `loopHost.tr`.
- **KEEP.**

**H3. Verbatim re-proofs of `loopHost` phase lemmas** — 14 members, 4657–5181, about 512 lines.
- Members: `emLoopHost_fuel_capture` 4658, `_init` 4670, `_input_rewind` 4680, `_fuel_rewind` 4699, `_fuel_copy` 4754, `_fuel_return` 4805, `_fuel_setup` 4860, `_prepare` 4896, `_release` 4939, `_borrow_step` 4967, `_borrow_run` 5005, `_borrow_rewind` 5038, `_borrow` 5088, `_reject` 5115.
- Scripted diff: 13 are byte-identical to their `loopHost_*` counterparts after renaming `emLoopHost`→`loopHost`. `_init` differs only by one extra simp lemma.
- **KEEP for this retrofit** — no §12 facility removes them. See the out-of-scope notes at the end.

**H4. Local re-derivation of `emit_run`** — 3 members, 5183–5240, about 56 lines.
- Members: `emLoopForwardCfg` 5185, `emLoop_forward_apply` 5192, `emLoop_forward_run` 5210.
- Its docstring (line 5206) says it was "proved locally so this batch does not depend on the concurrent `Turing.emit_run` admission". `Turing.emit_run` (Wrappers.lean:273) is now proved; Wrappers.lean has 0 sorries.
- **REPLACE (actionable).** Borderline on the facility: what replaces it is R1's exported precursor `emit_run` plus Simulation's `leftCfg_run`, not `embedEmitTM` itself. Details in section 3.

**H5. Forwarding call and round** — 7 members, 5242–5419, about 172 lines.
- Members: `emLoopCall` 5244, `emLoopCall_frame` 5255, `emLoopHost_body_forward` 5275, `emLoopHost_anchor_return` 5294, `emLoopCall_empty` 5332, `emLoopHost_start` 5346, `emLoopHost_round` 5370.
- **KEEP.** `emLoopHost_body_forward` becomes a direct `emit_run` citation if H4 is done. `emLoopHost_anchor_return` is a 36-line near-copy of `loopHost_anchor_return` (forward instead of capture).

**H6. Prefix summation** — 1 member: `emLoop_sum` 5427.
- **KEEP.**

### Dead-candidate evidence

`grep -nw` shows the declaration and nothing else for `loop_silent_prefix` (193) and `loopBody_capture` (697). The F4 names appear only inside lines 443–563, plus the docstring mention of `loopBorrow_correct` at 2205. The reachability computation puts all 8 outside the closure of every public declaration.

## 3. What would replace each REPLACE-role family, and why most must stay

Facts that block the replacements, checked against the sources:
- **R1 only describes its own machine.** It has lockstep lemmas for `embedSilentTM`/`embedEmitTM ι M` and the returning forms, but no "any host whose table agrees with the embedded action" lemma (the `hagree` form that `capture_run`/`emit_run` have).
- **The hosts are monolithic.** `loopHost` and `emCallTM` are single hand-built transition tables, not composites.
- **R2 has no way to start inside phase 2.** Every Seam theorem starts from `c₀.mapState Sum.inl`. `exists_loopCfgTM`'s per-round segments start at `cfg i`, inside the looping phase.
- **R2 has no back-edge.** `seamCompTM` is a one-shot sequential composite; the loop re-enters the body every round.
- **Catalog routines are canonical-only.** `transferTM_run`, `clearTM_run` and the rest are stated only from `Cfg.ofWords` with heads at the origin.

| Family | Would-be facility | Boundaries canonical? | Verdict |
|---|---|---|---|
| F7 (12) | R1 `embedSilentTM`/`embedSilentRetTM` | No: fuel residue kept, capture head at word end | LEAVE. Already one- to three-line citations of public Simulation/Wrappers lemmas; citing R1 means redefining `loopHost` as a composite |
| F7b (4) | R1 `embedSilentCfg` frame parameters | No | LEAVE (only pays off after an R1/R2 rebuild of the host) |
| G7 (4), G9a (13), G9b (8) | R1 `embedEmitTM`, `embedSlot` | Internal boundaries are not: data with holes, arbitrary heads | LEAVE. Needs an agreement lemma R1 lacks, a state embedding, and a guard; `embedSlot` is private. **Strongest R1 candidate** if R1 ever exports an agreeing-host lockstep |
| F5 (5), F12 (2) | R2 `seamReleaseTM` plus exit dispatch | — | LEAVE. Release must be re-armed every round by the controller (phases 6 and 9 dispatch to `(anchor, true)`), plus the halt-kind flag tape |
| G9c (10) | R2 `seamCompTM_*_ofCfg` | Outer entry yes; internal boundaries and emit-mode exit (`with output := …`) no | LEAVE. The bank loop runs over `Fin (M.k+1)` inside one state space, while R2 composes exactly two machines |
| F10 (9) | Catalog `transferTM` (3\|w\|+3) | No: capture head starts at \|w\|, arbitrary residue; copies and erases in one forward pass | LEAVE |
| G2 (12) | Catalog `clearTM` (2\|w\|+2) | No: data with holes, cells at negative positions (`lo ≤ 0`), head anywhere, marker tapes | LEAVE |
| G8 (8) | Catalog `clearTM` + `transferTM` | No: both heads enter at the right blanks; emit mode replays to output, which no catalog row does | LEAVE |
| **H4 (3)** | `Turing.emit_run` (Wrappers E2, R1's precursor) + `leftCfg_run` | General configurations — no canonical boundary needed | **REPLACE.** Glue: a padded source `P.tr = leftAction 1 id (loopBodySource.tr …)`; `emitAction ∘ leftAction 1 id = leftAction 1 id ∘ emitAction` (closes by `simp` with `Option.map_id`); one `Cfg.ext` showing `emitCfg ∘ leftCfg = leftCfg ∘ emitCfg`; the liveness guard comes from `leftCfg_run`. About 15–25 lines replacing 56. Needs build confirmation |

## 4. Catalog copies (input for 12.2c — all KEEP here)

- **All 95 core privates (lines 181–2614) have Catalog copies. None of the 91 `emCall*` or 28 `emLoop*` privates do.**
- **94 are copied as `f2_<name>`.** They sit in Catalog.lean roughly between 5571 (`f2_loop_live_prefix`) and 7823 (`f2_loop_find_run`). Examples: `f2_LoopHostState` 6109, `f2_loopHost` 6152, `f2_loopHost_contracts` 7637.
  - 92 are byte-identical after removing the prefix.
  - 2 are strengthened with head-position bounds:
    - `f2_loopHost_prepare` 6835 (↔ `loopHost_prepare` 1446) adds `∀ i, -(T) ≤ c.workTapePos i ≤ T`, proved via `head_steps`.
    - `f2_loopHost_contracts` 7637 (↔ `loopHost_contracts` 2214) adds per-round and terminal head bounds, using `f2_loopCall_heads`.
    - So the Loop originals are weaker special cases of these.
- **1 is copied as `a2_loop_halted_run`** (Catalog 10667 ↔ `loop_halted_run` 2445, identical).
- **Catalog-only analogues with no Loop counterpart:**
  - `f2_loopCall_heads` 7588, `f2_exists_loopFind_space` 7935;
  - `a2_loop_prepare` 10426, `a2_loop_start_prefix` 10510 and `a2_loop_round` 10539 — space-ledger variants of `loopHost_prepare`, `loopHost_start` and `loopHost_round`, built over `f2_loopHost`.
- **The 8 dead declarations were copied too and are dead in Catalog as well.** `f2_loop_silent_prefix` and `f2_loopBody_capture` each occur once; `f2_loopBorrow_correct` occurs twice (the declaration at 5940 and a docstring at 7628). 12.2c can drop them on both sides.

## 5. Summary

| Classification | Count | Families | Estimated line impact in Loop.lean |
|---|---|---|---|
| DEAD-CANDIDATE | 8 | F4 (6), `loop_silent_prefix`, `loopBody_capture` | about −160 (192–200, 439–563, 692–717), plus fixing the docstring sentence at 2205 |
| REPLACE, actionable | 3 | H4 | about −30 to −40 net (56 lines out, 15–25 in); borderline because the facility is `emit_run` |
| REPLACE-R1 role → LEAVE | 41 | F7 12, F7b 4, G7 4, G9a 13, G9b 8 | 0 (about 660 lines; replacing them is a host rebuild) |
| REPLACE-R2 role → LEAVE | 17 | F5 5, F12 2, G9c 10 | 0 |
| REPLACE-CATALOG role → LEAVE | 29 | F10 9, G2 12, G8 8 | 0 |
| KEEP | 116 | F1 8, F2, F3, F6, F8, F9, F11, F13, F14, F15, G1, G3–G6, H1–H3, H5, H6 | 0 |
| **Total** | **214** | | **about −190 to −200 under the strict bar** |

Of the 116 KEEP, 95 are the core loop (all with Catalog copies, see section 4).

## Out of scope, but noticed

- **The largest duplication in the file is internal, not §12.** H3's 14 lemmas (about 512 lines, plus the 36-line near-copy `emLoopHost_anchor_return`) repeat `loopHost`'s phase lemmas, because `emLoopHost` agrees with `loopHost` on every non-body state. A machine-agreement transfer lemma would collapse them. That is a separate decision from this retrofit.
- **Stale status headers.** Embed.lean, Seam.lean and Catalog.lean still say "statement skeleton / all sorried", but `grep -c sorry` returns 0 for all three.
