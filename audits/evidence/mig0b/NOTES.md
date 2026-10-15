# MIG-0b statement draft: notes (2026-10-13)

Read-only drafting against the campaign tip checkout `wt-m0b` (Lean 4.25.0, olean tree `oleans-f7`).
No `lake`, no git, no build command and no `.olean` were used or written. Line numbers below are
in `wt-m0b` unless a draft file is named. `D:` means `Contract-mig0b-draft.lean` and `A:` means
`Contract-mig0b-adapters.lean`.

## 1. Files and results

| File | What | Elaboration |
|---|---|---|
| `Contract-mig0b-draft.lean` (2,661 lines) | D:1–1099 is `audits/evidence/mig0/Contract-proposed-r2.lean.txt`, byte for byte (SHA-256 `078669b8a8ad…f7dd978b`, checked in `elaboration.log`). D:1100–2661 is the MIG-0b section. | 0 errors; 1 warning, `sorry` at D:2347 (`Turing.FinTM.exists_alphabetReduction_lockstep`) |
| `Contract-mig0b-adapters.lean` (3,283 lines) | The adapter probe: the same text plus two imports after line 8 (`SymbolLift`, `Build/CounterLoop`), and the adapter section A:2665–3283 | 0 errors; 1 warning, the same `sorry` (A:2349) |
| `layering-core-probe.lean` (1,717 lines) | The layering-split check (§4): the core declarations alone, over the machine core only | 0 errors; 1 warning, the same `sorry` |
| `elaboration.log`, `axioms.log` | Final runs; `#print axioms` for all 120 public MIG-0b declarations | only the two alphabet-reduction declarations depend on `sorryAx` |
| `work/` | Section sources, the build script (`build.py`, which asserts the verbatim prefix and the 100-column limit), the split script, the probes | |

**Why two files.** The draft must start with the MIG-0a file unchanged, and Lean imports must
precede everything, so the draft can import only what the MIG-0a file imports (`Seam`, `Catalog`,
`Mathlib.Tactic.Linarith`). Their closure (computed with `tools/imports.py`) is `Catalog`,
`Convention`, `Embed`, `Loop`, `Seam`, `Wrappers`, `Composition`, `Configuration`, `Deterministic`,
`Encoding`, `Finite`, `Robustness/AlphabetReduction`, `Robustness/SingleTape`, `Simulation`,
`StateRenaming` and `Sweep`. `SymbolLift`, `Build/CounterLoop`, `CfgRecord`, `RecordTable`,
`OracleSim`, `CodeSimulator`, `CertShell`, `Primitives` and `EmitIterEmbed` are outside it. The
symbol lift and the counter loop are therefore drafted in the adapter probe, which `work/build.py`
generates from the same section sources, so the MIG-0a text and the MIG-0b core text are identical
in both files. At the split, these declarations go to adapter modules that import those files
(§4). Rows that are private, or outside the closure, are fit-tested against verbatim copies, each
cited at file:line.

**Proof status.** Everything is proved except one statement, `exists_alphabetReduction_lockstep`
(D:2347). It needs `Robustness/AlphabetReduction`'s private `arTM`, `arCfg` and `arCfg_cycle`
exported. `alphabetReduction_contract` (D:2364) is proved from it. The structures and definitions
are data, not sorried. All docstrings carry statement prose; nontrivial proofs carry
`**Proof sketch.**`. A local copy of `scripts/style_lint.py` reports only the file-size notes
(sizes are not a driver; the split in §4 divides the file anyway).

## 2. The MIG-0a gate's round-2 input, folded in

1. **`counterSpan` is a segment, not a round.** `CounterLoop.lean:713`: no entry or endpoint
   constraint, a real zero-time case. Its verbatim copy `MIG0bFit.counterSpan` (A:2740) is proved
   equivalent to a `Segment` against `{some done, some escape}`. The relation is the counter
   interval together with the body relation (`counterSpan_iff_segment`, A:2753).
   `counter_span_append` (`CounterLoop.lean:727`) is re-derived as `Segment.trans` after
   `Segment.mono` (A:2776). The zero-time case you describe, with duration, counter position and
   width `0`, counter head at `0` and the constant-true predicate, is `Segment.zero` (A:2801,
   `counterSpan_zero`). The round layer now says that rounds describe the loop's **body interface**
   only (D:1504), and so does the segment layer's header (D:1260).
2. **Zero length, inclusive envelope, actual seam.** `Segment M F P a b t` (D:1287) carries:
   - the endpoint configuration `b` (the seam);
   - `t = 0` allowed (`Segment.zero`, D:1298);
   - the relation at every `u ≤ t`, so the envelope is inclusive;
   - the cut at every `u < t`, which is `RecordRun`'s shape (fit test D:2410).
3. **`splitSafe` is endpoint-inclusive.** It is `Primitives.lean:3505`, with `Catalog.lean:9182`'s
   `f2_splitSafe` identical to it. For it there is `SafeSegment` (D:1405), a segment whose endpoint
   is also off `F`; `safeSegment_iff` (D:1412) is the "every time through the endpoint" form, and it
   has `zero`, `trans`, `mono` and `endpoint_not_mem`. The fit tests:
   - `splitSafe_iff_safeSegment` (D:2517), and `splitSafe_add` re-derived (D:2526);
   - your example, as `stationary_safe` (D:2473): a positive stationary run away from the anchor
     is a `SafeSegment` of every length;
   - `stationary_no_contract` (D:2486): no first-exit contract of that machine with the anchor as
     exit has an admissible start there.

   A `Contract` is obtained only through `Contract.ofSegment` (D:1473), which needs the endpoint
   to lie in the exits.
   **Correction to the input:** `SafeRun` is in `Build/EmitIterEmbed.lean:67`, not `Build/Loop`,
   and its avoidance is **strict** (`∀ t' < t`). It is a plain `Segment` (`safeRun_iff_segment`,
   D:2503). `Build/Loop.lean` has no `splitSafe` or `SafeRun` (grep: 0 occurrences).
4. **Joint trajectories on general segments, with the shared witness.** The joint relation is
   `Segment`'s head-vector predicate `P`. It is not restricted to completed first-exit runs, and
   `trans`, `mono`, `and`, `take`, `drop`, `cons` and `live` preserve it.
   - **The shared witness.** `counterLoopTMVia_done_witness` (A:2818) and `_escape_witness`
     (A:2896) restate the public theorems with the relation **unweakened**: one round `r` and
     offset `u` at which every body head is the body's own. They keep the exact endpoint and the
     counter interval, and add **liveness**: `none` joins the forbidden set by `Segment.live`
     (D:1391), since the endpoint is live and halting is absorbing.
   - **The weakened forms.** `_done_segment` and `_escape_segment` (A:2856, A:2944) are the
     corollaries with a body relation.
   - **At contract level.** `RoundContract.counterLoopDone_traj` (A:3231) and
     `counterLoopEscape_traj` (A:3261) give the counter-loop contracts the shared-witness joint
     trajectory, beyond their per-tape hull envelope.

## 3. The new declarations and the rows they serve

**Exports for lower modules** (D:1100–1249)

| Declaration | What | Row served |
|---|---|---|
| `MultiTapeTM.workTapePos_runFrom_mem_Icc` D:1154 | After `u` steps each head is within `u` of its start | Catalog's private `f2_head_steps` (Catalog:3270, retires with MIG-1, F6-1(g)); time-derived envelopes for the find round, install/emit calls |
| `seamReleaseTM_runFrom_pos` D:1175 | Design item 5, the pointwise release lockstep, proved from the public `seamReleaseTM` definition and `runFrom_mapState_of_agreeOn` | replaces Seam's private `seamRelease_run_pos` (Seam:728); used by `RoundContract.release` |
| `embedEmitCfg_eq` D:1202 | The R1 reconstruction lemma (F6-1(i), F7-1(b)) | §5 |
| `embedEmitCfg_mapState_eq` D:1226 | Its relabelling corollary | §5 |
| `embedEmitCfg_ofWords_eq` D:1242 | Its word-layout corollary | §5 |

**Segment layer** (design item 1)

| Declaration | What | Row served |
|---|---|---|
| `HeadBox` D:1281 | An interval box as a predicate on head vectors | `Contract` envelopes as relations |
| `Segment` D:1287 | Fixed length `t ≥ 0`, endpoint config, strict cut against `F`, inclusive relation `P` | `RecordRun` (CfgRecord:365, 76 occurrences), `SafeRun` (EmitIterEmbed:67), `DGSpan` (SingleTape:1182), `counterSpan` (CounterLoop:713) |
| `Segment.zero` / `one` / `trans` / `mono` / `and` / `take` / `drop` / `cons` / `live` / `time_eq` (D:1298–1391) | Construction, concatenation with no dispatch step, weakening, splitting, liveness, uniqueness of first exits | `recordRun_zero/trans`, `SafeRun.zero/cons/trans`, `dgSpan_add`, `counter_span_append`; `time_eq` is what `rt_findClock_eq` needs |
| `SafeSegment`, `safeSegment_iff`, `SafeSegment.zero/trans/mono/endpoint_not_mem` D:1405–1452 | Endpoint-inclusive avoidance | `splitSafe`, `splitSafe_add/one/join` (Primitives:3505–3970), `f2_splitSafe` |
| `Contract.segment` D:1465 | A contract run is a segment against its exits | bridge |
| `Contract.ofSegment` D:1473 | A family of segments ending in the forbidden set is a contract | bridge "when the endpoint is a first exit"; used by the counter-loop contracts |
| `Contract.time_envelope` D:1491 | Envelope from time alone | rows with a time bound and no envelope |

**Round layer** (design item 2; the body interface)

| Declaration | What | Row served |
|---|---|---|
| `roundStop`, `not_mem_roundStop` D:1514–1519 | `{none, anchor} ∪ E`, and the rows' `∃ s, … = some s ∧ s ≠ a ∧ …` form | both rows state their cut that way |
| `Round` D:1540 | At anchor, positive exact time, endpoint at anchor or in `E`, interior live and off both, relation `P` | `rt_find_round_entry` (RecordTable:1810), counter-loop body rounds (`hround` of CounterLoop:1220, 1306) |
| `Round.segment` / `cut_some` / `of_cut` / `time_box` D:1554–1589 | A round is a segment against `E`; the rows' cut form; constructor from the rows' form; time-derived box | |
| `roundOrbit`, `roundOrbit_succ` D:1603–1608 | The orbit, definitionally `counterLoopOrbit` (A:2734 `rfl`) | CounterLoop:642 |
| `Round.iterate` D:1620 | `n` orbit rounds form one segment of length `∑ τ` | the counter loop's composition without the counter |
| `RoundContract` D:1636, `.round`, `.returning`, `.escaping` | The contract-level round, its returning case as a `ReturnContract`, its escaping case as a `Contract` | |
| `ReturnContract.toRound` D:1711 | A `ReturnContract` is a round contract with no escapes (liveness derived) | writer rounds (`writeAdvTM_run_ofCfg`) |
| `RoundContract.release` D:1745 | A round through the release adapter is a `Contract` with exits the right-tagged anchor and escapes | lets return and escape reach `branch`/`inPhase` as two live exits |
| A: `RoundContract.hullLo/hullHi/orbit_anchor/orbit_round/orbit_start`, `headBox_lastCases` (A:3021–3098) | Hull of an orbit's round boxes; orbit rounds are rounds | generic, core homes |
| A: `RoundContract.counterLoopDone` A:3122, `counterLoopEscape` A:3177, `_traj` A:3231, A:3261 | **The counter loop over the round layer**, contract to contract | `counterLoopTMVia_run_done`, `_run_escape` |

**Joint-trajectory layer** (design item 3)

| Declaration | What |
|---|---|
| `Contract.Traj` D:1803 | A head-vector relation at every time up to the endpoint, derived like `Frames` |
| `traj_env`, `Traj.mono`, `Traj.and`, `Traj.segment` D:1814–1830 | The envelope box as a joint trajectory; weakening; conjunction; to a segment |
| `Traj.trans` D:1841, `Traj.seq` D:1876, `Traj.inPhase` D:1929, `Traj.embed` D:1957, `Traj.branch` D:1978 | **Preservation by all five compositions** (all proved) |
| `Frames.trans` D:1858, `Frames.seq` D:1905 | Frame preservation (the auditor's suggestion) |
| `clearTM_contract_traj` D:2028 | Instance: the uncleared heads are fixed, a whole-vector relation |

**Sanity** (design item 7)

- `time_eq_zero_iff` (D:2052): time `0` exactly when the entry is an exit, on admissible starts.
- `positive_of_not_mem` and `not_mem_of_positive`.
- Positivity: `trans_positive`, `seq_positive`, `inPhase_positive`, `branch_positive`,
  `embed_positive`, `ReturnContract.release_positive` and `RoundContract.release_positive`
  (D:2064–2130).

**Transports** (design item 6)

| Declaration | What |
|---|---|
| `Contract.mapState` D:2187 | State renaming along an embedding, over `runFrom_mapState_of_agreeOn` (proved) |
| `Lockstep` D:2224, `.runFrom` / `.cut` / `.locate` | Macro-step simulation with per-step cost; covers alphabet reduction (cost `3(|Γ|+1)+2`) and lockstep decorations (cost `1`); folding has variable cost |
| `Contract.lockstep` D:2307 | Contract transport along a lockstep (proved); the index records the source start |
| `FinTM.exists_alphabetReduction_lockstep` D:2347 (**sorry**), `FinTM.alphabetReduction_contract` D:2364 | Alphabet reduction as a lockstep, then contract to contract ([AB09, Claim 1.5]) |
| A: `Contract.liftSymbols` A:2701 | The symbol lift through `Cfg.decodeSymbols` (proved), over `liftSymbols_runFrom_over` and `liftOver_decodeSymbols` (SymbolLift:348, :371) |

## 4. Fit-test results

All proved, against the rows at file:line:

| Row | Fit test | Result |
|---|---|---|
| `RecordRun` (CfgRecord:365) | `recordRun_iff_segment` D:2410 | `↔ Segment R {some yes, some no} (radius relation)`; `recordRun_trans` (:385) and `recordRun_zero` (:372) re-derived, D:2418, D:2430 |
| `SafeRun` (EmitIterEmbed:67) | `safeRun_iff_segment` D:2503 | a plain segment |
| `splitSafe` (Primitives:3505) | `splitSafe_iff_safeSegment` D:2517, `splitSafe_add` D:2526 | endpoint-inclusive segment |
| `DGSpan` (SingleTape:1182) | `dgSpan_iff_segment` D:2543 | `Segment tm ∅ (interval on tape 0)` |
| `counterSpan` (CounterLoop:713) | A:2753, A:2776, A:2801 | a segment with a joint relation; append; zero case |
| round 1, counterexample 4 | `idle_segment` D:2463 | the idling segment is a `Segment` |
| round 2's example | `stationary_safe` D:2473, `stationary_no_contract` D:2486 | `SafeSegment` yes; first-exit contract impossible |
| `rt_find_round_entry`'s conclusion (RecordTable:1810) | `findRound_round` D:2552 | a `Round` with the time-derived box (the row states no envelope) |
| counter-loop body rounds (`hround`, CounterLoop:1220) | `counterLoop_hround_of_rounds` D:2568, fed to the public theorem in A:2818 | the round layer supplies the public hypothesis exactly |
| `counterLoopTMVia_run_done/_escape` (CounterLoop:1220, 1306) | A:2818–2944, A:3122–3261 | host segments and contracts derived from the **public** theorems |
| R1 family | D:2589–2653, A:2989 | §5 |

Two Lean pitfalls recurred and are recorded for the tactics (§7):
- `omega` fails on un-beta-reduced box goals `(fun j => …) j` until `simp only [Finset.mem_Icc]`;
- implicit relations in `Segment.mono` need a type ascription (the `counter_span_append` fit).

## 5. The R1 reconstruction lemma and its consumers

`embedEmitCfg_eq σ tapes heads pre c d hs hin hout selected outside` (D:1202) is the main lemma.
It needs no machine argument, so the time-zero `embedEmitTM_frame` workaround that the consumers
carry goes away (45 uses of `embedEmitTM_frame` outside `Embed`). `embedEmitCfg_mapState_eq`
(D:1226) adds relabelling, and `embedEmitCfg_ofWords_eq` (D:1242) is the word layout. Each
consumer's verbatim statement is proved from it in `MIG0bFit`:

- **`OracleSim.oracleBankCfg_eq`** (OracleSim:532; used at :1337, :1536, :1869). Fit:
  D:2589, one term. **Citation:**

  ```lean
  apply embedEmitCfg_eq ι _ _ [] c d hs hin hout
  ```

  The two goals `htape` and `hhead` merge into one `selected` goal, `fun i => ⟨htape i, hhead i⟩`.
  `outside` is `fun _ _ => ⟨rfl, rfl⟩`, since the frame is `d`'s own. `hout : c.output = d.output`
  is accepted as `[] ++ c.output = d.output` by definitional unfolding. The unused machine argument
  `A` disappears.
- **`Loop.emCall_exit_fixed`'s local `hframe`** (Loop:4554–4573, used at :4585). The private
  `emCallEmbeddedCfg` (Loop:3535) is definitionally `(embedEmitCfg index tapes heads [] c).mapState
  emb`. Fit: `emCall_hframe` (D:2631), whose `hs` is `hz.symm`. **Citation**, replacing the 20-line
  `have`:

  ```lean
  embedEmitCfg_mapState_eq (emCallPairEmbedding M) (fun q => .inr (.inr q))
    z.workTapes z.workTapePos [] c z hz.symm rfl rfl (fun _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
  ```

  `hz.symm` may need a `by simp [c, hz]` if the local `c` is not unfolded.
- **`CodeSimulator.canonEmbedEq`** (CodeSimulator:1201; used at :1238, :1686, :1698, :1775).
  Fit: D:2601, one term. **Citation:** the arguments reorder, the machine goes, and
  `pre := []` appears:

  ```lean
  -- before
  canonEmbedEq M ι c d tapes heads hs hp ho sel out
  -- after
  embedEmitCfg_eq ι tapes heads [] c d hs hp ho sel out
  ```

  For example, :1686 becomes `embedEmitCfg_eq ι _ _ [] src d rfl rfl rfl (fun _ => ⟨rfl, rfl⟩)
  (fun _ _ => ⟨rfl, rfl⟩)`.
- **The analogues** (the F7-1(b) family):
  - `Primitives.emitterP2_frame` (Primitives:5199; five uses at :5228–5344, all
    `apply emitterP2_frame q <;> try rfl`) becomes `apply embedEmitCfg_mapState_eq index emb tapes
    heads [] <;> try rfl` (fit D:2615).
  - `CodeSimulator.canonEmbedWords` (:1231, nine uses) becomes `embedEmitCfg_ofWords_eq` with the
    machine argument dropped (fit D:2642).
  - `CertShell.cert_embed_words` (:228, uses :269, :276) is the same, but its `hout` points the
    other way (`target i = frame i`), so it is cited with `fun i hi => (hout i hi).symm`.
- **Members not in the records:**
  - `CounterLoop.counter_layout` (CounterLoop:650, used at :687, :874, :898, :1010–1018, :1153,
    :1156) does the same time-zero trick. Its reconstruction form is `counterLoopCfg_body`
    (A:2989), proved by `embedEmitCfg_eq`. Recommendation: re-prove `counter_layout` by
    `embedEmitCfg_eq` at MIG-15 and keep its statement, since its uses are `simp` rewrites.
  - MIG-0a's own `embedEmitCfg_select` (D:525) is a one-term corollary (D:2653).
- **Not covered: the silent flavour.** `CertShell.cert_silent_words` (:315) works on
  `embedSilentCfg` with a capture tape. It needs a public capture-field lemma; `CertShell`'s
  `cert_capture_fields` (:101) is private. See open question 9.

## 6. Layering plan (design item 4)

**Checked:** `layering-core-probe.lean` is the draft with the adapter and routine declarations
removed (`work/coresplit.py`, 42 named blocks). It imports only `Mathlib.Tactic.Linarith`,
`Simulation` and `StateRenaming`, contains the two moved-down lemmas verbatim at their proposed
homes, and has the generic orbit-hull lemmas appended. It elaborates with only the
alphabet-reduction `sorry`. The core's import closure is `Configuration`, `Deterministic`,
`Finite`, `Simulation` and `StateRenaming`. It contains no `Build` module, so `Build/Loop` and
`Build/CounterLoop` can import the core with no cycle.

**Step 1: move down first (additive; names and namespaces unchanged).**
- `MultiTapeTM.spaceUsedByTape_le_card_Icc` goes from Catalog:392 to `Deterministic.lean`, after
  `spaceUsedByTape` (:256). `Int.card_Icc` is available through `Configuration`'s
  `Mathlib.Data.Int.Interval`. Its users are Catalog:412, `ClassPSPACE/TQBF.lean:1949` and the
  MIG-0a draft line 177; `Build/Zone.lean:110` only cites its location in a docstring, which needs
  updating.
- `MultiTapeTM.runFrom_mapState_of_agreeOn` goes from **`Build/Embed.lean:1010`** (not
  `StateRenaming.lean`) to `StateRenaming.lean`, which then imports `Simulation` (for `AgreeOn` and
  `runFrom_eq_of_agreeOn`, Simulation:970, :1002). `Simulation` does not import `StateRenaming`,
  so there is no cycle. Without this move, `Contract.mapState` goes to the Embed adapter instead
  (open question 7).
- New: `MultiTapeTM.workTapePos_runFrom_mem_Icc` goes to `Deterministic.lean`, beside
  `workTapePos_step_le` (:235).

**Step 2: the exports go into their lower modules.**
- `Build/Embed`:
  - `embedEmitCfg_unselected` (MIG-0a);
  - `Cfg.select` and `embedEmitCfg_select`, the latter re-proved by `embedEmitCfg_eq`;
  - `embedEmitCfg_eq` and `embedEmitCfg_mapState_eq`;
  - `embedEmitCfg_ofWords_eq`, which needs `Cfg.ofWords` (Convention:80). Recommended: `Embed`
    imports `Convention`, which imports only `Simulation`.
- `Build/Seam`: `seamCompTM_runFrom_right` (MIG-0a) and `seamReleaseTM_runFrom_pos`, which
  replaces the private `seamRelease_run_pos`.

**Step 3: the core module, `Build/Contract/Basic.lean`.** It imports `Simulation`, `StateRenaming`
and `Mathlib.Tactic.Linarith`, and holds:
- MIG-0a: `Contract`, `within`, `spaceUsedByTape_le`, `Positive`, `mem_Icc_of_abs_le`, the hull
  lemmas, `runFrom_state_none_mono`, `trans`, `live`, `Cfg.SameOutside` with `.trans`, `.mapState`,
  `.keep_word` and `.keep_blank`, `Frames`, `frames_iff` and `ReturnContract`;
- MIG-0b: `HeadBox`, `Segment` and its lemmas, `SafeSegment`, `Contract.segment`,
  `Contract.ofSegment`, `time_envelope`, `roundStop`, `Round` and its lemmas, `roundOrbit`,
  `Round.iterate`, `RoundContract` with `round`, `returning` and `escaping`,
  `ReturnContract.toRound`, `hullLo`, `hullHi`, `orbit_*`, `headBox_lastCases`, `Traj` with
  `traj_env`, `mono`, `and`, `segment` and `trans`, `Frames.trans`, the sanity lemmas
  (`time_eq_zero_iff`, `positive_of_not_mem`, `not_mem_of_positive`, `trans_positive`),
  `Contract.mapState` and `Lockstep` with `Contract.lockstep`.

**Step 4: the adapters.**
- `Build/Contract/Seam.lean` (core + `Seam`):
  - from MIG-0a: `mapState_state`, `seq_traj`, `seq`, `Cfg.bindState`, `inPhase_traj`, `inPhase`,
    `mapState_const_inl(_inl)`, `branch_traj`, `branch`, `release_start` and
    `ReturnContract.release`;
  - from MIG-0b: `RoundContract.release`, `Traj.seq`, `Traj.inPhase`, `Traj.branch`, `Frames.seq`,
    the positivity of `seq`, `inPhase` and `branch`, and both `release_positive`.
- `Build/Contract/Embed.lean` (core + `Embed`): `embed`, `Traj.embed` and `embed_positive`.
- `Build/Contract/Catalog.lean` (core + `Catalog`): `clearTM_contract`, `clearTM_contract_frames`,
  `clearTM_contract_traj`, and MIG-11's ~25 instances.
- `Build/Contract/Lift.lean` (core + `SymbolLift`): `Contract.liftSymbols`.
- `Build/CounterLoop.lean` itself, which imports the core:
  - `counterLoopOrbit` becomes an abbreviation of `roundOrbit`;
  - the `_witness` and `_segment` theorems;
  - `counterLoopBody` and `counterLoopCfg_body`, which retires `counter_layout`'s workaround;
  - `counterValue` and the two `RoundContract.counterLoop*` contracts with their `_traj`.
- `Robustness/AlphabetReduction.lean`, which imports the core: the lockstep existence, proved
  there against the private simulator, and `alphabetReduction_contract`.

**Step 5.** Add the facade `Build/Contract.lean` with `## Contents`, and export it from
`TCSlib.lean`. A flat alternative (`Build/Contract.lean`, `Build/ContractSeam.lean`, …) is
equivalent; the subdirectory follows `policy.md` §1's Area/Topic/Piece layout.

**Step 6.** The `MIG0bFit` tests do not land; their content is the rebases (MIG-5, MIG-12, MIG-13,
MIG-15, MIG-16, MIG-17, RS-3). The two gate examples could stay as `example`s in a test file.

## 7. Tactics (design item 7; no implementation)

A small contract tactic set, run against the residue that the layers leave:

- **`contract_start`.** A simp set for the start boilerplate in every adapter field:
  - `(d.mapState fun _ => e).state = some e`;
  - re-tagging identities such as `(c.mapState f).mapState g = d` (`mapState_const_inl`,
    `release_start`).
  Concrete goal: `rt_find_round_entry`'s `hstart` (RecordTable:1830), now
  `apply Cfg.ext <;> simp [d, Cfg.mapState, hc]`.
- **`seg_split`.** For a goal at `u ≤ t₁ + t₂` or `u < …`: split at `t₁`, take the offset, and
  rewrite `runFrom_add` and the first run.
  - Concrete goals: `counter_span_append` (CounterLoop:727–750), `recordRun_trans`
    (CfgRecord:385–402), `dgSpan_add` (SingleTape:1190), `splitSafe_add` (Primitives:3510) and
    `SafeRun.trans` (EmitIterEmbed:94). All five become `Segment.trans` (or `SafeSegment.trans`),
    as the fit tests show.
  - What is left is in `Traj.trans`, `Traj.seq` and `Traj.branch`.
- **`exit_tag`.** Closes `(X.mapState tag).state ∉ Option.map tag' '' E` by tag injectivity and
  constructor disjointness. It covers MIG-0a's `seq` cut (D:359–371), the `branch` cut
  (D:1036–1072) and `RoundContract.release`'s cut.
- **`r1_ext`.** Closes configuration equalities by `embedEmitCfg_eq`, `embedEmitCfg_mapState_eq`
  or `Cfg.ext`, with `rfl` per field. Concrete goal: Loop:4554's `hframe`.
- **`envelope`.** Normalizes box goals (`simp only [Finset.mem_Icc]`, which removes the
  `(fun j => …) j` redexes that defeat `omega`), then combines `mem_Icc_of_abs_le`,
  `workTapePos_runFrom_mem_Icc` and the hull lemmas `Finset.inf'_le` / `Finset.le_sup'`.
- **Default-argument obligations**, in the manner of [AFM26]: the link obligations of
  `trans`/`seq`/`branch` (`hlink`, `hX`) as `autoParam`s (`by first | assumption | simp_all`).
  The target is CfgRecord's pipeline chains (CfgRecord:1657–1828).

## 8. Open questions, with recommendations

1. **Time-independent relations.** `Segment`'s `P` sees only the head vector. Every row fitted is
   time-independent. Recommendation: keep it; time-indexed facts (a sweep's `head = start + u`)
   stay trajectory lemmas until a consumer needs an indexed variant.
2. **`SafeSegment` as `Segment ∧ endpoint ∉ F`**, rather than a flag on `Segment`.
   Recommendation: keep the conjunction; every segment lemma is reused.
3. **Liveness in the round cut** (`roundStop ∋ none`). It matches both rows verbatim.
   Recommendation: keep.
4. **The round contract's index is constant along the orbit** (`counterLoopDone` asks
   `R.pre p.1` at every orbit point). The find round's per-round data (the current entry) lies on
   the tape, so `pre` can read it from the configuration. Recommendation: keep; add an
   index-update function only if MIG-13 needs it.
5. **A general positive-cut contract** (MIG-0a minor 5's alternative; F7-1(d)'s
   `canonStrictInstall`). The install and emit calls cut only against the exit at positive times
   and may revisit the entry, so they are not rounds. A `PositiveContract`, with the release, would
   need no `entry = exit` case split. `RoundContract.release`'s proof carries over with
   `roundStop` replaced by the exits. Recommendation: add it at the MIG-0b fill (about 60 lines,
   ESTIMATED), keeping `ReturnContract` as gated.
6. **The lockstep's index records the source start** (`ι × Cfg`), instead of a decoder
   `dec` with `enc ∘ dec = id`. Recommendation: the index (no inverse needed).
7. **`runFrom_mapState_of_agreeOn`'s home.** Move it to `StateRenaming` (recommended), or put
   `Contract.mapState` in the Embed adapter.
8. **`embedEmitCfg_ofWords_eq`'s home.** `Embed` importing `Convention` (recommended), or `Seam`.
9. **The silent-flavour reconstruction** (`CertShell.cert_silent_words`). Recommendation: export
   the capture-tape field of `embedSilentCfg` next to `embedEmitCfg_unselected`, then add
   `embedSilentCfg_mapState_eq`; schedule with MIG-14 (`CertShell`).
10. **The alphabet-reduction export.** Make `arTM`, `arCfg` and `arCfg_cycle` public (renamed),
    plus a lemma that a mid-cycle control is never `arReady`. Then prove
    `exists_alphabetReduction_lockstep` in `AlphabetReduction` (80–150 lines, ESTIMATED), at
    RS-5. The robustness lockstep combinators (Oblivious decorations, SingleTape folding) are
    `Lockstep` instances once their private simulators are exported; folding needs the
    variable-cost form already drafted.
11. **Retire `counterLoopOrbit`** in favour of `roundOrbit` (definitionally equal, A:2734) at
    MIG-15. Recommendation: yes, as an abbreviation first.
12. **Hull envelopes are data-dependent** (`hullLo`/`hullHi`, `Contract.lockstep`).
    Recommendation: add corollaries for a uniform round envelope at the fill.
13. **Not yet drafted:** `Frames` for `embed`, `inPhase`, `branch` and the release, and `Traj`
    for `ReturnContract`/`RoundContract`. Recommendation: add them when a consumer asks; MIG-16
    (`OracleSim`) likely needs `Frames.embed`.
14. **`ReturnContract.release`'s envelope** could use `seamReleaseTM_runFrom_pos` instead of the
    visited-set detour (MIG-0a D:847–858). This is a proof-only change to MIG-0a code.
    Recommendation: do it at the split, under the freeze/fidelity gate.

## 9. Size (ESTIMATE)

**Measured:** the new MIG-0b text is 2,182 lines:

| Source | Lines |
|---|---|
| exports | 153 |
| segment and round | 533 |
| trajectory and sanity | 350 |
| transports and fits | 526 |
| adapters | 620 |
| **Total** | **2,182** |

Of these, 337 are fit tests that do not land.

**ESTIMATED landed size of MIG-0b:**

| Part | Lines |
|---|---|
| Landable text (2,182 − 337) | about 1,850 |
| Module headers and facade | about 150 |
| The alphabet-reduction export | 80–150 |
| **Total** | **about 2.1k–2.2k** |

With MIG-0a's 1,099 lines, MIG-0 totals about 3.3k–3.4k. That is **above** backlog MIG-0's
"+1.5k to +2.5k" (backlog:592).

**ESTIMATED direct retirements in the rebases**, about 400 lines:
- CfgRecord's `RecordRun` trio;
- `counterSpan` and its append;
- `DGSpan` and its add;
- `splitSafe` and its add/one/join, and the `f2_` copy;
- `SafeRun.zero`, `cons` and `trans`;
- the seven-member R1 family.

These are counted inside the MIG-12, MIG-15, RS-3, MIG-17, MIG-5 and MIG-16 savings, not in
addition to them.

## 10. What the code contradicts in the records

1. **backlog MIG-17** says "`splitSafe`/`SafeRun` become Contracts", scoped to `Primitives` and
   `Loop`. In the code, `splitSafe` (Primitives:3505) is an endpoint-inclusive segment and
   `SafeRun` (**EmitIterEmbed:67**, MIG-5's file) is a strict segment; neither is a first exit,
   and `Loop` contains neither. Round 2's input has the same `Loop` attribution.
2. **backlog MIG-15** says "`counterSpan` becomes MIG-0b's round layer". `counterSpan`
   (CounterLoop:713) is a segment with a joint relation. Only the body rounds are rounds, as round
   2 also found.
3. **backlog RS-3** says "`DGSpan` becomes a Contract". `DGSpan` (SingleTape:1182) has no exit
   and no cut; it is `Segment tm ∅ …` (D:2543).
4. **The MIG-0a header** (D:106) names `MultiTapeTM.liftSymbols_runFrom` for the symbol lift
   through `Cfg.decodeSymbols`. That route needs `liftSymbols_runFrom_over` (SymbolLift:348) and
   `Cfg.liftOver_decodeSymbols` (:371). `liftSymbols_runFrom` (:178) takes a `Bool` input and
   keeps no rich frame.
5. **`runFrom_mapState_of_agreeOn`** lives in `Build/Embed.lean:1010`, not `StateRenaming.lean`.
   Design §16a item 4's "the core part needs only the machine core, apart from
   `spaceUsedByTape_le_card_Icc`" therefore omits a second move-down, if state renaming is to be
   in the core (§6).
6. **F7-1(b)'s reconstruction family** is larger than recorded: also `CounterLoop.counter_layout`
   (:650), `CodeSimulator.canonEmbedWords` (:1231), `CertShell.cert_embed_words` (:228) and
   MIG-0a's `embedEmitCfg_select`. The silent analogue (`CertShell.cert_silent_words`, :315) is
   not covered by one emit-flavour lemma.
7. **`audits/mig0a-resolutions.md:10`** gives the r2 file as "1,100 lines". It has 1,099
   newline-terminated lines (`wc -l`), the convention under which round 1's 888 and 843 are right;
   1,100 counts the empty string after the final newline.
8. **Design §16a item 2** describes rounds as having "positive cuts against the anchor and the
   escape". Both rows also require the interior to be **live** (`∃ s, … = some s`;
   CounterLoop:1230–1232, RecordTable:1819). The round layer includes it.
