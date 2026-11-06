# Fill u2s-g5 — `Turing.FinTM.two_work_tapes_run` (Hennie–Stearns on two work tapes): COMPLETE

**Outcome: complete.** `Turing.FinTM.two_work_tapes_run` is proved, with its frozen statement,
on `[propext, Classical.choice, Quot.sound]`; so are `two_work_tapes_binary` and (see §9)
`Turing.universal_TlogT`. All nine checkpoints are reached. Nothing outside regions (a)–(c) is
changed; region (d) is not used (the target is closed). No new public declaration, no new file,
no new import beyond region (a)'s.

- Agent: Claude (Claude Code, cloud session). Brief `u2s-fill-g5.md` (SHA-256
  `c5723901fcd2b098b7d75cafbef799d8be629fbc5fa3e5c02e8dc48de3e85360`, verified) and addendum v2.6
  (`9f5bd5e74bb767e50a6e7a372e98a5567998ec14be432c1dfb7ff8856eb9bd28`, verified), both identical to
  the records commit `fe5cb6fb`'s `campaign/fills/u2s/briefs/u2s-fill-g5.md` and
  `campaign/standards/fill-environment-addendum.md`.
- **Base** `335d31d408f1b4b4164f5b1b3a37d246a42b25cc` (`git checkout -b fill/u2s-g5 335d31d4…` on a
  checkout of `complexity/arora-barak-ch3-4`; `git rev-parse HEAD` printed it). **Ancestor check**
  `git merge-base --is-ancestor 335d31d4… HEAD` on `complexity/arora-barak-ch3-4`: passed. **Blob
  check** `git rev-parse HEAD:TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean` =
  `cc35767342620a3be6331c57239e5eafa5ea4c45`: passed. No rebase, merge or cherry-pick.
- **Final commit:** `71046be089f7c248291cde78be2c47a6440fd92b` (the bundle `fill-u2s-g5.bundle` has the base as its only
  prerequisite; `patches/` is `git format-patch 335d31d4..71046be089f7c248291cde78be2c47a6440fd92b`, 15 patches).

## 1. Environment (addendum v2.6 Part 1; Part 2 not needed)

From `evidence/logs/preflight.log`: `nproc` 4; cgroup v1, limit 14,337,302,528 B; memory in use
`usage 803598336 − total_cache 747200512 + total_shmem 0 = 56397824` B; **headroom 13.30 GiB**
(floor 4); `MemAvailable` 15.23 GiB; `oom_kill 0`. Clone and scratch on `/dev/vda`, **ext4**;
**29.31 GiB free** (floor 12); re-check after the toolchain 28.89 GB free (floor 8 GiB).
Toolchain: elan + `leanprover/lean4:v4.25.0`, installed by this session; Lean starts normally, so
**the `/proc/<pid>/exe` shim was not used**.

**Cache:** the archive store `/root/.cache/mathlib` did not exist before the fetch
(`cache-store.log`: 0 files, 0 bytes); every archive was downloaded by this session.
`TAR_OPTIONS=--no-same-owner lake exe cache get $(cat mathlib-roots.txt)` with the **42 roots**:
"Attempting to download 1022 file(s)", "Decompressing 1022 file(s)", "Completed successfully!",
exit 0, no failed download. Manifest check: `manifest check: PASS (every present package matches)`,
ABSENT `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; empty oleans 0. Cache probe
(`import Mathlib.Algebra.BigOperators.Fin`) exit 0. Never `lake build`, never the unfiltered fetch;
one Lean process at a time (the copy screens ran beside at most one).

`/usr/bin/time` is absent; every module's start, end, elapsed time and maximum RSS is logged by a
small wrapper (`resource.getrusage(RUSAGE_CHILDREN)`).

## 2. Bootstrap and final sweep

- **Bootstrap, first part** (addendum item 5): the 25 order-list modules of `TwoTapes`' closure,
  in order, on the overlay (`bootstrap-1-closure.log`, `bootstrap-1-table.md`): all exit 0, 575 s;
  peaks `Build/ZoneRebalance` 372 s / **4,629 MiB** (above the addendum's 2.8 GiB figure; recorded,
  no shortage) and `Build/Catalog` 107 s / 2,875 MiB. Overlay `TwoTapes`: exactly
  `TwoTapes.lean:65:8: declaration uses 'sorry'`.
- **Final sweep** = the whole order list (105 modules, `final-sweep-list.txt`) with the final
  `TwoTapes`, in order (`final-sweep.log`, `final-sweep-table.md`). The 80 modules outside the
  closure are first built here (the list's remaining modules, built before any check that needs
  them). Result: **all 105 modules exit 0, 0 errors** (`SWEEP EXIT 0`; 1,116 s in all; the largest `Build/ZoneRebalance` again; `TwoTapes` 7.6 s, 2,132 MiB, no warning). Logged per module with time and maximum RSS.
- **Sorry warnings** (base: 22 entries in 9 modules, `u2s-fill-g5-base-sorries.txt`): **21 warnings in 8 modules — the base set minus `TwoTapes`' one, module by module**: Simulation 1, Composition 3, Build/Wrappers 2, Build/Loop 5, Encoding 1, ClassP/TimeConstructible 2, Build/Primitives 3, Build/RecordTable 4 (the counts per module equal the base list's; Lean's warnings carry positions, not names). `TwoTapes`: none. No difference from the base.

## 3. The proof (what each part does)

`TwoTapes.lean`: 86 → **2,464 lines**; **2 public (unchanged), 102 private**, all `tt_`, all in
region (b) (between `namespace Turing.FinTM` and the target's docstring) and the target's body
(region (c)). Every proof over 20 lines carries a `**Proof sketch.**`.

**Frame (CP1, route steps 0–1)** — `tt_zero_tapes` (`k = 0`: R1 `embedEmitTM σ M.tm`, `c = 1`),
`tt_frame` (`alphabet_reduction_run (Function.Embedding.inl) HS`, `c = c₂ · c₁`), `tt_route`;
copied from the route probe.

**The machine `HS` (CP2–3)** — tapes: `0` the zoned tape (`Turing.zonedTape`), `1` the scratch
tape; input `x.map Sum.inl` read directly.
- *Leaf* (`tt_leafTr`, `tt_leafTM`, one-step lemma `tt_leaf_step`): read the home tuple
  `(zoneCellOfCell (w 0) t).join` and the input through `Sum.inl`; apply `M.tm.tr q`; write
  `some (.inr fun t => some (v' t))`, `v' t = (a.workTapes t).1.getD (v t)`; move the input head;
  emit `a.output.map Sum.inl`; keep both work heads; go to `inr (q', m)` or halt with `M`.
- *Phases* (`tt_I`, `tt_Ph`, `tt_Mf`): the leaf `none`, and `some (q', m, t)` running the track step
  of direction `tt_dir (m t)` from the chosen family `tt_Fam` (`exists_zoneTrackStepTM`); **every
  track has a phase every round, a stay being a zero-time phase** (redirected at its entry).
- *Redirects* (`tt_red`, classical): leaf exit → track `0`'s entry; track `t`'s live exit (stay:
  entry) → track `t + 1`'s entry, or the leaf at `q'` after the last (`tt_next`). Host:
  `phaseHostTM (tt_Mf M F) ⟨none, inl M.tm.q₀⟩ (tt_red M F hk)` (`tt_HS`), states
  `Σ i, tt_Ph M F i`, finite by `tt_phFin`/`tt_phDec`.
- *One round* as a `Turing.Segment` against `{none}`: `tt_track_seg` (one track, via
  `phaseHostTM_run` with the track contract's run, cut, exit and `Contract.live`), `tt_tracks_seg`
  (the tracks, **by `Segment.iterate_seq`**), `tt_round` (leaf + tracks; the halting round via
  `phaseHostTM_run_le`), `tt_τ_le` (time).

**The invariant (CP4)** — `tt_rep` (`zoneTrackTape (D.2 t) p = c.workTapes t (c.workTapePos t + p)`)
and fullness `tt_full` (each level: `|L_i| + |R_i| = zoneCapacity i`, `|R_i| ∈ {0, 2^i, 2^{i+1}}`):
preserved by the home write, the extension, both rebalances (`tt_full_*`, `tt_tape_rebalance`,
`tt_trackStep_inv`, `tt_Dtr_inv`, `tt_homeData_inv`, `tt_round_inv`), along the **data orbit**
`tt_D` (a `tt_` recursion over `M`'s run `tt_c`; `tt_D_inv`). The round's action computed from the
homes is `M`'s (`tt_rep_home`).

**The run (CP5)** — boundary configurations `tt_cs` (explicit encodings: `HS.initCfg`, then the
leaf at `M`'s state with the orbit's data, input position and encoded output); `tt_cs_start`
(the first round from the blank tape: `zonedTape_blank_outside`, `zoneStart_eq`), `tt_cs_round`,
**`tt_cs_run` by `Segment.iterate_seq` over the rounds**, `tt_cs_halt`, `tt_forward_run` (first
halt `exists_first_halt`; `HS` halts with `o.map Sum.inl` after `∑_{r<t₀−1} T_r + 1` steps).

**Fullness arithmetic, count and level (CP6)** — side totals `tt_rsum z n` (right cells below
level `n`) under every zone operation (`tt_rsum_low`, `tt_rsum_rebalance_true/false`,
`tt_rsum_homeWrite`, `tt_rsum_extend`, `tt_trackStep_rsum`), through a round (`tt_Dtr_other`,
`tt_round_rsum`) and along the run (`tt_orbit_rsum`).
- *Count* (`tt_count`): after a step of index `> i` track `t`'s side total below `i + 1` is
  `2^{i+1} − 1`; each round moves it by at most one (or resets it); a step of index `> i` needs it
  at `0` or `2^{i+2} − 2`; so such steps are `≥ 2^{i+1}` rounds apart and
  `#{s < T | i < idx t s} ≤ T / 2^i + 1` (`tt_card_le_of_gap`).
- *Level* (`tt_round_disp`, `tt_D_level`, `tt_idxR_le`): the displacement invariant
  `rsum_t(all levels) + pos_t = 2^ℓ − 1`; an extension at level `ℓ` needs `|pos_t| = 2^ℓ − 1 ≤ r`,
  so `2^{ℓ_r} ≤ 2r + 1` and every scanned index of a run of `T` live rounds is
  `≤ L := log₂ T + 1` (the index of round `s` bounded by the level after round `s`, as the brief
  requires, `s + 1 ≤ T`).

**Cost and forward (CP7)** — `tt_cost`: `∑_{r<t₀−1} T_r + 1 ≤ ∑_{r<t₀} T_r`;
`T_r ≤ B + A ∑_t (2^{idx t r} + 1) + k` with **`B = 2`** (leaf step + dispatch; each track adds its
phase and one dispatch); `Turing.sum_cost_le_of_count k t₀ L A 2` with **`L = Nat.log 2 t₀ + 1`**
gives `2 t₀ + k (A ((L + 2) t₀ + 2^L) + t₀)`; with `2^L ≤ 2 t₀` (`Nat.pow_log_le_self`) and
`log₂ t₀ ≤ log₂ (t₀ + 1)`: `≤ c₁ · (t₀ + 1)(log₂(t₀ + 1) + 1)` with
**`c₁ = 2 + k (5A + 1)`** (`(L+2) t₀ ≤ 3P`, `2^L ≤ 2P`, `t₀ ≤ P`, `P = (t₀+1)(log₂(t₀+1)+1)`).
Then `t₀ ≤ t`, `Nat.log_mono_right` and `ComputesInTime.mono`. **`A`** is
`exists_zoneTrackStepTM`'s constant; **`c = c₂ · c₁`** with `c₂` from `alphabet_reduction_run`.

**Converse (CP8)** — `tt_converse`: if `M` never halted, `t' + 1` rounds would keep `HS` live past
`t'` (each round `≥ 2` steps, `tt_T_ge`); so `M` halts, `HS` halts with its encoded output, and
`ComputesInTime.output_unique` identifies `o'`.

**Target (CP9)** — body: `refine tt_route (fun M hk => ?_) M`; `choose` the family from
`exists_zoneTrackStepTM M.k`; `HS := tt_HS`, `c₁ := 2 + M.k * (5 * A + 1)`; forward by
`tt_forward_run` + `tt_cost`; converse `tt_converse`.

## 4. Edge cases
- `k = 0`: `tt_zero_tapes` (R1, no alphabet reduction). `k = 1`: one track; tape `1` still scratch
  (`tt_HS` needs only `0 < k`).
- `t = 0`: impossible — `tt_forward_run` shows the first halt is `≥ 1` (initial state live).
  `t = 1`: `t₀ = 1`, zero full rounds, one halting step; the bound `c₁ · 2 · 1`.
- Halting at the first transition: `tt_cs_halt` at `r = 0` (one leaf step, no track step).
- Stays: zero-time phases, index `0` (`tt_idx`), never counted.
- First move of a track at level `0`: a short scan, extension, retry inside the track step
  (`tt_trackStep_inv`/`_rsum` short case); its cost uses `zoneRebalanceIndex = ℓ`.
- Several tracks extending in one round: the round's intra-track induction (`tt_Dtr_inv`,
  `tt_round_disp`) handles each extension on every track.
- Input head at either end, `x = []`: `tt_inputSymbol` (`inputSymbol_of_zero`/`_of_end`,
  `inputSymbolInner`), `tt_moveInputPos_val`.
- Blank write vs no write: `tt_homeNew` (`getD`) ≡ `Action.apply_workTapes`.
- Emission at the halting transition: `tt_round`'s halting clause, `tt_cs_halt`.
- A source that never halts: no completed output of `HS` (`tt_converse`), hence none of `M'`.

## 5. Rule 10 (no unfolding) and rule 11
- **Elaborated-constant walk** (`final/walk.out`): the TCSlib constants used from other modules,
  each with its kind. Non-theorems: structure types, constructors, projections, the reducible
  `abbrev`s `ZoneSym`, `ZoneCell`, `ZoneData`, `Cfg.Halted`, and 43 definitions — all sealed.
- **Seal** (`evidence/seal/TwoTapesSealed.lean`, generated by `mkseal.py` from `seal-list.txt`): **43
  other-file definitions** `[local irreducible]` (the route probe's 15; the brief's list; and
  `FinTM.ComputesFunInTime`, `ZoneContents.empty`, `zoneCascadeLeft`, `zoneCascadeRight`,
  `zoneStart`), `[-simp]` on `MultiTapeTM.initCfg`, `Cfg.init`, `Action.apply`. Command
  `bash scripts/lean_check_tree.sh Scratch/seal-final/TwoTapesSealed`: **exit 0, no diagnostic**.
  The reducible abbrevs cannot be sealed (route probe README) and stay out.
  *The seal caught one violation during the fill* (fixed in `71046be0`): a `show` in
  `tt_cs_start` stated the output equation the wrong way round and closed only by unfolding
  `runFrom`/`Cfg.init`; it now rewrites with `Cfg.init_output`.
- **Controls** (`TwoTapesCtl_unsealed.lean` / `_sealed.lean`; `#ctl_rfl` + `#ctl_eqn` per sealed
  definition, `#ctl_simp` for the three simp ones): **unsealed 89 CONTROL_PASS / 0 FAIL; sealed
  0 PASS / 89 CONTROL_FAIL**; both exit 0. Raw outputs with commands: `evidence/logs/final/`.
- **Inspection table** `final/inspection.md`: every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/
  `change` argument classified; **other-file definitions passed to a rewriting tactic: **0** (586 arguments classified)**.
  `unfold` is used only on this file's `tt_rsum`; `show` steps reduce only this file's definitions
  and structure projections (the seal confirms).
- **Import probe** re-run, extended: **307 checks** (pre-ship 217 + 90 further names cited,
  `evidence/seal/G5ImportProbeExt.lean`), 0 errors.
- **Rule 11** (`final/rule11.txt`): none of the six R3 rows; no other file's private name.

## 6. Axioms (`final/TwoTapesAxioms.out`, `final/UniversalAxioms.out`)
`two_work_tapes_run`, `two_work_tapes_binary`: `[propext, Classical.choice, Quot.sound]`. All 102
privates within those three (72 on all three, 13 on `propext, Quot.sound`, 12 on `propext`, the
rest on none). **No `sorryAx` anywhere in the module.** `Turing.universal_TlogT` (probe importing
`UniversalTlogT`): `'Turing.universal_TlogT' depends on axioms: [propext, Classical.choice, Quot.sound]` — **no `sorryAx`** (`final/UniversalAxioms.out`, exit 0).

## 7. Duplication
- **Before screen** (frozen worktree of the overlay commit `3232187a`): byte-identical to the screen
  base (1,210 declarations, 819 pairs, 281,024 characters).
- **After screen** (frozen worktree of the final commit, same command): **1,277 declarations, 843
  pairs, 290,770 characters**. All 819 base pairs are unchanged; **no new cross-file pair** — no pair
  has a `TwoTapes` declaration on one side and another file's on the other. The **24 new pairs are
  all inside `TwoTapes`** (both sides this fill's privates), the largest at 89%, none at the 90%
  copy threshold; each with its disposition in `evidence/logs/final/screen-new-pairs.md`: the
  left/right mirror lemmas (`tt_full_pre_*`, `tt_full_rebalance_*`, `tt_rsum_rebalance_*`, 78–84%),
  the `match`-reading idiom of the orbit's own definitions (`tt_D`, `tt_T`, `tt_idxR`,
  `tt_D_succ`, `tt_T_ge`), the two track inductions, and `tt_cs_round`/`tt_cs_halt`. They are
  accounting items for the integrator (a refactor through the mirror would merge the first group).
- During the fill two pairs appeared and were removed (checkpoint 3): `tt_round` vs `ZoneRebalance`'s
  `zr_mir_lockstep` (the RO-1 idiom's text; reworded) and an in-file pair (factored into
  `tt_τ_of_lt`).
- **Semantic search per private** (`final/semantic-search.txt`): no `tt_` identifier outside
  `TwoTapes` on the tree or on the open PR heads #209, #208, #195 (fetched as `pull/N/head`).
  Ninety-odd privates state facts about this file's own definitions (the leaf, controller,
  boundary configurations, orbit, side totals), which no library declaration can state. Those whose
  statements use only library notions were posed to `exact?` (`evidence/seal/G5FillExact.lean`,
  `final/G5FillExact.out`): `exact?` closes none of `tt_card_le_of_gap`, `tt_sum_range_fin` (its Mathlib forms are not imported, below), `tt_moveInputPos_val`, the encoded-input reading of `tt_inputSymbol`, or the row-endpoint renaming of `tt_mapState_eq_cfg` (expected exit 1); the first probe, `j : Fin 2, j ≠ 0 ⊢ j = 1`, is closed by `Fin.eq_one_of_ne_zero`, and that private was removed during the fill (commit `afff3c4a`). Nearest library relatives, cited rather than restated:
  `tt_tape_rebalance` is `zoneTrackTape_rebalance_right`/`_left` with their hypotheses discharged
  from fullness; `tt_inputSymbol` is the encoded-input analogue of `Cfg.inputSymbol_congr`
  (CfgFacts; same input only); `tt_mapState_eq_cfg` is an instance of RN-1's
  `Cfg.mapState_eq_of_fields`; `tt_count` feeds `sum_cost_le_of_count`'s hypothesis and does not
  restate it. `tt_sum_range_fin` restates Mathlib's `Finset.sum_range` /
  `Fin.sum_univ_eq_sum_range`, **which are outside the import closure** (`Mathlib.Algebra.BigOperators.Fin`,
  `Mathlib.Data.Fintype.BigOperators`; probe `Scratch/Probe2`: unknown constant) — a three-line
  private, reported as an **accounting minor** for the integrator (no import may be added).
- **Inline-step sweep** (`final/inline-sweep.txt`): `Cfg.ext` once (the leaf's one-step lemma
  `tt_leaf_step`, a step against a structure literal, not a renaming); RO-1 once
  (`runFrom_succ_eq_step.trans runFrom_zero`, the leaf's one step in `tt_round`);
  `runFrom_succ_eq_step'` four times (`M`'s run one step on: `c_{r+1} = step c_r`, the published
  lemma itself); `runFrom_add` once (`tt_forward_run`: the rounds' segment, then the halting step)
  — not with `Nat.exists_eq_add_of_le`; `lt_trichotomy` twice, over zone **levels** in
  `tt_full_rebalance_*`, not over runs; no `Nat.find`, no `runFrom_of_halt`.
- Families touched: RN-1 (`Cfg.mapState_eq_of_fields`, cited in `tt_cfg_mapState`,
  `tt_mapState_eq_cfg`, `tt_cs_start`), FH-1 (`exists_first_halt`), RI-1 (its generalization
  `Segment.iterate_seq`, twice), RO-1 (one use, above). **ZP-1: not touched, and disclosed.** The
  brief asks to cite `zoneRowPre_congr`/`zoneRowPre_mapState_iff` at every phase start and redirect;
  this route never needs the precondition's independence of the state, because every phase start is
  built directly as a phase-boundary configuration `tt_cfg` at the phase's own state type (its
  precondition read off by `zoneRowPre_iff`, `tt_cfg_rowPre`) and every redirected endpoint is
  converted field by field (`tt_mapState_eq_cfg`, through `zoneRowPre_iff`). Nothing about the
  precondition's state-independence is re-derived.
- **New copies: none** (no cross-file pair; no in-file pair at 90% or more).

## 8. Promotion candidates, escalations, Implementation paragraph
- **Promotion candidate (`[Q3]`)**: the round over the zoned carrier — `tt_Fam`, the phase layout
  (`tt_Ph`, `tt_Mf`, `tt_red`), `tt_track_seg`, `tt_tracks_seg`, `tt_round` — is a simulation-step
  block over a track-step family and a finite-state leaf; a public form would serve any
  zoned-tape simulator.
- **Promotion candidate (arithmetic)**: `tt_card_le_of_gap` (sparse sets of times) and the side-total
  layer (`tt_rsum_*`) are statements about the pure zone layer and could join `Build/Zone`/`ZoneStep`.
- **Escalations: none.**
- **Proposed `**Implementation.**` paragraph** (for the maintainer, the docstring is frozen):
  > **Implementation.** `M`'s `k ≥ 1` work tapes are the tracks of one zoned tape over
  > `Turing.ZoneSym k`; a phase host runs one transition step on the home tuple and then one track
  > step per track (`Turing.exists_zoneTrackStepTM`; a stay takes no time), and the resulting
  > two-tape machine over the zone alphabet is made binary by
  > `Turing.FinTM.alphabet_reduction_run`. The count of expensive steps uses the zones' side totals:
  > after a step of index `> i` the levels below `i + 1` are half full, so two such steps are
  > `2^{i+1}` steps apart; an extension at level `ℓ` needs a head displacement of `2^ℓ − 1`, so the
  > level after `t` steps is `O(log t)`; `Turing.sum_cost_le_of_count` sums the costs. With no
  > work tapes, `M` runs beside two idle tapes (`Turing.embedEmitTM`).
  The construction follows the frozen sketch; the only departures are of bookkeeping (a zone `i` is
  rebalanced at most once every `2^{i+1}` steps, against the sketch's `2^(i-1)`; and the alphabet
  reduction is a separate last step).

## 9. Lint, size, final checks
- `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`: **0 FAIL, 72 WARN over
  92 files** (base 71): the one new WARN is `TwoTapes.lean 2464 lines > 1000` (the brief: no size
  cap, size reported; the plan's homes put the reduction in `TwoTapes`). INFO: 2 public / 102
  private.
- Policy linter `scripts/style_lint.py` on the file: 1 finding, the same size note (`2465 lines
  (> 1000, must split)`); no missing docstring or proof sketch (base: 0 findings).
- No line over 100 characters. `TwoTapes` check: exit 0, **no warning at all**
  (`final/TwoTapes-check.log`).
- File size: **2,464 lines** (base 86), against the plan's estimate of 1.2–2.2k.
