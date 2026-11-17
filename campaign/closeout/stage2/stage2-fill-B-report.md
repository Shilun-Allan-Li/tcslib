# Stage 2, Fill B report: one-step windows (WS-1) and the seam space lemma (F6-1(b))

- **Base:** `closeout/stage1` at `ceece3a04a3d8896f7dcc216c252ccfed057784a`.
- **Branch:** `closeout/stage2-fill-B`.
  - The Lean patch is the single commit "Closeout stage 2, fill B: one-step windows …".
  - It touches only the 11 files FILL-B.md lists.
  - This report is a separate commit: drop it when you integrate, or keep it as the record.
- **Net Lean lines:** 115 added, 150 deleted, **net −35**.
  - B1 is −38.
  - B2 is +3.
- **New public declarations:** two, both approved in FILL-B.md:
  - `Turing.Action.apply_workTapes_of_ne`;
  - `Turing.seamCompTM_spaceUsed_le_add_ofCfg`.

  No other public statement changed. I compared every `theorem`/`lemma`/`def` header in the 11 files against the base.

## B1. WS-1: one step keeps a configuration in a window

**Published** in `TuringMachine/CfgFacts`:

```lean
theorem Action.apply_workTapes_of_ne (a : Action k Symbol State) (c : Cfg k Symbol State input)
    (i : Fin k) {z : ℤ} (hz : z ≠ c.workTapePos i) : (a.apply c).workTapes i z = c.workTapes i z
```

- The proof is `rw [Action.apply_workTapes, Function.update_of_ne hz]`, using Configuration's published field equation.
- The docstring cites [AB09, §1.2] and has a proof sketch.
- The module docstring now says "Five small facts" and lists the lemma under Main results.

**Members:**

| Member (file) | Change | Net lines |
|---|---|---|
| Oracle's private `apply_workTapes_eq_of_ne` | **deleted**; its one use (`OracleTM.workTapes_step_eq_of_ne`) cites the public lemma | −10 |
| `OracleTM.step_radius` (Oracle) | unchanged; it cites `workTapes_step_eq_of_ne`, which now rests on the public lemma | 0 |
| `inWin_mono` (ExpBFS/Radius) | proof is `h.mono hs` (`Cfg.InWindow.mono`) | −13 for the file (both members) |
| `inWin_stepWith` (ExpBFS/Radius) | `NDTM.stepWith_of_halt`/`_of_some`, then `Cfg.InWindow.mono` or `Cfg.InWindow.apply_of_lt` | (above) |
| `boundary_iff`, window half (Codec/Step) | `rw [left, right, hC.apply_iff a]`, then a two-line logical rearrangement; sketch names `apply_iff` | −24 |
| `codec_step_blank` (TQBF, private) | `MultiTapeTM.step_of_halt`/`_of_some`, then the tape half | −1 |
| `FinTM.source_bounds` (Sweep) | one-step case through `step_of_halt`/`_of_some`, `Action.apply_workTapes` and `Function.update_of_ne` | −3 |
| `dgWindow_step` (SingleTape, private) | the window shape `[a, a+n)` is kept; the step reads `Action.apply_workTapePos`/`Action.apply_workTapes` | −1 |
| `emCall_track_support` (Loop, private) | as Sweep; zero case through published equations | 0 |
| `emCall_track_extent` (Loop, private) | zero case through published equations (the step case already cited `workTapePos_step_le`) | 0 |
| `Cfg.InWindow.apply_iff` (CfgRecord) | tape-half step re-pointed to the public lemma (statement unchanged) | 0 |
| CfgFacts | the new lemma and the module docstring | +14 |

B1 total: **−38**. ExhaustiveReplay's member was left to Fill A, as the brief says.

**No import added.** Sweep, SingleTape and Loop do not import CfgFacts, even transitively. Their members therefore cite Configuration's `Action.apply_workTapes` with `Function.update_of_ne`, which is the published equation the tape half itself rests on. An import would have been a structural change the brief does not authorize.

**Rule-10 repairs in touched proofs.** There were 25 sites; the measurement estimated about 19.

- **Radius `inWin_stepWith`:**
  - `unfold NDTM.stepWith` became `NDTM.stepWith_of_halt`/`NDTM.stepWith_of_some`;
  - two `simp only [Action.apply, …]` were removed, with the window lemmas used instead.
- **Codec/Step `boundary_iff`:** four `simp only [Action.apply, …]` were replaced by `Cfg.InWindow.apply_iff`.
- **TQBF `codec_step_blank`:**
  - `simpa only [MultiTapeTM.step, …]` and `simp only [MultiTapeTM.step, hs, Action.apply]` became `MultiTapeTM.step_of_halt`/`step_of_some`;
  - `simp [Function.update, …]` became the tape half.
- **Sweep `source_bounds`:**
  - `simp [MultiTapeTM.initCfg, Cfg.init]` became `simp only [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos, Cfg.init_workTapes]` followed by `simp`;
  - `unfold MultiTapeTM.step` and `dsimp only [Action.apply]` became `step_of_*` and `Action.apply_workTapes`.
- **SingleTape `dgWindow_step`:**
  - five `simp only [Action.apply, …]` became `Action.apply_workTapePos`;
  - one `simp [Action.apply, …]` became `Action.apply_workTapes`.
- **Loop `emCall_track_extent`:** `simp [… MultiTapeTM.initCfg, Cfg.init]` became the published equations, as in Sweep.
- **Loop `emCall_track_support`:**
  - the zero case's `rfl`, which unfolded `runFrom`, `initCfg` and `Cfg.init`, became `rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq, Cfg.init_workTapes]`;
  - `unfold MultiTapeTM.step` and `dsimp only [Action.apply]` became `step_of_*` and `Action.apply_workTapes`.
- **Oracle:** the private copy's `dsimp only [Action.apply]` is gone with the copy.
- **Seam `seamCompTM_spaceUsed_le_add`:** `unfold MultiTapeTM.spaceUsed` is gone (see B2).

**Left untouched (outside the touched proofs, noted for the seals).** Each of these still reads another file's definition:

- Codec/Step's `stepWith_eq_apply` (`NDTM.stepWith`) and `cellOf_apply` (`Action.apply`). Both are in Hydroxyi's file, which was kept to minimal citations.
- SingleTape's `dgWindow_init` (`MultiTapeTM.initCfg`, `Cfg.init`).

## B2. F6-1(b): the general seam space lemma

**Published** in `Build/Seam`:

```lean
theorem seamCompTM_spaceUsed_le_add_ofCfg … (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) :
    (seamCompTM M₁ exit M₂ entry).spaceUsed (c₀.mapState Sum.inl) (T₁ + 1 + T₂) ≤
      M₁.spaceUsed c₀ T₁ + M₂.spaceUsed (c₁.mapState fun _ => entry) T₂
```

- **Proof:** for each tape, apply `Finset.card_le_card` to the public trajectory theorem `seamCompTM_visitedByTapeHead_ofCfg`, then `Finset.card_union_le`. The total is summed through the published `MultiTapeTM.spaceUsed_eq_sum` and `spaceUsedByTape_eq_card`; nothing is unfolded.
- **Phase two's endpoint is unconstrained**, so the lemma covers a genuine halt, as the B3a gate's correction requires.
- **Docstrings:** the new lemma has a statement and a proof sketch. It has no [AB09] tag, because it is construction glue, like its siblings. The module docstring lists it under Main results.
- **One declaration moved.** `seamCompTM_visitedByTapeHead_ofCfg` moved up, unchanged, to sit beside its canonical sibling `seamCompTM_visitedByTapeHead`. The new lemma and the canonical corollaries derived from it must come after it.

**Canonical corollaries:**

- **`seamCompTM_spaceUsed_le_add`** is now derived from the new lemma: `simpa only [Cfg.ofWords_mapState] using seamCompTM_spaceUsed_le_add_ofCfg …`. Its statement is unchanged, and its proof sketch is updated.
- **`seamCompTM_spaceUsedByTape_le_add`** (per tape) is **not** re-derived, because a per-tape bound does not follow from a total one. Deriving it would need a second, per-tape general lemma, which is a public declaration the brief does not list. It still projects from the canonical headline `seamCompTM_visitedByTapeHead`, unchanged. If a per-tape general twin is wanted, it is about 12 lines.
- **New warning.** The canonical total no longer uses `h₂`, so Lean reports an unused-variable warning on it. The same warning already appears on the canonical headline, the per-tape corollary and the max corollary.

**Constructible:**

- The private `b3a_seam_space` is **deleted** (22 lines).
- Its two uses (`firstLedger`, `lastLedger` in `b3a_log_machine`) cite `seamCompTM_spaceUsed_le_add_ofCfg` directly.

B2 net: Seam +25 (the move counts 15 lines on each side of the diff), Constructible −22, **total +3**.

**`b3a_cfg` through `Cfg.ofWords`: not done (stopped under rule 10).**

- The shapes agree only up to `FinTM.bufferTape_nil`, not definitionally:
  - `b3a_cfg s x w` = `{Cfg.init s x with workTapes := fun j => if j = 0 then bufferTape w else fun _ => none}`;
  - `Cfg.ofWords s (fun j => if j = 0 then w else [])` puts `bufferTape []` on the other tapes.
- Redefining `b3a_cfg` would change every proof that reads its fields: `b3a_cfg_map`, `b3a_embed_cfg`, `b3a_counter`, `b3a_overwrite`, `b3a_virtual_cfg` and the `start` step of `b3a_log_machine`.
- Once those proofs are touched, their existing reads of other files' definitions would have to be repaired.
- `b3a_virtual_cfg` reads VirtualInput's `vhostCfg` by `simp`/`rfl`, and `vhostCfg` has **no published field equations**. Rule 10 says to stop and report, so `b3a_cfg` is left as it is.
- Shorter, but also blocking: `b3a_embed_cfg` reads Embed's `embedEmitCfg` by `rfl` for the state, input head and output fields. Embed does publish simps equations for those fields (`attribute [simps …] embedEmitCfg`), so that read alone would be repairable.

## Elaboration

- **Setup:**
  - elan, toolchain `leanprover/lean4:v4.25.0`;
  - `TAR_OPTIONS=--no-same-owner lake exe cache get` narrowed to the 55 Mathlib roots of the closure, 977 files fetched (`lake exe cache get` cloned the packages itself);
  - no `lake build`.
- **Base snapshot:**
  - I built the import closure of the 11 brief files (188 modules), not the root's whole closure (886 modules) that `bootstrap-snapshot.sh` compiles. This was a scope reduction: the fill only needs these modules.
  - Each module was compiled by `scripts/lean_check_tree.sh`, in dependency order, with at most three Lean processes at once.
  - Base at `ceece3a`: **188/188, 0 errors**.
- **Fill check:**
  - Every module in that closure that depends on a changed file (**116 modules**, the 11 changed files included) was recompiled by `scripts/lean_check_tree.sh` against the base snapshot.
  - Result at the fill commit: **116/116, exit 0, 0 errors, 0 `sorry`**.
  - The 11 changed modules are TuringMachine `CfgFacts`, `Oracle`, `Sweep`, `Robustness/SingleTape`, `Build/Loop`, `Build/Seam` and `Build/CfgRecord`; SpaceComplexity `Constructible`, `Codec/Step` and `ExpBFS/Radius`; and ClassPSPACE `TQBF`.
- **New warnings:** only the unused `h₂` on `seamCompTM_spaceUsed_le_add` described in B2. The other warnings in these files are pre-existing lines.
- **Not checked here:** modules outside the brief files' import closure that import a changed module, for example `ObliviousCandidate`, which cites `FinTM.source_bounds`. No statement changed, and the only declarations removed are private, so they should be unaffected. The maintainer's merged-tree replay covers them.
