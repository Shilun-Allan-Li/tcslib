# C1 UN continuation 1 — fill delivery report (Megafill A, item 2 of 3)

**Target:** `Turing.exists_timed_universal_NDTM` (`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`).
**Status: COMPLETE.** The target is proved, modulo exactly the cited stubs: the interpreter core
`Turing.exists_ndInterpreterCore` (sorried at the base in `NDCodeSimulator`; proved on this
session's item-1 branch `fill/c1-core-cont2`, which is upstream work on its own branch and not
cited here beyond the statement) — `Complexity.ntime_hierarchy` stays sorried (C1-E's) and is not
in the target's axiom walk. The setup `P` is fully built and `un_setup` (the hypothesis of
`un_universal_of_setup`, verbatim) is proved with a **clean axiom walk** (no `sorryAx`).

- Base: `6cfee54474e3d954e3395f9d9eab5d025452a8dd` (`git rev-parse HEAD` printed it at branch
  creation; `git merge-base --is-ancestor` of the base into `complexity/arora-barak-ch3-4`
  passed at session start, per the cover brief). Branch `fill/c1-universal-cont1`, created
  2026-10-22T09:07:40Z (budget 3 h; delivered within it). No rebase, merge or cherry-pick.
- First edit: the overlay `NTimeHierarchyOverlay.lean.txt`, byte for byte (`cmp` clean,
  commit `de83b80f`). Reversal check at delivery: stripping regions (b)-additions and restoring
  target 1's `sorry` reproduces the overlay byte for byte. Nothing outside regions (b) and (c);
  region (d) is unused (the fill is complete). Imports: exactly the overlay's (rule 6).
- Checkpoint zips: none were cut — the proof landed inside the budget in one arc; the
  delivery zip is the single artifact (commits document the arc: `de83b80f` first edit,
  `cec06611` leaves, `460911e9` complete, `5824c69a` seal-robustness, then screens/wraps).

## Shared setup (megafill A, done once — quoted from the session's shared logs)

- Preflight 2026-10-22T05:11:11Z: disk available 26.5 GB (floor 12 GiB: PASS); no cgroup
  memory limit, headroom = MemAvailable = 15,975,212 kB ≈ 15.24 GiB (floor 4 GiB: PASS);
  nproc 4; no oom events (`evidence/logs/preflight.log` on `fill/c1-core-cont2`).
- Toolchain: `leanprover/lean4:v4.25.0` (elan), per the pin.
- One clone; one narrowed cache fetch for the union of the three order lists' Mathlib roots:
  41 roots, `TAR_OPTIONS=--no-same-owner lake exe cache get` → 1023/1023 files, "Completed
  successfully!", no failed download; `find .lake/packages -name '*.olean' -size 0` empty;
  root-import probe elaborated (shared `cache-get.log`, `cache-probe.log`, `mathlib-roots.txt`).
- This item's re-bootstrap (addendum Part 3 item 3.2): the full 75-module order list
  `campaign/fills/c1/orders/c1-fill-universal-cont1.txt`, after the first edit, 09:08–09:27 UTC,
  0 FAILs (`evidence/logs/item2-bootstrap.log`); the base's 26 sorry warnings in 12 modules
  reproduced (`c1-fill-universal-cont1-base-sorries.txt`), mine among them.

## The setup machine, as built

**Tape layout** (`k := K + kC + 1`): the core's `K` tapes under `ι := castSucc ∘ castAdd kC`
(so `ι jR` is the stream tape), the embedded header composite's `kC` tapes under
`ιC := castSucc ∘ natAdd K`, and `cap := Fin.last (K + kC)` — the capture tape, which is also
the expansion's counter tape (`expandTM` counts on the last tape). Here
`kC := (bufferedCompTM universalPrefixTM F).k` with `F := FinTM.pairExtractTM true false`,
read only through `FinTM.bufferedCompTM_k` and `universalPrefixTM_k` as
`kC = universalPrefixTM.k + (1 + F.k)`; **`F.k` is left abstract throughout** (see rule 10
below). Inside the composite, the code buffer is coordinate `natAdd universalPrefixTM.k
(castAdd F.k 0)` (val 0) and the extractor bank `natAdd universalPrefixTM.k (natAdd 1 e)`
(val `1 + e`), both transported by `Fin.cast` along `bufferedCompTM_k`; their images are
`iBuf` (val `K`) and the bank `Sx` (vals `K + 1 + e`).

**Phases**, seam-composed left-nested (`seamCompTM`), with `P := { chain with q₀ := the
nested-inl entry }` so that `MultiTapeTM.initCfg_with_q₀` / `runFrom_with_q₀` give the start:

| # | machine | what it does | exact time |
|---|---|---|---|
| A1 | `embedSilentRetTM ιC cap MC.tm` | the header pass: the composite `bufferedCompTM universalPrefixTM F` runs embedded and silent; its first halt (at exactly `3|u|+4+(4|bt|+5)`, `un_canon_halt`) lands in the live return anchor with the output `bits t` captured on `cap` | `3|u|+4+4|bt|+5` |
| A2 | `rewindTM k iBuf` | code-buffer head `2|bt|+2 → 0` | `2|bt|+4` |
| A3 | `clearTM k iBuf` | blank the code buffer's word `u` | `2|u|+2` |
| A4 | `un_bankTM k Sx cap` | the guided bank erase: blanks every extractor tape while the guide (`cap`) head travels with the bank; leaves `cap`'s word intact with its head at the origin — the capture rewind for free | `|bt|+2` |
| A5 | `expandTM (K+kC) iBlkb [true]` | the expansion: counter `bits t` on `cap` (value `t` by `counterValue_bits`), writes the `t`-cell block on `ι jR`; counter left all-`true` at width `|bt|`, head back at the origin | `2t + counterOverhead bt (t+1)` |
| A6 | `rewindTM k (ι jR)` | block head `t → 0` | `t+2` |
| A7 | `clearTM k cap` | blank the all-`true` counter word | `2|bt|+2` |
| A8 | `un_inRewTM k` | the input rewind: input head `2|u|+3 → 1` | `2|u|+4` |

`pexit := Sum.inr 2` (A8's park). Exit configuration: exactly the hypothesis's
`⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩` with
`blk := FinTM.bufferTape (List.replicate t true)` (`blk p ≠ none ↔ 0 ≤ p < t` proved from
`bufferTape_nat`/`bufferTape_of_neg`/`length_replicate`). First exit: every phase's framed run
carries a first-visit cut, inherited seam by seam (`seamCompTM_firstReturn_ofCfg` via
`un_step`/`un_step'`).

**The ledger.** `TP = Σ Tᵢ + 7 ≤ 25|bt| + 7|α| + 7t + 48 + (counterOverhead ≤ 4t + 2|bt| + 2
by counterOverhead_le)`, and `|bt| ≤ t` (`length_bits_le_self`), so `TP ≤ 32t + 7|α| + 50 ≤
CP·(t+1)` with **`CP := 7·|α| + 130`** — no `|x|` term (the header pass never reads past the
header; the input rewind costs `2|u|+4`, and `|u| = 2|bt|+2+|α|` by `length_pairEncode`).
Edge cases hold uniformly: `t = 0` (`bits 0 = []`, empty block, `blk` everywhere blank),
`x = []` (A8's unconditional first left step handles the right-sentinel start), `α = []`
(the buffer head starts just past the word; `rewindTM_run_ofCfg` allows `n = |word|`).
**Target 1's constant: `C = CP + CR + 13`** per `un_universal_of_setup`.

## New declarations (all `private`, prefix `un_`, home (b))

| name | role |
|---|---|
| `un_flatten` | `(replicate t [true]).flatten = replicate t true` |
| `un_buffer_ge` | a buffered word is blank at and beyond its length |
| `un_step` | one seam step: run + exit state + inherited first-visit cut |
| `un_canon_halt` | the header composite's exact first halt at `3|u|+4+(4|a|+5)`, live before, uniformly in the suffix |
| `un_bankAct` / `un_bankAct_eq` | the bank erase's action and its two work-tape component equations |
| `un_bankTM` / `un_bank_run` | the guided bank-erase leaf and its framed run (exact time `L+2`, cut) |
| `un_inRewTM` / `un_inRew_run` | the input-rewind leaf (from `FinTM.controlAction`) and its framed run (exact time `p+1`, cut) |
| `un_mapState_comp` | a constant relabeling collapses any previous relabeling |
| `un_step'` | `un_step` at a right-tagged handover (the chain's shape) |
| `un_setup` | **the setup**: the hypothesis of `un_universal_of_setup`, verbatim, proved |

Target 1's body is one line: `exact un_universal_of_setup c un_setup`.

## Rule 10 (the pinned base; no unfolding)

- **Cited outside the file** (all public at the base): `prefixCanon_run`, `prefixCanon_start`,
  `prefixCanonTM_eq`, `FinTM.pairExtractTM_fst_run`, `FinTM.bufferedCompTM_k`,
  `universalPrefixTM_k`, `FinTM.bufferedSecondCfg_state/_inputPos/_output`,
  `FinTM.bufferedSecondCfg_workTapes_cast`/`_workTapePos_cast`,
  `FinTM.tapeBlocks_buffer`/`_right`, `embedSilentRetTM_run`,
  `embedSilentCfg_state/_inputPos/_output/_selected_tape/_selected_pos/_cap/_unselected`,
  `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `rewindTM_run_ofCfg`,
  `clearTM_run_ofCfg`, `expandTM_run_ofCfg`, `counter_cfg_eq`, `counterValue_eq`,
  `counterValue_bits`, `counterOverhead_le`, `FinTM.controlAction`, `FinTM.controlAction_apply`,
  `FinTM.bufferTape_nat/_nil/_of_neg`, `MultiTapeTM.initCfg_eq`,
  `MultiTapeTM.initCfg_with_q₀`, `MultiTapeTM.runFrom_with_q₀`,
  `MultiTapeTM.runFrom_zero/_succ_eq_step'/_state_ne_none_of_le`, `MultiTapeTM.step_of_some`,
  `Cfg.init_*`, `Cfg.mapState_*`, `Action.apply_*` (incl. `Action.apply_workTapes`),
  `Cfg.workTapeSymbols_eq`, `Cfg.inputSymbol_of_zero`, `inputSymbolInner`,
  `moveInputPos_zero/_neg_of_ne_left/_pos_of_ne_right`, `length_pairEncode`,
  `length_bits_le_self`; machine and type names (`seamCompTM`, `embedSilentRetTM`, `rewindTM`,
  `clearTM`, `expandTM`, `prefixCanonTM`, `FinTM.bufferedCompTM`, `FinTM.pairExtractTM`,
  `universalPrefixTM`, `SweepPhase`, `RewindPhase`, `CounterLoopState`, `FlagPhase`) are used
  by name only; plus `un_universal_of_setup` (this file's own private) and standard
  Mathlib/core lemmas.
- **The `F.k` gap, resolved without new API.** `pairExtractTM` has **no published tape-count
  equation**, so the extractor's tape count is left abstract everywhere: the layout carries the
  composite's `kC` as a single abstract block, the composite's final configuration is read only
  through the cast pair and the `tapeBlocks` projections (the two coordinates needed — the
  buffer and the `natAdd 1`-bank — are written in `natAdd`/`castAdd` form, so no enumeration of
  `F.k` is ever needed), and the scratch cleanup erases the whole extractor bank **uniformly**
  with the guided bank-erase leaf (`Finset`-selected tapes, the guide's word as the ruler)
  instead of one `clearTM` per tape. The frames of `prefixCanon_run`'s statement
  (`fun i => i.elim0`) are **generalized on obtaining** the fact (an `∃ fr1 fr2` wrapper), so
  the proof never re-elaborates them against `universalPrefixTM.k ≡ 0`.
- **Seal test** (`evidence/logs/item2-seal.log`): the whole file elaborates with 28 other-file
  definitions `local irreducible` around the new region (`pairEncode`, `FinTM.bufferTape`,
  `Cfg.mapState`, `embedSilentCfg`, `MultiTapeTM.initCfg/runFrom/step`, `Action.apply`,
  `Cfg.init`, `bufferedSecondCfg`, `bufferedCompTM`, `seamCompTM`, `embedSilentRetTM`,
  `rewindTM`, `clearTM`, `expandTM`, `counterLoopCfg`, `counterValue`, `counterOverhead`,
  `prefixCanonTM`, `universalPrefixTM`, `pairExtractTM`, `controlAction`, `tapeBlocks`,
  `moveInputPos`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `Cfg.ofWords`): exit 0, 0 errors.
  **Control**: `example : pairEncode [] [] = [false, true] := rfl` inside the sealed section
  fails (`item2-seal-control.log`, 1 error) and passes unsealed — the seal bites. The seal
  found three fragile steps during development (an `Option.map_some` rewrite, an
  `Option.map_eq_none_iff` use, and the `elim0`-frame re-elaboration); all three were repaired
  before delivery (commit `5824c69a`), and the delivered file passes sealed.
- **Inspection of every `rw`/`simp`/`simpa`/`unfold` argument:** no `unfold` is used; every
  `rw`/`simp only` argument naming another file is a published theorem; the only definitions
  passed to `simp` are this file's own (`un_bankAct`, `un_bankTM`, `un_inRewTM`) and local
  `let`s; `dsimp only` is used without arguments (beta/iota only).
- **Import probe:** re-run after delivery, 95 checks, 0 errors, 0 warnings
  (`evidence/logs/item2-probe.log`).
- **Deviation note (route refinement):** the brief's cleanup list names `FinTM.rewind_heads`
  for the input rewind; `rewind_heads` gives an existential time and no first-visit cut, which
  the seam chain's final anchor needs. The leaf is built exactly from `FinTM.controlAction`
  (as prescribed) and its framed run is proved directly (`un_inRew_run`: exact time and cut),
  citing `controlAction_apply`; `rewind_heads` itself is therefore not cited. Likewise the
  buffer-head normalization uses the brief's sanctioned `rewindTM_run_ofCfg` alternative
  rather than `skipTM`/`skipBackTM`.

## Rule 11 (MIG-1)

- None of the R3 canonical rows is cited (grep over `rewindTM_run`, `clearTM_run`,
  `copyTM_run`, `transferTM_run`, `skipTM_run`, `skipBackTM_run`, `expandTM_run`,
  `compareTM_run`, `incrementTM_run` as bare `_run` forms: 0 hits — only `_ofCfg` forms).
- No private declaration of another file is cited (grep over `ic_`, `xr_`, `ss_`, `iw_`,
  `em_` prefixes: 0 hits).
- Every new private is `un_`-prefixed.

## Duplication governance (copy-text screen v3, one at a time, `nice -n 10`)

- **Before** (after the first edit; `evidence/logs/item2-screen-before.log`):
  `declarations screened: 603; copy pairs (target reproduces >= half of source): 450;
  reproduced text: 123,003 chars` — **equal to the base**
  (`c1-fill-universal-cont1-screen-base.txt`).
- **After** (`evidence/logs/item2-screen-after.log`): `declarations screened: 616; copy
  pairs: 454; reproduced text: 123,797 chars`.
- **New pairs: 4, none at 90% or more; new copies: none.** Each, justified:
  - `ExhaustiveReplay::xr_inRewindTM ↔ NTimeHierarchy::un_inRewTM` (61%/59%, cross-file,
    owned side): both are the canonical three-state input-rewind leaf (unconditional left,
    scan-left-while-some, park) that rule 7 explicitly allows this fill to build
    ("the input-rewind leaf is allowed"); the resemblance is the shape of the leaf, not a
    transcription — different state type (`Fin 3` vs `xr_St`), different action helper
    (`controlAction` vs `xr_act`), different park discipline. Flagged for the maintainer as
    a promotion candidate (below), which would collapse both.
  - `ExhaustiveReplay::xr_E_initCfg ↔ NTimeHierarchy::un_mapState_comp` (54%, cross-file,
    owned side): both are five-field `Cfg.ext`s over the published `Cfg.mapState_*`
    equations — the API's spelling, no shared logic.
  - `NTimeHierarchy::un_setup ↔ NTimeHierarchy::un_mapState_comp` (87%, in-file): the
    assembly's start identification (`hstart`) repeats the same `Cfg.mapState_*` rewrite
    litany the helper packages; in-file, both mine.
  (During development the twin component lemmas `un_bankAct_wr`/`un_bankAct_mv` screened at
  100% and were merged into the single `un_bankAct_eq` before delivery; the delivered screen
  carries no pair at 90% or more.)

## Verification

- **Owned file:** 0 errors; exactly one sorry warning — `ntime_hierarchy` (C1-E's, frozen).
- **Final sweep:** the full 75-module order list, in order, 10:44-10:57 UTC
  (`evidence/logs/item2-final-sweep.log`): **0 FAILs, 0 errors, exactly 25 sorry warnings**
  — the base's 26 minus target 1. Tail quoted in `SWEEP-TAIL.txt`; the per-module sorry
  accounting in `SORRY-DIFF.txt`.
- **Axioms** (`evidence/logs/item2-axioms.log`):
  - `Turing.exists_timed_universal_NDTM`: `[propext, sorryAx, Classical.choice, Quot.sound]`
    — the `sorryAx` enters only through the cited stub `exists_ndInterpreterCore`;
  - `un_setup` and **every** new private: within `[propext, Classical.choice, Quot.sound]`,
    **no `sorryAx`**.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`:
  **`0 FAIL, 2 WARN over 5 files`** (`evidence/logs/item2-lint.log`). The base's EXPCOM WARN
  is unchanged; the second WARN is new and disclosed: `NTimeHierarchy.lean 1905 lines > 1000:
  policy requires a split or a recorded justification`. Justification, recorded here: the
  growth is the fill's proof mass in the authorized home (b) (rule 8: no cap; file size alone
  is not a driver); a split is an integration decision for the maintainer (the setup machine
  and its leaves are the natural split line, see the promotion candidates). No new line over
  100 characters (the one line over 100 is the overlay's own, line 118).
- **Import probe:** re-run after delivery (`evidence/logs/item2-probe.log`): 95 checks,
  exit 0, 0 errors, 0 warnings.
- **File size:** 1,905 lines; 5 public (unchanged), 14 private declarations (the overlay's
  `un_universal_of_setup` plus this fill's 13).

## Promotion candidates (notes only)

- The header's first-component pass **with its cleanup** (A1–A4 as a bundle): R's startup and
  B5a's H1 need the same capture-normalize-erase prologue.
- The guided bank erase (`un_bankTM`/`un_bank_run`): generic in the selected `Finset` and the
  guide; it erases any uniform-width bank in `L + 2` steps and doubles as the guide's rewind —
  it is also what makes the build independent of the extractor's unpublished tape count.
- The input-rewind leaf **with its first-visit cut** (`un_inRewTM`/`un_inRew_run`): the cut is
  what `FinTM.rewind_heads` lacks and what every seam consumer needs; promoting it would also
  collapse the `xr_inRewindTM` pair above.
- The seam-step composers (`un_step`/`un_step'`): the "run + exit + cut" package every chained
  fill rebuilds.

## Escalations

None.
