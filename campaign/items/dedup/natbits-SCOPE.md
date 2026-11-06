# NatBits re-scope (BL-1 + NB-1, with LS-3 and BL-2's lemma)

Tree: `origin/complexity/arora-barak-ch3-4` at `f4dfc3f3` (worktree
`/home/user/tcslib-scratch/wt-natbits`, branch `lean/dedup-natbits`). The Lean tree is identical
to `a28b8c42`, the tree of `replay-lcamp2` (`git diff a28b8c42 f4dfc3f3 -- TCSlib` is empty).
The plan (`campaign/items/dedup/natbits-PLAN.md`) was written at `c942799e`; since then 16 Lean
files changed (#208, #212, #213). Rulings applied: the user's of 2026-11-06 (D1–D6 defaults, one
PR, D7 Meyer sites mechanical, D8 keep binding, D9 record only).

## Canonical homes (today)

| Statement | Today | Lines |
|---|---|---|
| (iii) `Turing.length_bits_le_self` | `TuringMachine/Encoding` | 289–292 (results line 75) |
| (i) `Complexity.LogProg.length_bits_le` | `Machines/Bin` | 124–127 |
| BL-2 `Complexity.LogProg.length_bits_succ_le` (merged, #208) | `Machines/Bin` | 129–138 |
| (v) `Complexity.LogProg.two_pow_bits_le` | `Machines/Bin` | 140–151 |
| (ii) `Complexity.LogProg.length_bits_mono` | `Machines/Bin` | 153–155 |
| LS-2 conv. `Complexity.LogProg.length_bits_le_log` | `Machines/Bin` | 157–159 |
| (vi) `Complexity.LogProg.bitsVal_lt_two_pow` (stays, D4) | `Machines/Bin` | 87–91 |
| (iv) `Randomized.PolyAmp.lt_two_pow_bits` (moves, D2a) | `Randomized/SpaceAmplifyPoly` | 247–249 |
| (v) 2n+1 `Randomized.PolyAmp.two_pow_bits_le` (deleted, D2b) | `Randomized/SpaceAmplifyPoly` | 241–245 |

Not moved: `Turing.bits_two_pow_mul` / `bits_two_pow_eq_replicate` (`Encoding:294–316`). The
ruling's D6 bullet names `length_bits_succ_le` only; the shift law is not a ledger member and the
plan marks it optional. Left for the user (report).

## Site table, refreshed

Columns: line numbers at `f4dfc3f3`; "Plan" is the plan's row. All site files reach `Encoding`
(checked on the import graph), so no site needs an import edit.

| # | Site (now) | Kind | Closing today | Re-point | Owner | Open-PR overlap |
|---|---|---|---|---|---|---|
| 1 | `Diagonalization/NTimeDiagonalizer:416–424` `qy_ones_ge` | (iv) ×2 | `size_eq_bits_len` ×2, `Nat.lt_size_self` ×2 | `Complexity.LogProg.lt_two_pow_bits n`, `… D` | E-D (landed) | none (dedup-ro1, parked: disjoint) |
| 2 | same, `:426–439` `qy_two_pow_bits_le` | (v) 2n+1 with LS-3 inline | `Nat.size_le` both ways | delete; users `:3638`, `:4388`, `:4506`, `:7690` cite `two_pow_bits_le_two_mul_add_one`; docstrings `:4382`, `:4433`, `:7686` name it | same | same |
| 3 | same, `:442–449` `qy_log_bits` | LS-3 | `Nat.size_le` both ways | delete; users `:3780`, `:4453` use `(length_bits_eq_log _).symm` | same | same |
| 4 | same, `:3251–3255` `qy_bits_len_mono` | (ii) | `Nat.size_le_size` | delete; users `:3630`, `:8302` (docstring `:8266`) use `length_bits_mono` | same | same |
| 5 | same, `:3257–3260` `qy_lt_two_pow_bits` | (iv) | `Nat.lt_size_self` | delete; users `:3602`, `:3635` use `lt_two_pow_bits` | same | same |
| 6 | same, `:7677–7684` `dz_word_lt` | (vi) `ofDigits` | Mathlib `ofDigits_lt_base_pow_length` | delete; user `:7689` uses `ofDigits_lt_two_pow` | same | same |
| 7 | `Build/RecordTable:2761–2762` | (ii) | `simpa [size_eq_bits_len] using Nat.size_le_size` | `Complexity.LogProg.length_bits_mono (Nat.le_succ _)` | campaign | none |
| 8 | `Build/InputLength:417–420` ×2 | (ii) ×2 | same | `length_bits_mono` ×2 | campaign | none |
| 9 | `Build/Catalog:4123–4125` | (ii), size form | `rw [f2_counterInc_bits, size_eq_bits_len] at hcarry`; `Nat.size_le_size hi` | keep the `f2_counterInc_bits` rewrite only; `hwidth := (length_bits_mono hi).trans_eq (Nat.size_eq_bits_len _)`. **Note:** the plan's "drop the rewrite; `length_bits_mono hi`" alone does not close: the declaration's statement (`f2_counter_count_space`) is in `Nat.size x.length` form, so one Mathlib bridge equation stays. No statement change. | campaign | none (dedup-ro1: disjoint) |
| 10 | `Build/CfgRecord:242–245` `Turing.record_pos_lt` (public, kept) | (iv) | `unfold posWidth`, `size_eq_bits_len`, `lt_size_self` | `unfold posWidth` (own file), `lt_two_pow_bits _`; sketch updated | campaign | none (dedup-ro1: disjoint) |
| 11 | `CookLevin/Hardness:1127–1146` `clCount_width`; `:2252–2256` `clElapsed_width` | (i) by binary induction; (iii) through (i) | `Nat.binaryRec'` | delete `clCount_width` (only user `:2256`); `clElapsed_width := (Turing.length_bits_le_self n).trans hn`. **Blueprint consequence (not in the plan):** `blueprint/src/chapter/Complexity/CookLevin/Hardness.tex:740–746` binds `Complexity.clCount_width` and `:1230` (`clElapsed_width`'s entry) `\uses` it. The entry is removed and the `\uses` re-pointed to `Turing.length_bits_le_self` (bound at `Encoding.tex:528`); mechanical, as SG-1 did for `Tautology.tex`. | campaign | none |
| 12 | `Logspace/Mult:254–255` (`mult_product_length`) | (iv) ×2 | `simpa [size_eq_bits_len] using Nat.lt_size_self` | `lt_two_pow_bits a`, `… b` (`open LogProg` at `:51`) | campaign | none (#208 merged) |
| 13 | `Logspace/QueryReshape:188–205` `query_index_bound` | (v) native + (iv) | `Nat.size_le`, `lt_size`, `size_pos` | `r < 2^\|bits r\| ≤ 2^\|bits n\|` (`LogProg.lt_two_pow_bits`, `Nat.pow_le_pow_right`), then `LogProg.two_pow_bits_le` for `n ≠ 0`; `n = 0` apart. Sketch updated | campaign | none |
| 14 | `Randomized/UniformSample:93–101` `Randomized.le_two_pow_size_pred` (public, kept) | (v) positive branch | `Nat.lt_size`, `pow_succ'` | second conjunct: `← size_eq_bits_len`, `Complexity.LogProg.two_pow_bits_le (N-1)`; `N = 1` apart | Hydroxyi | none |
| 15 | `Codec/Word:462–468` `Complexity.Codec.bitsVal_lt_two_pow` (public) | (vi) exact copy | induction | delete (D2c). Users `Word:473`, `Deciders:141`, `Layout:218`, `Layout2:168`, `Parse:88`, `StepDecider:346`, `:375` resolve to `LogProg`'s through `open Turing LogProg` (all six files, checked) | Hydroxyi | none |
| 16 | `Randomized/QuasiPolyHierarchy:58–64` `length_bits_eq` | LS-3 (`if` form) | `Nat.size_le`, `lt_size` | delete; user `budgetSeed_eq` (`:211`) splits on `x.length = 0` and cites `length_bits_eq_log` | Hydroxyi | none |
| 17 | `SpaceComplexity/Constructible:76–83` `b3a_bits_length` | LS-3 through `logSpace` | `Nat.lt_size`, `length_bits_le_log`, `unfold logSpace` | `(LogProg.length_bits_eq_log hn).trans (logSpace_eq n).symm` (drops the `unfold` of another file's definition) | campaign | none |
| 18 | `ClassNP/ExhaustiveReplay:1807–1810` `xr_val_lt` | (vi) `ofDigits` | Mathlib | `unfold xr_val` (own file), `ofDigits_lt_two_pow w` | campaign | **#217** (NZ-1): its hunks are at `:47–60` and `:157`, disjoint |
| 19 | `Randomized/SpaceAmplifyPoly:272` (`bigK_le`) | consequence of D2b | `PolyAmp.two_pow_bits_le` | `two_pow_bits_le_two_mul_add_one n` | Hydroxyi | none |
| 20 | **new**: `SavitchARM/Deepen:777` (`dp_run`'s `hn`, private, new in #208) | (iv), `Nat.size_le.mp` form (`\|bits n\| ≤ W → n < 2^W`, as row 13's `hr`) | `Nat.size_le.mp (by rw [← size_eq_bits_len]; omega)` | `(lt_two_pow_bits _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))` (file is in `namespace Complexity.LogProg.SavitchARM`) | campaign (#208) | none (#216 touches `SavitchARM/Correct`, `Reach` only) |
| 21 | **new (missed by the plan; present at `c942799e`)**: `Build/CfgRecord:626–636` `recordStep_width_one` (private) | (iv), `Nat.lt_size.mpr` form (`2 ≤ m → 1 < \|bits m\|`) | `size_eq_bits_len`, `Nat.lt_size.mpr`, `Nat.size_one` | forward: `lt_two_pow_bits (n+1)` rewritten by the width; backward: `Nat.one_bits` | campaign | none (dedup-ro1: disjoint) |
| X1 | `CircuitComplexity/Meyer:188–189` (`lenAll_inst`) | (i) | `size_eq_bits_len`, `Nat.size_le.mpr` | `Complexity.LogProg.length_bits_le hjW` (mechanical; D7) | colleague (Hydroxyi) | none |
| X2 | `CircuitComplexity/MeyerTableau:436–437` (`bits_pad`) | (i) | same | `Complexity.LogProg.length_bits_le hj` (mechanical; D7) | colleague (Hydroxyi) | none |

Rows 20 and 21 need no statement change, no rename and no design choice: each is a private
`have`/lemma body re-pointed to the new (iv) lemma, the same reading the plan gives row 13's
`Nat.size_le.mp hwidth`. They are accounting corrections inside BL-1 (minor).

## Searches re-run, by kind (at `f4dfc3f3`)

`size_eq_bits_len` (36 hits), every `Nat.size`/`Nat.size_*`/`Nat.lt_size*`/`size_pos`/`binaryRec*`
(Lean code only), `lt_two_pow_self` within 3 lines of `bits`/`size`, `ofDigits_lt_base_pow_length`,
`pow_log_le_self`, `Nat.log 2 _ + 1 =`, and every `have … : …bits….length (≤|<|=)` not citing a
canonical lemma, plus every `… < 2 ^ (…bits…).length` and `2 ^ …bits….length ≤ 2 * …`.

New since the plan: only `SavitchARM/Deepen` (from #208): `:410` and `:777`. Missed by the plan:
`CfgRecord:626–636`.

Classified non-members (unchanged reading of the plan unless noted):
- **Citations:** `PrimeFind:469–474`, `DetMod:454`, `CodeSimulator:1446`, `RecordTable:2763`,
  `Constructible:441–444`, `ImplicitPoly:307–308`, `NARMExample:96`, `Parse:90`, `PathHard:87–93`,
  `RandomWalkPad:152–155`, `BPLInP:316`, `:399–402`, `ISCountGenCorrect:208–210`, and the
  `length_bits_mono` citations in `ARMProof:290`, `FragDec:301`, `MARMTime:506`, `ARMReach:101`,
  `ARMWidth:123`, `NARMProof:119`, `ARMRun:142`; `Hardness:2694` etc. cite `clElapsed_width`.
- **Native `Nat.size` facts** (statement or definition in `Nat.size` form): `Jacobi`, `ModPow`,
  `ISCountMath:60–68`, `RandomWalkPad:146–149`, `UniformSample:95` (first conjunct) and `:264`,
  `Catalog:4087–4185` (statement form; `:4166` a bridge), `PathHard:74` (`ell_eq_size`, a
  bridge for its own definition), `ISCountRegs:277`, `ISCountGenLoop`, `TimeConstructible:446`,
  `Programs/Light/Lib/Emod`.
- **LS-family steps:** `PathHard:78–88` (`logSpace_le_ell`), `SpaceAmplifyPoly:251–254`,
  `BPLInP:396–398`, `:438–440`, and **`Deepen:405–411` `dp_bits_logSpace`** (new; LS-2 converted
  to the bits form through `logSpace_le_size_succ`, the same idiom as `BPLInP:396`).
- **Other families:** every `binaryRec'` site other than `clCount_width` proves a value or
  increment law of `Nat.bits` (`*_bits`, `*_injective`, `inputLength_digits`), not a length bound.
- **D9 (record only, not acted on):** positivity `RecordTable:192–194`, `:4685–4687`, `:5909–5910`,
  `InputAccess:995–997`, `ISCountMath:63`; halving `ISCountMath:60`, `InputAccess:993`,
  `UPathWalk:116–117`; one width, three definitions (`posWidth`, `Codec.wP`, `PathHard.ell`);
  (vi) over other value functions (`EXP:127`, `MeyerTab:68`, `LupanovGates:132`,
  `HardFunctions:106–107`).

## Blueprint

- `Encoding.tex:528` binds `Turing.length_bits_le_self`: name unchanged, binding kept (D8).
- `Hardness.tex:740–746` (`Complexity.clCount_width`) and `:1230` (`\uses`): see row 11.
- No other deleted or moved name appears under `blueprint/src`.

## Open-PR overlaps

- #217 (NZ-1): `ClassNP/ExhaustiveReplay` (row 18), hunks disjoint.
- #214, #215, #216, #211: no file in common. (#215 touches `Robustness/SingleTape`, which
  `Encoding` imports; not edited here.)
- Parked `lean/dedup-ro1` (no PR): `Encoding` (import block, adjacent), `NTimeDiagonalizer`,
  `Catalog`, `CfgRecord`, `ExhaustiveReplay`; hunks disjoint from ours.

## Stop check

No member needs a statement change, a rename outside the plan, or a new design choice. Two
points are reported rather than decided: the `clCount_width` blueprint entry (removed, as a
mechanical consequence of the planned deletion), and the shift law left in `Encoding`.

## Addendum (after elaboration)

- **`SpaceComplexity/Machines/Frag:128` (`halfL_run`, `hrd`), not a member.** Under the new
  imports below `Encoding`/`Bin`, its bare `simp` leaves `bufferTape (…) (min ↑k ↑w.length) =
  some w[k]`. #215 (SG-1) hit the same step and pinned it (`4801588a`); that commit is
  cherry-picked verbatim (`345c6371`), so the two branches carry an identical hunk.
