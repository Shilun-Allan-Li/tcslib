/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Zone
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the multi-track zoned carrier (§13d G3)

The physical representation of the Hennie–Stearns simulation ([AB09] §1.7) over a rich alphabet
(`machine-library-design.md` §13d, G3; decisions 13d.1 and 13d.5): `k` tracks of zone contents
(`Turing.ZoneContents`, the per-track pure layer of `Build/Zone`, reused verbatim) on **one**
work tape over `Turing.ZoneSym k := Bool ⊕ Turing.ZoneCell k`. One physical cell holds one
virtual slot of every track; the home, at cell `0`, holds every track's virtual symbol under its
head, so the simulator reads and writes all `k` virtual heads in one step.

**Status: proved.** Every declaration of the module is proved.

## Design

* **The layout** (decision 13d.1). One blank separator precedes each zone: the right zone `i`
  occupies `[zoneStart i, zoneStart i + zoneCapacity i)` with `zoneStart i = zoneBase i + i + 2
  = 2^(i+1) + i`, and the left zone `i` the mirror image. Each zone is therefore a delimited
  nonblank word (`Turing.zonedTape_right_word`, `Turing.zonedTape_left_word`), so the framed
  sweeps of `Build/Catalog` (the scan, and the G2 mapped sweeps) run on a zone with no save and
  restore, and the separators mark the zone boundaries, so no counter is needed.
* **Inner packing.** In each zone, track `t`'s stored cells occupy the innermost slots and the
  rest hold `⊠`: a zone is empty on a track exactly when its innermost slot is `⊠`, and full
  exactly when its outermost slot is occupied. The book leaves the placement of `⊠` free.
* **Per-track access** is `Turing.zoneSlotOf` (read a slot) and `Turing.zoneSlotSet` (write a
  slot, keeping the other tracks): the `extract` and `merge` of the per-track mapped sweeps.
* **The carrier is an encoding**, `Turing.zonedTape`, faithful (`Turing.zonedTape_injective`).
  The fullness invariant is not part of it; it is the Hennie–Stearns consumer's (§13d, G5).

## Main definitions

* `Turing.ZoneCell`, `Turing.ZoneSym`: the alphabet; `Turing.zoneSlotOf`, `Turing.zoneSlotSet`.
* `Turing.zoneStart`, `Turing.zoneOwner`: the layout.
* `Turing.zoneCells`, `Turing.zoneCellAt`, `Turing.zonedTape`: the carrier.

## Main results

* `Turing.zonedTape_zero`, `Turing.zonedTape_right`, `Turing.zonedTape_left`: the cells.
* `Turing.zonedTape_right_sep`, `Turing.zonedTape_left_sep`, `Turing.zonedTape_blank_outside`:
  the blanks.
* `Turing.zonedTape_right_word`, `Turing.zonedTape_left_word`: zones are delimited words.
* `Turing.zonedTape_update_slot`, `Turing.zonedTape_isSome`: track independence and a
  contents-independent layout.
* `Turing.zonedTape_homeWrite`, `Turing.zonedTape_extend`: what the home write and the extension
  change.
* `Turing.zonedTape_injective`: the encoding is faithful.
* The specification API (user, 2026-10-16), the definitions as equations:
  `Turing.zoneSlotOf_inl`/`_inr`, `Turing.zoneCellOfCell_inr`/`_inl`/`_none`,
  `Turing.zoneSlotSet_eq`, `Turing.zoneOwner_eq`, `Turing.zoneCells_eq`, `Turing.zoneCellAt_eq`,
  `Turing.zonedTape_of_pos`/`_of_neg`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009. (§1.7, the Hennie–Stearns simulation; Claim 1.5, the alphabet reduction that
  finishes a machine over `Turing.ZoneSym k`.)
-/

namespace Turing

/-! ### The alphabet -/

/-- **A zone cell** (design §13d, G3; decision 13d.5): one slot per track. In track `t`'s slot,
`none` is the buffer symbol `⊠` (an unoccupied slot) and `some v` an occupied slot storing the
virtual symbol `v`, where `v = none` is the virtual blank. [AB09, §1.7]: the tape alphabet
`Γ^k` of the parallel tracks, with the buffer symbol `⊠`. -/
abbrev ZoneCell (k : ℕ) : Type := Fin k → Option (Option Bool)

/-- **The simulator's alphabet** (decision 13d.5): a binary symbol (`Sum.inl`, the input and
output alphabet that `Turing.FinTM.ComputesFunInTimeVia`'s embedding uses) or a zone cell
(`Sum.inr`). It is finite and has decidable equality, so a machine over it is a `FinTM`, and
`Turing.FinTM.alphabet_reduction` turns it into a binary machine. [AB09, §1.7, with Claim 1.5
for the alphabet reduction] -/
abbrev ZoneSym (k : ℕ) : Type := Bool ⊕ ZoneCell k

/-- Track `t`'s slot of a physical symbol: the slot of a zone cell; `⊠` for a binary symbol.
This is the `extract` of the per-track mapped sweeps (design §13d, G2). -/
def zoneSlotOf {k : ℕ} (t : Fin k) : ZoneSym k → Option (Option Bool)
  | .inl _ => none
  | .inr c => c t

/-- A binary symbol has `⊠` in every track's slot: `zoneSlotOf t (.inl b) = none`
(the specification API, user 2026-10-16). -/
theorem zoneSlotOf_inl {k : ℕ} (t : Fin k) (b : Bool) : zoneSlotOf t (.inl b) = none :=
  rfl

/-- A zone cell's track-`t` slot is its `t`-th entry: `zoneSlotOf t (.inr c) = c t`
(the specification API, user 2026-10-16). -/
theorem zoneSlotOf_inr {k : ℕ} (t : Fin k) (c : ZoneCell k) : zoneSlotOf t (.inr c) = c t :=
  rfl

/-- The zone cell a physical cell holds: its cell if it holds one, all `⊠` otherwise (a blank
or a binary cell). -/
def zoneCellOfCell {k : ℕ} : Option (ZoneSym k) → ZoneCell k
  | some (.inr c) => c
  | _ => fun _ => none

/-- A physical cell holding a zone cell gives that cell: `zoneCellOfCell (some (.inr c)) = c`
(the specification API, user 2026-10-16). -/
theorem zoneCellOfCell_inr {k : ℕ} (c : ZoneCell k) : zoneCellOfCell (some (.inr c)) = c :=
  rfl

/-- A physical cell holding a binary symbol gives the all-`⊠` cell:
`zoneCellOfCell (some (.inl b)) = fun _ => none` (the specification API, user 2026-10-16). -/
theorem zoneCellOfCell_inl {k : ℕ} (b : Bool) :
    zoneCellOfCell (k := k) (some (.inl b)) = fun _ => none :=
  rfl

/-- A blank physical cell gives the all-`⊠` cell: `zoneCellOfCell none = fun _ => none`
(the specification API, user 2026-10-16). -/
theorem zoneCellOfCell_none {k : ℕ} : zoneCellOfCell (k := k) none = fun _ => none :=
  rfl

/-- Overwrite track `t`'s slot of a physical cell, keeping its other tracks; a blank or binary
cell is read as all `⊠` first. This is the `merge` of the per-track mapped sweeps (design §13d,
G2; `merge : Option Γ → Δ → Γ`, so that blank destinations are admitted). -/
def zoneSlotSet {k : ℕ} (t : Fin k) (cell : Option (ZoneSym k)) (s : Option (Option Bool)) :
    ZoneSym k :=
  .inr (Function.update (zoneCellOfCell cell) t s)

/-- Setting track `t`'s slot to `s` gives the zone cell of the old cell updated at `t`:
`zoneSlotSet t cell s = .inr (Function.update (zoneCellOfCell cell) t s)`
(the specification API, user 2026-10-16). -/
theorem zoneSlotSet_eq {k : ℕ} (t : Fin k) (cell : Option (ZoneSym k)) (s : Option (Option Bool)) :
    zoneSlotSet t cell s = .inr (Function.update (zoneCellOfCell cell) t s) :=
  rfl

/-- Setting a track's slot sets that slot. -/
@[simp] theorem zoneSlotOf_slotSet_self {k : ℕ} (t : Fin k) (cell : Option (ZoneSym k))
    (s : Option (Option Bool)) : zoneSlotOf t (zoneSlotSet t cell s) = s := by
  simp [zoneSlotOf, zoneSlotSet]

/-- Setting a track's slot keeps every other track's slot of a zone cell. -/
theorem zoneSlotOf_slotSet_ne {k : ℕ} {s t : Fin k} (h : s ≠ t) (c : ZoneCell k)
    (v : Option (Option Bool)) :
    zoneSlotOf s (zoneSlotSet t (some (.inr c)) v) = c s := by
  simp [zoneSlotOf, zoneSlotSet, zoneCellOfCell, Function.update_of_ne h]

/-! ### The layout -/

/-- **The first physical cell of zone `i`**, on the right; the left zone `i` starts at
`-zoneStart i`. Home is cell `0`, and one blank separator precedes each zone (decision 13d.1):
`zoneStart i = zoneBase i + i + 2`, the `i + 1` separators and the inner zones' cells beyond
the home. -/
def zoneStart (i : ℕ) : ℕ := zoneBase i + i + 2

/-- Consecutive zones are one separator apart. -/
theorem zoneStart_succ (i : ℕ) : zoneStart (i + 1) = zoneStart i + zoneCapacity i + 1 := by
  rw [zoneStart, zoneStart, zoneBase_succ]
  omega

/-- The closed form `zoneStart i = 2^(i+1) + i`. -/
theorem zoneStart_eq (i : ℕ) : zoneStart i = 2 ^ (i + 1) + i := by
  have h := Nat.two_pow_pos i
  simp only [zoneStart, zoneBase, pow_succ]
  omega

/-- A zone ends, with its trailing separator, before any later zone starts. -/
theorem zoneStart_add_lt {i j : ℕ} (h : i < j) : zoneStart i + zoneCapacity i < zoneStart j := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show i + 1 ≤ j by omega)
  rw [zoneStart_eq, zoneStart_eq]
  simp only [zoneCapacity, pow_succ] at *
  omega

/-- Zone starts are monotone. -/
theorem zoneStart_mono {i j : ℕ} (h : i ≤ j) : zoneStart i ≤ zoneStart j := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · have := zoneStart_add_lt h
    omega

/-- Every zone starts at least two cells from home. -/
theorem two_le_zoneStart (i : ℕ) : 2 ≤ zoneStart i := by
  unfold zoneStart
  omega

/-- The laid-out zone owning physical distance `n` from home, if any: the unique `i < ℓ` with
`zoneStart i ≤ n < zoneStart i + zoneCapacity i`. Home, separators and cells beyond the layout
have no owner. -/
def zoneOwner (ℓ n : ℕ) : Option (Fin ℓ) :=
  Fin.find fun i : Fin ℓ => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i

/-- The owner of distance `n` is the first laid-out zone whose cells contain `n`:
`zoneOwner ℓ n = Fin.find (fun i => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i)`
(the specification API, user 2026-10-16). -/
theorem zoneOwner_eq (ℓ n : ℕ) :
    zoneOwner ℓ n = Fin.find fun i : Fin ℓ => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i :=
  rfl

/-- A cell inside a laid-out zone is owned by that zone.

**Proof sketch.** `Fin.find_eq_some_iff`; minimality holds because another owner `j` would
overlap zone `i`, which `Turing.zoneStart_add_lt` excludes in either order. -/
theorem zoneOwner_of_mem {ℓ : ℕ} (i : Fin ℓ) {n : ℕ} (h₁ : zoneStart i ≤ n)
    (h₂ : n < zoneStart i + zoneCapacity i) : zoneOwner ℓ n = some i := by
  rw [zoneOwner, Fin.find_eq_some_iff]
  refine ⟨⟨h₁, h₂⟩, fun j hj => ?_⟩
  by_contra hlt
  have := zoneStart_add_lt (show j.val < i.val by omega)
  omega

/-- A cell owned by no laid-out zone has no owner. -/
theorem zoneOwner_of_not_mem {ℓ n : ℕ}
    (h : ∀ i : Fin ℓ, ¬ (zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i)) :
    zoneOwner ℓ n = none :=
  Fin.find_eq_none_iff.mpr h

/-- The separator before zone `i` (any `i`, laid out or not) has no owner.

**Proof sketch.** A zone `j < i` ends before it (`Turing.zoneStart_succ`,
`Turing.zoneStart_mono`); a zone `j ≥ i` starts after it. -/
theorem zoneOwner_sep (ℓ i : ℕ) : zoneOwner ℓ (zoneStart i - 1) = none := by
  apply zoneOwner_of_not_mem
  intro j ⟨h₁, h₂⟩
  have h2 := two_le_zoneStart i
  rcases Nat.lt_or_ge j.val i with hj | hj
  · have := zoneStart_mono (show j.val + 1 ≤ i by omega)
    have := zoneStart_succ j.val
    omega
  · have := zoneStart_mono hj
    omega

/-- Past the last laid-out zone nothing has an owner. -/
theorem zoneOwner_beyond {ℓ n : ℕ} (h : zoneStart ℓ - 1 ≤ n) : zoneOwner ℓ n = none := by
  apply zoneOwner_of_not_mem
  intro j ⟨_, h₂⟩
  have := zoneStart_mono (show j.val + 1 ≤ ℓ by omega)
  have := zoneStart_succ j.val
  omega

/-! ### The carrier -/

/-- **The physical cells of zone `i` on one side** (`side = true` the right), inner end first:
cell `p` holds, in track `t`'s slot, the `p`-th stored cell of track `t`'s zone word, or `⊠`
beyond its length. Stored cells are thus **packed at the inner end** of each zone, so a zone is
empty on a track exactly when its innermost slot is `⊠`. Every cell is a zone cell, hence
nonblank: each zone is a nonblank word of length `zoneCapacity i`. -/
def zoneCells {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) :
    List (ZoneSym k) :=
  (List.range (zoneCapacity i)).map fun p => .inr fun t => ((z t).words side i)[p]?

/-- Zone `i`'s cells are its `zoneCapacity i` offsets, offset `p` holding in track `t`'s slot
cell `p` of that track's zone word, or `⊠` beyond it:
`zoneCells side z i = (List.range (zoneCapacity i)).map (fun p => .inr fun t => …[p]?)`
(the specification API, user 2026-10-16). -/
theorem zoneCells_eq {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) :
    zoneCells side z i =
      (List.range (zoneCapacity i)).map fun p => .inr fun t => ((z t).words side i)[p]? :=
  rfl

/-- The cell at distance `n ≥ 1` from home on one side: the matching zone cell when a laid-out
zone owns it, blank otherwise (a separator, or beyond the layout). -/
def zoneCellAt {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (n : ℕ) :
    Option (ZoneSym k) :=
  (zoneOwner ℓ n).map fun i => .inr fun t => ((z t).words side i)[n - zoneStart i]?

/-- The cell at distance `n` is, for its owner `i`, the zone cell holding in track `t`'s slot
cell `n - zoneStart i` of that track's zone word, and blank without an owner:
`zoneCellAt side z n = (zoneOwner ℓ n).map (fun i => .inr fun t => …[n - zoneStart i]?)`
(the specification API, user 2026-10-16). -/
theorem zoneCellAt_eq {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (n : ℕ) :
    zoneCellAt side z n =
      (zoneOwner ℓ n).map fun i => .inr fun t => ((z t).words side i)[n - zoneStart i]? :=
  rfl

/-- **The zoned tape** (design §13d, G3): the physical work tape that represents `k` tracks of
zone contents on `ℓ` laid-out levels. Cell `0` is the home, holding every track's virtual
symbol under its head; the right zone `i` occupies `[zoneStart i, zoneStart i + zoneCapacity i)`
and the left zone `i` the mirror image, each holding `Turing.zoneCells`; every other cell is
blank (the separators, one before each zone, and everything beyond the layout). [AB09, §1.7]:
the zones `L_i`, `R_i` of the single work tape, with the tracks in parallel. Deviations: one
blank separator between zones (decision 13d.1, so that zones are delimited words); stored cells
packed at each zone's inner end (the book leaves the placement of `⊠` free). -/
def zonedTape {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (c : ℤ) : Option (ZoneSym k) :=
  if c = 0 then some (.inr fun t => some (z t).home)
  else if 0 < c then zoneCellAt true z c.toNat
  else zoneCellAt false z (-c).toNat

/-- A positive cell of the zoned tape is the right side's cell at that distance:
`zonedTape z c = zoneCellAt true z c.toNat` when `0 < c`
(the specification API, user 2026-10-16). -/
theorem zonedTape_of_pos {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) {c : ℤ} (hc : 0 < c) :
    zonedTape z c = zoneCellAt true z c.toNat := by
  simp only [zonedTape, if_neg (show c ≠ 0 by omega), if_pos hc]

/-- A negative cell of the zoned tape is the left side's cell at that distance:
`zonedTape z c = zoneCellAt false z (-c).toNat` when `c < 0`
(the specification API, user 2026-10-16). -/
theorem zonedTape_of_neg {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) {c : ℤ} (hc : c < 0) :
    zonedTape z c = zoneCellAt false z (-c).toNat := by
  simp only [zonedTape, if_neg (show c ≠ 0 by omega), if_neg (show ¬ 0 < c by omega)]

/-- A zone has exactly `zoneCapacity i` cells. -/
@[simp] theorem zoneCells_length {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (i : Fin ℓ) : (zoneCells side z i).length = zoneCapacity i := by
  simp [zoneCells]

/-- The home cell holds every track's virtual symbol. -/
@[simp] theorem zonedTape_zero {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) :
    zonedTape z 0 = some (.inr fun t => some (z t).home) := by
  simp [zonedTape]

/-- A right zone cell holds the zone words' cells at its offset.

**Proof sketch.** The cell is positive and owned by zone `i` (`Turing.zoneOwner_of_mem`). -/
theorem zonedTape_right {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) (p : ℕ)
    (hp : p < zoneCapacity i) :
    zonedTape z ((zoneStart i + p : ℕ) : ℤ) =
      some (.inr fun t => ((z t).words true i)[p]?) := by
  have h2 := two_le_zoneStart i
  have ho := zoneOwner_of_mem (ℓ := ℓ) i (n := zoneStart i + p) (by omega) (by omega)
  simp only [zonedTape, zoneCellAt]
  rw [if_neg (by omega), if_pos (by omega), Int.toNat_natCast, ho]
  simp

/-- A left zone cell holds the zone words' cells at its offset. -/
theorem zonedTape_left {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) (p : ℕ)
    (hp : p < zoneCapacity i) :
    zonedTape z (-((zoneStart i + p : ℕ) : ℤ)) =
      some (.inr fun t => ((z t).words false i)[p]?) := by
  have h2 := two_le_zoneStart i
  have ho := zoneOwner_of_mem (ℓ := ℓ) i (n := zoneStart i + p) (by omega) (by omega)
  simp only [zonedTape, zoneCellAt]
  rw [if_neg (by omega), if_neg (by omega), neg_neg, Int.toNat_natCast, ho]
  simp

/-- The right separator before zone `i` is blank, for every `i` (laid out or not). -/
theorem zonedTape_right_sep {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : ℕ) :
    zonedTape z ((zoneStart i : ℤ) - 1) = none := by
  have h2 := two_le_zoneStart i
  simp only [zonedTape, zoneCellAt]
  rw [if_neg (by omega), if_pos (by omega), show ((zoneStart i : ℤ) - 1).toNat =
    zoneStart i - 1 by omega, zoneOwner_sep]
  rfl

/-- The left separator before zone `i` is blank. -/
theorem zonedTape_left_sep {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : ℕ) :
    zonedTape z (-(zoneStart i : ℤ) + 1) = none := by
  have h2 := two_le_zoneStart i
  simp only [zonedTape, zoneCellAt]
  rw [if_neg (by omega), if_neg (by omega), show (-(-(zoneStart i : ℤ) + 1)).toNat =
    zoneStart i - 1 by omega, zoneOwner_sep]
  rfl

/-- **Blank outside the layout**: every cell at distance at least `zoneStart ℓ - 1` from home
(the separator after the last laid-out zone, and beyond) is blank. With `ℓ` levels the
nonblank cells lie in `[-(zoneStart ℓ - 2), zoneStart ℓ - 2]`; this replaces the retired
`Turing.zoneTape_blank_outside` as the carrier's extent. -/
theorem zonedTape_blank_outside {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (c : ℤ)
    (hc : (zoneStart ℓ : ℤ) - 1 ≤ |c|) : zonedTape z c = none := by
  have h2 := two_le_zoneStart ℓ
  have h0 : c ≠ 0 := by
    intro h
    rw [h, abs_zero] at hc
    omega
  unfold zonedTape zoneCellAt
  rw [if_neg h0]
  by_cases hp : 0 < c
  · rw [abs_of_pos hp] at hc
    rw [if_pos hp, zoneOwner_beyond (by omega)]
    rfl
  · rw [abs_of_nonpos (by omega)] at hc
    rw [if_neg hp, zoneOwner_beyond (by omega)]
    rfl

/-- **Each right zone is a delimited word** (the carrier invariant that lets the framed sweeps
run on a zone, with no save and restore; design §13d, G3): from its first cell, the right zone
`i` holds `Turing.zoneCells true z i`, with blanks at relative positions `-1` and
`zoneCapacity i`. This is the precondition form of `Turing.copyTM_run_ofCfg` and of the mapped
sweeps with the head at `zoneStart i`.

**Proof sketch.** Inside the zone, `Turing.zonedTape_right` and the cells' definition; position
`-1` is the separator before zone `i` and position `zoneCapacity i` the one before zone `i + 1`
(`Turing.zonedTape_right_sep`, `Turing.zoneStart_succ`). -/
theorem zonedTape_right_word {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (zoneCapacity i : ℤ) →
      zonedTape z ((zoneStart i : ℤ) + p) = FinTM.bufferTape (zoneCells true z i) p := by
  intro p h₁ h₂
  rcases (show p = -1 ∨ (0 ≤ p ∧ p < zoneCapacity i) ∨ p = zoneCapacity i by omega) with
    h | ⟨h₁, h₂⟩ | h
  · subst h
    rw [show (zoneStart i : ℤ) + -1 = (zoneStart i : ℤ) - 1 by omega, zonedTape_right_sep]
    simp [FinTM.bufferTape]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    rw [show (zoneStart i : ℤ) + n = ((zoneStart i + n : ℕ) : ℤ) by omega,
      zonedTape_right z i n (by omega), FinTM.bufferTape_nat]
    simp [zoneCells, show n < zoneCapacity i by omega]
  · subst h
    have hs := zoneStart_succ i.val
    rw [show (zoneStart i : ℤ) + (zoneCapacity i : ℕ) = (zoneStart (i.val + 1) : ℤ) - 1 by
      omega, zonedTape_right_sep, FinTM.bufferTape_nat]
    simp

/-- **Each left zone is a delimited word**, read in the sweep direction (left to right): from
the zone's outermost cell `-(zoneStart i + zoneCapacity i - 1)`, the left zone `i` holds the
reversed `Turing.zoneCells false z i`, with blanks at relative positions `-1` and
`zoneCapacity i`.

**Proof sketch.** Position `p` inside is the cell at offset `zoneCapacity i - 1 - p` from the
zone's inner end, which the reversed list holds at `p`; the delimiters are the separators
before zones `i + 1` and `i`. -/
theorem zonedTape_left_word {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (zoneCapacity i : ℤ) →
      zonedTape z (-((zoneStart i : ℤ) + zoneCapacity i - 1) + p) =
        FinTM.bufferTape (zoneCells false z i).reverse p := by
  intro p h₁ h₂
  have hc : 0 < zoneCapacity i := by
    have := Nat.two_pow_pos i.val
    unfold zoneCapacity
    omega
  rcases (show p = -1 ∨ (0 ≤ p ∧ p < zoneCapacity i) ∨ p = zoneCapacity i by omega) with
    h | ⟨h₁, h₂⟩ | h
  · subst h
    have hs := zoneStart_succ i.val
    rw [show -((zoneStart i : ℤ) + zoneCapacity i - 1) + -1 =
      -(zoneStart (i.val + 1) : ℤ) + 1 by omega, zonedTape_left_sep]
    simp [FinTM.bufferTape]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    rw [show -((zoneStart i : ℤ) + zoneCapacity i - 1) + n =
      -((zoneStart i + (zoneCapacity i - 1 - n) : ℕ) : ℤ) by omega,
      zonedTape_left z i _ (by omega), FinTM.bufferTape_nat, List.getElem?_reverse
        (by simp; omega)]
    simp [zoneCells, show zoneCapacity i - 1 - n < zoneCapacity i by omega]
  · subst h
    rw [show -((zoneStart i : ℤ) + zoneCapacity i - 1) + (zoneCapacity i : ℕ) =
      -(zoneStart i : ℤ) + 1 by omega, zonedTape_left_sep, FinTM.bufferTape_nat]
    simp

/-- **Track independence**: changing one track's contents changes no other track's slot,
anywhere on the tape. -/
theorem zonedTape_update_slot {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) {s t : Fin k}
    (h : s ≠ t) (w : ZoneContents ℓ) (c : ℤ) :
    (zonedTape (Function.update z t w) c).map (zoneSlotOf s) =
      (zonedTape z c).map (zoneSlotOf s) := by
  unfold zonedTape zoneCellAt
  split_ifs <;> simp [zoneSlotOf, Function.update_of_ne h] <;>
    cases zoneOwner ℓ _ <;> simp [zoneSlotOf, Function.update_of_ne h]

/-- **The layout does not depend on the contents**: a cell is blank on one family's tape
exactly when it is blank on another's, for the same number of levels. -/
theorem zonedTape_isSome {k ℓ : ℕ} (z z' : Fin k → ZoneContents ℓ) (c : ℤ) :
    (zonedTape z c).isSome = (zonedTape z' c).isSome := by
  unfold zonedTape zoneCellAt
  split_ifs <;> simp

/-- **Writing the home** is a one-cell write: overwriting cell `0` with the new virtual
symbols gives the zoned tape of the home-written family. -/
theorem zonedTape_homeWrite {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (v : Fin k → Option Bool) :
    Function.update (zonedTape z) 0 (some (.inr fun t => some (v t))) =
      zonedTape (fun t => zoneHomeWrite (z t) (v t)) := by
  funext c
  by_cases h : c = 0
  · subst h
    simp [zoneHomeWrite]
  · rw [Function.update_of_ne h]
    unfold zonedTape zoneCellAt
    simp [h, zoneHomeWrite, ZoneContents.words]

/-- Zone contents are determined by their home and words. -/
theorem ZoneContents.ext' {ℓ : ℕ} {a b : ZoneContents ℓ} (h₀ : a.home = b.home)
    (h₁ : a.left = b.left) (h₂ : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

/-- **The encoding is faithful**: two families on the same levels with the same zoned tape are
equal. (A sanity theorem: the carrier loses nothing.)

**Proof sketch.** The homes are read at cell `0`. A zone word is determined by its lookups: at
an offset below the capacity, `Turing.zonedTape_right`/`_left` expose it in the track's slot;
beyond the capacity both lookups are `none`, since words fit their zones. -/
theorem zonedTape_injective {k ℓ : ℕ} {z z' : Fin k → ZoneContents ℓ}
    (h : zonedTape z = zonedTape z') : z = z' := by
  funext t
  have hw : ∀ (side : Bool) (i : Fin ℓ), (z t).words side i = (z' t).words side i := by
    intro side i
    apply List.ext_getElem?
    intro p
    by_cases hp : p < zoneCapacity i
    · cases side
      · have e := congrFun h (-((zoneStart i + p : ℕ) : ℤ))
        rw [zonedTape_left z i p hp, zonedTape_left z' i p hp] at e
        simpa using congrFun (Sum.inr_injective (Option.some_injective _ e)) t
      · have e := congrFun h ((zoneStart i + p : ℕ) : ℤ)
        rw [zonedTape_right z i p hp, zonedTape_right z' i p hp] at e
        simpa using congrFun (Sum.inr_injective (Option.some_injective _ e)) t
    · rw [List.getElem?_eq_none (by have := (z t).words_le side i; omega),
        List.getElem?_eq_none (by have := (z' t).words_le side i; omega)]
  apply ZoneContents.ext'
  · have e := congrFun h 0
    simp only [zonedTape_zero] at e
    simpa using congrFun (Sum.inr_injective (Option.some_injective _ e)) t
  · funext i
    exact hw false i
  · funext i
    exact hw true i

/-- Ownership after laying out one more level: the old zones own what they owned, the new zone
`ℓ` owns its own cells, and nothing else changes.

**Proof sketch.** The old levels embed by `Fin.castSucc`, with the same starts; the new level
is `Fin.last ℓ`; uniqueness of owners is `Turing.zoneOwner_of_mem`. -/
theorem zoneOwner_succ (ℓ n : ℕ) :
    zoneOwner (ℓ + 1) n =
      if zoneStart ℓ ≤ n ∧ n < zoneStart ℓ + zoneCapacity ℓ then some (Fin.last ℓ)
      else (zoneOwner ℓ n).map Fin.castSucc := by
  split_ifs with h
  · exact zoneOwner_of_mem (Fin.last ℓ) h.1 h.2
  · cases ho : zoneOwner ℓ n with
    | none =>
      apply zoneOwner_of_not_mem
      intro i hi
      refine Fin.lastCases (motive := fun i : Fin (ℓ + 1) =>
        ¬ (zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i)) ?_ (fun j => ?_) i hi
      · simpa using h
      · intro hj
        rw [zoneOwner_of_mem j hj.1 hj.2] at ho
        exact Option.some_ne_none _ ho
    | some j =>
      rw [Fin.find_eq_some_iff.mp ho |>.1 |> fun hj => zoneOwner_of_mem j.castSucc hj.1 hj.2]
      rfl

/-- **What the extension writes**: laying out level `ℓ` on every track changes exactly the
cells of the two new zones, each of which then holds, on every track, a stored virtual blank in
its inner `2^ℓ` slots and `⊠` in its outer `2^ℓ` slots. Every other cell is unchanged.

**Proof sketch.** `Turing.zoneOwner_succ` splits the cells into the new zone's and the old
owners'; the old words are kept (`Turing.ZoneContents.extend_words_castSucc`) and the new ones
are `replicate (2^ℓ) none` (`Turing.ZoneContents.extend_words_last`). -/
theorem zonedTape_extend {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (c : ℤ) :
    zonedTape (fun t => (z t).extend) c =
      if (zoneStart ℓ : ℤ) ≤ |c| ∧ |c| < zoneStart ℓ + zoneCapacity ℓ then
        some (.inr fun _ => if (|c|).toNat - zoneStart ℓ < 2 ^ ℓ then some none else none)
      else zonedTape z c := by
  by_cases h0 : c = 0
  · subst h0
    have := two_le_zoneStart ℓ
    simp only [abs_zero, zonedTape_zero]
    rw [if_neg (by omega)]
    rfl
  · unfold zonedTape zoneCellAt
    rw [if_neg h0, if_neg h0]
    by_cases hp : 0 < c
    · rw [if_pos hp, if_pos hp, zoneOwner_succ, abs_of_pos hp]
      by_cases hz : zoneStart ℓ ≤ c.toNat ∧ c.toNat < zoneStart ℓ + zoneCapacity ℓ
      · rw [if_pos hz, if_pos (by omega)]
        simp [ZoneContents.extend_words_last, List.getElem?_replicate]
      · rw [if_neg hz, if_neg (by omega)]
        cases zoneOwner ℓ c.toNat <;> simp [ZoneContents.extend_words_castSucc]
    · rw [if_neg hp, if_neg hp, zoneOwner_succ, abs_of_nonpos (by omega)]
      by_cases hz : zoneStart ℓ ≤ (-c).toNat ∧ (-c).toNat < zoneStart ℓ + zoneCapacity ℓ
      · rw [if_pos hz, if_pos (by omega)]
        simp [ZoneContents.extend_words_last, List.getElem?_replicate]
      · rw [if_neg hz, if_neg (by omega)]
        cases zoneOwner ℓ (-c).toNat <;> simp [ZoneContents.extend_words_castSucc]

end Turing
