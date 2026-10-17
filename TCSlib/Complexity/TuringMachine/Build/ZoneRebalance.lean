/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.ZoneTape
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the rebalance and extension rows (§13d G4)

The machine rows of the Hennie–Stearns zone layer ([AB09] §1.7; `machine-library-design.md`
§13d, G4; decisions 13d.2–13d.4), stated as `Turing.Contract`s from the start (§16b, item 5).
Both rows are two-tape machines over `Turing.ZoneSym k`: tape `0` carries the zoned tape
(`Turing.zonedTape`), tape `1` is a blank scratch tape, the buffer.

* **The rebalance row**, one machine per direction and track (the track in finite control,
  decision 13d.4): from the home, scan the feeding side for the scanned index
  `Turing.zoneShiftIndex`, realize the total cascade there (`Turing.zoneRebalance`, decision
  13d.3), return home; exit `done`, or `short` when every feeding zone is empty. Time
  `O(2^{i₀} + 1)`, the zoned head within the level-`i₀` extent.
* **The extension row** (decision 13d.2): lay out level `ℓ` on every track, half full of virtual
  blanks, in `O(2^ℓ + 1)`.

**Status: statements.** The two rows are sorried under their proof sketches (the fill plan);
everything else here is proved. These rows replace the retired binary rows
`exists_zoneShiftInTM` and `exists_zoneShiftOutTM` of `Build/Zone`.

## How the assembly consumes the rows (§13d, G5; sketched for fit, not in this module)

One simulated step reads the home tuple, applies the simulated transition in finite control,
writes the home tuple (`Turing.zonedTape_homeWrite`), and for each moving track runs its
rebalance row; on `short` it runs the extension row and the rebalance again, which then exits
`done` (`Turing.zoneRebalanceIndex_extend_of_short`). Every row's endpoint satisfies the next
row's precondition (`Turing.zoneRowPre_rebalancePost`, `Turing.zoneRowPre_extendPost`), and the
represented tapes move as the simulated heads do (`Turing.zoneTrackTape_rebalance_right` and its
mirror). The amortization `Σ_i T/2^{i-1} · 2^i = O(T log T)` is the consumer's mathematics.

## Main definitions

* `Turing.ZoneData`, `Turing.zoneRowPre`: the index and the precondition.
* `Turing.zoneRebalanceIndex`, `Turing.zoneRebalanceData`, `Turing.zoneExtendData`.
* `Turing.zoneRebalancePost`, `Turing.zoneExtendPost`, `Turing.zoneRowLo`, `Turing.zoneRowHi`:
  the endpoints and envelopes.

## Main results

* `Turing.exists_zoneRebalanceTM`, `Turing.exists_zoneExtendTM`: the rows (sorried).
* `Turing.zoneRowPre_rebalancePost`, `Turing.zoneRowPre_extendPost`: rows chain.
* `Turing.zoneRebalancePost_state_done`, `Turing.zoneRebalanceData_of_short`,
  `Turing.zoneRebalanceIndex_extend_of_short`: the two exits.
* `Turing.zoneRebalancePost_frames`, `Turing.zoneExtendPost_frames`: the footprints.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009. (§1.7, the Hennie–Stearns simulation: zones, shifts and their index.)
-/

namespace Turing

/-! ### The data, the precondition, the endpoints and the envelopes -/

/-- **The data index of the zone rows**: a level count `ℓ` and a contents family over `ℓ` laid
out levels, one `Turing.ZoneContents` per track. -/
abbrev ZoneData (k : ℕ) : Type := Σ ℓ : ℕ, Fin k → ZoneContents ℓ

/-- **The precondition of every zone row**: work tape `0` holds the zoned tape of the data,
with its head at home (cell `0`); work tape `1`, the scratch tape, is blank everywhere, its
head anywhere. Nothing is required of the control state beyond the contract's entry, of the
input tape or of the output. -/
def zoneRowPre {k : ℕ} {S : Type} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) S x) : Prop :=
  d.workTapes 0 = zonedTape D.2 ∧ d.workTapePos 0 = 0 ∧ ∀ q, d.workTapes 1 q = none

/-- The scanned index of the rebalance of track `t` in direction `dir`. -/
def zoneRebalanceIndex {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k) : ℕ :=
  zoneShiftIndex dir (D.2 t)

/-- The data after the rebalance of track `t` in direction `dir`: track `t` rebalanced
(`Turing.zoneRebalance`), every other track and the level count unchanged. -/
def zoneRebalanceData {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k) : ZoneData k :=
  ⟨D.1, Function.update D.2 t (zoneRebalance dir (D.2 t))⟩

/-- The data after the extension: one more level, laid out on every track
(`Turing.ZoneContents.extend`). -/
def zoneExtendData {k : ℕ} (D : ZoneData k) : ZoneData k :=
  ⟨D.1 + 1, fun t => (D.2 t).extend⟩

/-- **The rebalance row's endpoint**: from `d`, the state is the exit `done` when the scanned
index is below `ℓ` and `short` otherwise; tape `0` holds the zoned tape of the rebalanced data;
every other field of `d` (the scratch tape, both heads, the input position, the output) is
unchanged. -/
def zoneRebalancePost {k : ℕ} (dir : Bool) (t : Fin k) {S : Type} {x : List (ZoneSym k)}
    (done short : S) (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) : Cfg 2 (ZoneSym k) S x :=
  { d with
    state := some (if zoneRebalanceIndex dir t D < D.1 then done else short)
    workTapes := fun j => if j = 0 then zonedTape (zoneRebalanceData dir t D).2
      else d.workTapes j }

/-- **The extension row's endpoint**: the exit `done`; tape `0` holds the zoned tape of the
extended data; every other field of `d` is unchanged. -/
def zoneExtendPost {k : ℕ} {S : Type} {x : List (ZoneSym k)} (done : S) (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) S x) : Cfg 2 (ZoneSym k) S x :=
  { d with
    state := some done
    workTapes := fun j => if j = 0 then zonedTape (zoneExtendData D).2 else d.workTapes j }

/-- **The lower envelope of a zone row reaching level `r D`**: the zoned head stays at or
right of `-zoneStart (r D + 1)` (inside the level-`r D` extent and its outer separator, with one
cell to spare), and the scratch head at or right of its start minus `C · (2^(r D) + 1)`. -/
def zoneRowLo {k : ℕ} {S : Type} {x : List (ZoneSym k)} (r : ZoneData k → ℕ) (C : ℕ)
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) (j : Fin 2) : ℤ :=
  if j = 0 then -(zoneStart (r D + 1) : ℤ) else d.workTapePos j - C * (2 ^ r D + 1)

/-- The upper envelope of a zone row reaching level `r D`, mirroring `Turing.zoneRowLo`. -/
def zoneRowHi {k : ℕ} {S : Type} {x : List (ZoneSym k)} (r : ZoneData k → ℕ) (C : ℕ)
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) (j : Fin 2) : ℤ :=
  if j = 0 then (zoneStart (r D + 1) : ℤ) else d.workTapePos j + C * (2 ^ r D + 1)

/-- The directed position of a slot, measured from the zone's inner end. -/
private def zr_zonePos (side : Bool) (i p : ℕ) : ℤ :=
  if side then (zoneStart i + p : ℕ) else -((zoneStart i + p : ℕ) : ℤ)

/-- Reading a slot uses the same formula on both sides; the left side is mirrored. -/
private lemma zr_read_slot {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (i : Fin ℓ) (t : Fin k) (p : ℕ) (hp : p < zoneCapacity i) :
    (zonedTape z (zr_zonePos side i p)).map (zoneSlotOf t) =
      some ((z t).words side i)[p]? := by
  have hcell : zonedTape z (zr_zonePos side i p) =
      some (.inr fun s => ((z s).words side i)[p]?) := by
    cases side
    · exact zonedTape_left z i p hp
    · exact zonedTape_right z i p hp
  simp only [hcell, Option.map_some, zoneSlotOf_inr]

/-- Every physical zone has positive capacity. -/
private lemma zr_capacity_pos (i : ℕ) : 0 < zoneCapacity i := by
  rw [zoneCapacity_eq]
  exact Nat.mul_pos (by decide) (Nat.two_pow_pos i)

/-- Inner packing turns a buffer-slot test into a length comparison. -/
private lemma zr_slot_empty_iff {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (i : Fin ℓ) (t : Fin k) (p : ℕ) (hp : p < zoneCapacity i) :
    (zonedTape z (zr_zonePos side i p)).map (zoneSlotOf t) = some none ↔
      ((z t).words side i).length ≤ p := by
  rw [zr_read_slot side z i t p hp, Option.some.injEq, List.getElem?_eq_none_iff]

/-- The scan's innermost-slot test detects exactly an empty feeding zone. -/
private lemma zr_inner_empty_iff {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (i : Fin ℓ) (t : Fin k) :
    (zonedTape z (zr_zonePos side i 0)).map (zoneSlotOf t) = some none ↔
      (z t).words side i = [] := by
  have hp := zr_capacity_pos i.val
  rw [zr_slot_empty_iff side z i t 0 hp]
  simp only [Nat.le_zero, List.length_eq_zero_iff]

/-- A zone is full exactly when its outermost slot is occupied. -/
private lemma zr_outer_full_iff {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (i : Fin ℓ) (t : Fin k) :
    (zonedTape z (zr_zonePos side i (zoneCapacity i - 1))).map (zoneSlotOf t) ≠
        some none ↔ ((z t).words side i).length = zoneCapacity i := by
  have hc := zr_capacity_pos i.val
  have hfit := (z t).words_le side i
  rw [ne_eq, zr_slot_empty_iff side z i t _ (by omega)]
  omega

/-- The outward-shift room guard is one slot test, including equality at the boundary.
The amount must be positive so that the tested slot belongs to the zone. -/
private lemma zr_room_iff {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (i : Fin ℓ) (t : Fin k) (m : ℕ) (hm : 0 < m) (hcap : m ≤ zoneCapacity i) :
    (zonedTape z (zr_zonePos side i (zoneCapacity i - m))).map (zoneSlotOf t) =
        some none ↔ ((z t).words side i).length + m ≤ zoneCapacity i := by
  rw [zr_slot_empty_iff side z i t _ (by omega)]
  omega

/-- The physical scan tests characterize the pure scanned index.

**Proof sketch.** Convert each innermost-slot test to emptiness. The public least-nonempty
index characterization then identifies the first occupied level. -/
private lemma zr_scan_index {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (t : Fin k) (j : ℕ) (hj : j < ℓ)
    (hbefore : ∀ i : Fin ℓ, i.val < j →
      (zonedTape z (zr_zonePos side i 0)).map (zoneSlotOf t) = some none)
    (hat : (zonedTape z (zr_zonePos side j 0)).map (zoneSlotOf t) ≠ some none) :
    zoneShiftIndex side (z t) = j := by
  apply zoneShiftIndex_eq side (z t) j hj
  · intro i hi
    exact (zr_inner_empty_iff side z i t).mp (hbefore i hi)
  · intro he
    exact hat ((zr_inner_empty_iff side z ⟨j, hj⟩ t).mpr he)

/-- If every scanned slot is empty, the pure rebalance takes its identity branch. -/
private lemma zr_scan_short {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (t : Fin k) (h : ∀ i : Fin ℓ,
      (zonedTape z (zr_zonePos side i 0)).map (zoneSlotOf t) = some none) :
    zoneRebalance side (z t) = z t := by
  apply zoneRebalance_of_le
  have he := (zoneShiftIndex_eq_length_iff side (z t)).mpr
    (fun i => (zr_inner_empty_iff side z i t).mp (h i))
  omega

/-- The preceding zone is a ruler of the new zone's half-capacity. -/
private lemma zr_ruler_length (i : ℕ) (hi : 1 ≤ i) : zoneCapacity (i - 1) = 2 ^ i := by
  have he : i = (i - 1) + 1 := by omega
  conv_rhs => rw [he, pow_succ]
  simp only [zoneCapacity_eq, Nat.mul_comm]

/-- The level extent has a uniform geometric bound, including level zero. -/
private lemma zr_extent_cost (i : ℕ) : zoneStart (i + 1) ≤ 6 * (2 ^ i + 1) := by
  have hi : i < 2 ^ i := Nat.lt_two_pow_self
  rw [zoneStart_eq]
  simp only [pow_succ]
  omega

/-- Swapping every track's sides mirrors the physical tape about home.

**Proof sketch.** Home is unchanged. At a positive or negative cell, the owner depends only on
its absolute distance, and swapping contents exchanges the selected side's word. -/
private lemma zr_mirror_tape {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (c : ℤ) :
    zonedTape (fun t => (z t).swap) c = zonedTape z (-c) := by
  rcases lt_trichotomy c 0 with hn | rfl | hp
  · rw [zonedTape_of_neg _ hn, zonedTape_of_pos _ (by omega)]
    simp only [zoneCellAt_eq, ZoneContents.words_false, ZoneContents.swap_left,
      ZoneContents.words_true]
  · simp only [neg_zero, zonedTape_zero, ZoneContents.swap_home]
  · rw [zonedTape_of_pos _ hp, zonedTape_of_neg _ (by omega)]
    simp only [neg_neg, zoneCellAt_eq, ZoneContents.words_true, ZoneContents.swap_right,
      ZoneContents.words_false]

/-- The extension writes its two constant half-words on either side of home. -/
private lemma zr_extend_cell {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (p : ℕ) (hp : p < zoneCapacity ℓ) :
    zonedTape (fun t => (z t).extend) (zr_zonePos side ℓ p) =
      some (.inr fun _ => if p < 2 ^ ℓ then some none else none) := by
  have ha : |zr_zonePos side ℓ p| = ((zoneStart ℓ + p : ℕ) : ℤ) := by
    cases side
    · change |-((zoneStart ℓ + p : ℕ) : ℤ)| = _
      rw [abs_neg, abs_of_nonneg (by omega)]
    · change |((zoneStart ℓ + p : ℕ) : ℤ)| = _
      exact abs_of_nonneg (by omega)
  rw [zonedTape_extend, ha, if_pos (by omega)]
  simp only [Int.toNat_natCast, Nat.add_sub_cancel_left]

/-- Advancing only the ruler head exposes its tail as the next directed word.

**Proof sketch.** At offset `p` after that advance, the old offset is `p + 1`. The old word is
nonempty, so this offset is covered by the original word premise, including its delimiter.
The bound is valid for a one-cell ruler, whose tail is empty. -/
private lemma zr_ruler_tail {Γ : Type} (tape : ℤ → Option Γ) (q : ℤ) (dir : SignType)
    (w : List Γ) (hw : w ≠ [])
    (hword : ∀ p : ℕ, p ≤ w.length →
      tape (q + (dir : ℤ) * p) = FinTM.bufferTape w p) :
    ∀ p : ℕ, p ≤ w.tail.length →
      tape ((q + (dir : ℤ)) + (dir : ℤ) * p) = FinTM.bufferTape w.tail p := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons a w =>
    intro p hp
    have he : (q + (dir : ℤ)) + (dir : ℤ) * p =
        q + (dir : ℤ) * ((p + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      omega
    rw [he, hword (p + 1) (by simpa using hp)]
    simp only [FinTM.bufferTape_nat, List.getElem?_cons_succ, List.tail_cons]

/-- A single-cell controller with two live verdicts. No public row performs just one optional
write, one work-head step, and a slot-dependent verdict: the sweep and seek rows traverse whole
words. This permitted leaf covers the ruler adjustment, constant writes, and slot tests; it
contains no iteration or phase dispatch. State `none` is the entry; `some b` is verdict `b`. -/
private def zr_cellTM {k : ℕ} (i : Fin 2) (choose : Option (ZoneSym k) → Bool)
    (wr : Option (Option (ZoneSym k))) (dir : SignType) :
    MultiTapeTM 2 (ZoneSym k) (Option Bool) where
  q₀ := none
  tr q _ a := match q with
    | none => tapeAction i 0 wr dir (some (choose (a i)))
    | some b => inputMoveAction 0 (some b)

/-- The single-cell leaf's endpoint; all unmentioned configuration fields are preserved. -/
private def zr_cellPost {k : ℕ} {x : List (ZoneSym k)} (i : Fin 2)
    (choose : Option (ZoneSym k) → Bool) (wr : Option (Option (ZoneSym k)))
    (dir : SignType) (d : Cfg 2 (ZoneSym k) (Option Bool) x) :
    Cfg 2 (ZoneSym k) (Option Bool) x :=
  { d with
    state := some (some (choose (d.workTapeSymbols i)))
    workTapes := match wr with
      | none => d.workTapes
      | some a => Function.update d.workTapes i
          (Function.update (d.workTapes i) (d.workTapePos i) a)
    workTapePos := Function.update d.workTapePos i (d.workTapePos i + dir) }

/-- The leaf takes its advertised single step, using the public action lemmas.

**Proof sketch.** Split on whether a write was requested, and apply the existing writing or
non-writing action lemma. The input movement is zero in either case. -/
private lemma zr_cell_step {k : ℕ} {x : List (ZoneSym k)} (i : Fin 2)
    (choose : Option (ZoneSym k) → Bool) (wr : Option (Option (ZoneSym k)))
    (dir : SignType) (d : Cfg 2 (ZoneSym k) (Option Bool) x)
    (hd : d.state = some none) :
    (zr_cellTM i choose wr dir).step d = zr_cellPost i choose wr dir d := by
  cases wr with
  | none =>
    simpa only [moveInputPos_zero] using
      step_of_tapeAction_move (zr_cellTM i choose none dir) d i 0 dir hd rfl
  | some a =>
    simpa only [moveInputPos_zero] using
      step_of_tapeAction_write (zr_cellTM i choose (some a) dir) d i 0 a dir hd rfl

/-- The one-cell leaf as a contract: exact time one, with each head between its two endpoints.
No condition is imposed on the tape, the input position, or the existing output.

**Proof sketch.** The public single-action equations give the run. The only strict-prefix time
is zero, when the entry differs from both verdicts. At time zero and time one the head lies at
one of the two ends of the stated interval. -/
private def zr_cellContract {k : ℕ} (i : Fin 2) (choose : Option (ZoneSym k) → Bool)
    (wr : Option (Option (ZoneSym k))) (dir : SignType) (x : List (ZoneSym k)) :
    Contract (zr_cellTM i choose wr dir) none (Set.range fun b : Bool => some (some b))
      Unit x where
  pre _ _ := True
  time _ _ := 1
  post _ d := zr_cellPost i choose wr dir d
  lo _ d j := min (d.workTapePos j) ((zr_cellPost i choose wr dir d).workTapePos j)
  hi _ d j := max (d.workTapePos j) ((zr_cellPost i choose wr dir d).workTapePos j)
  run _ d hd _ := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      zr_cell_step i choose wr dir d hd]
  exit_mem _ d _ _ := ⟨choose (d.workTapeSymbols i), rfl⟩
  cut _ d hd _ u hu := by
    have he : u = 0 := by omega
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    rintro ⟨b, hb⟩
    cases hb
  env _ d hd _ u hu j := by
    have he : u = 0 ∨ u = 1 := by omega
    rcases he with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
      exact Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
        zr_cell_step i choose wr dir d hd]
      exact Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩

/-- Agreement with each delimited field determines the layout up to its end offset.

**Proof sketch.** Induct on the number of fields covered. A position is either before the
last field's offset or in that field, including its right separator. Use the public field
word theorem in the latter case; no layout implementation is unfolded. -/
private lemma zr_fieldsTape_eq {Γ : Type} (fs : List (List Γ)) (tape : ℤ → Option Γ)
    (hword : ∀ (j : ℕ) (hj : j < fs.length) (q : ℤ), 0 ≤ q →
      q ≤ (fs[j].length : ℤ) →
      tape ((fieldOffset fs j : ℤ) + q) = FinTM.bufferTape fs[j] q)
    (p : ℤ) (hp : 0 ≤ p) (he : p < (fieldOffset fs fs.length : ℤ)) :
    tape p = fieldsTape fs p := by
  have cover : ∀ n, n ≤ fs.length → ∀ q : ℤ, 0 ≤ q →
      q < (fieldOffset fs n : ℤ) → tape q = fieldsTape fs q := by
    intro n
    induction n with
    | zero =>
      intro hn q hq hend
      rw [fieldOffset_zero] at hend
      omega
    | succ n ih =>
      intro hn q hq hend
      by_cases hb : q < (fieldOffset fs n : ℤ)
      · exact ih (by omega) q hq hb
      · have hindex : n < fs.length := by omega
        have hs := fieldOffset_succ fs n hindex
        have h0 : 0 ≤ q - (fieldOffset fs n : ℤ) := by omega
        have h1 : q - (fieldOffset fs n : ℤ) ≤ (fs[n].length : ℤ) := by
          rw [hs] at hend
          omega
        have hq' : (fieldOffset fs n : ℤ) + (q - fieldOffset fs n) = q := by omega
        calc
          tape q = tape ((fieldOffset fs n : ℤ) + (q - fieldOffset fs n)) :=
            congrArg tape hq'.symm
          _ = FinTM.bufferTape fs[n] (q - fieldOffset fs n) := hword n hindex _ h0 h1
          _ = fieldsTape fs ((fieldOffset fs n : ℤ) + (q - fieldOffset fs n)) :=
            (fieldsTape_field fs n hindex _ (by omega) h1).symm
          _ = fieldsTape fs q := congrArg (fieldsTape fs) hq'
  exact cover fs.length le_rfl p hp he

/-- The right layout's level `i` begins at the physical start of zone `i`.

**Proof sketch.** The home field contributes two cells including its separator. Each further
field contributes the capacity of its zone and one separator, exactly the zone-start recurrence. -/
private lemma zr_right_offset {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : ℕ)
    (hi : i ≤ ℓ) :
    fieldOffset ([.inr fun t => some (z t).home] :: List.ofFn (zoneCells true z)) (i + 1) =
      zoneStart i := by
  induction i with
  | zero =>
    rw [fieldOffset_cons_succ, fieldOffset_zero, zoneStart_eq]
    norm_num
  | succ i ih =>
    rw [fieldOffset_succ _ (i + 1) (by simp only [List.length_cons, List.length_ofFn]; omega)]
    rw [ih (by omega)]
    simp only [List.getElem_cons_succ, List.getElem_ofFn, zoneCells_length]
    rw [zoneStart_succ]
    omega

/-- From home, the right zones form the field layout required by the seek-to-end row.

**Proof sketch.** The home and its following separator form the first field. Every later
field is the corresponding right-zone word at the offset computed above. The shared layout
comparison covers the interior; the published blank-outside equation covers the end. -/
private lemma zr_zonedTape_right_fields {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) :
    ∀ p : ℤ, 0 ≤ p →
      p ≤ (fieldOffset ([.inr fun t => some (z t).home] :: List.ofFn (zoneCells true z))
        (ℓ + 1) : ℤ) →
      zonedTape z p =
        fieldsTape ([.inr fun t => some (z t).home] :: List.ofFn (zoneCells true z)) p := by
  let fs : List (List (ZoneSym k)) :=
    [.inr fun t => some (z t).home] :: List.ofFn (zoneCells true z)
  have hlen : fs.length = ℓ + 1 := by simp only [fs, List.length_cons, List.length_ofFn]
  have hend : fieldOffset fs fs.length = zoneStart ℓ := by
    rw [hlen]
    exact zr_right_offset z ℓ le_rfl
  intro p hp hp'
  change zonedTape z p = fieldsTape fs p
  by_cases he : p < (fieldOffset fs fs.length : ℤ)
  · apply zr_fieldsTape_eq fs (zonedTape z) _ p hp he
    intro j hj q hq hq'
    cases j with
    | zero =>
      simp only [fs, List.getElem_cons_zero, List.length_singleton] at hq' ⊢
      rw [fieldOffset_zero]
      have hcases : q = 0 ∨ q = 1 := by omega
      rcases hcases with rfl | rfl
      · simp only [Nat.cast_zero, zero_add, zonedTape_zero]
        simpa only [Nat.cast_zero, List.getElem?_cons_zero] using
          (FinTM.bufferTape_nat ([.inr fun t => some (z t).home] : List (ZoneSym k)) 0).symm
      · have hsep := zonedTape_right_sep z 0
        norm_num only [zoneStart_eq, pow_one, Nat.add_zero, Nat.cast_ofNat] at hsep
        simpa only [Nat.cast_zero, zero_add, FinTM.bufferTape_nat,
          List.getElem?_cons_succ, List.getElem?_nil] using hsep
    | succ j =>
      have hj' : j < ℓ := by omega
      simp only [fs, List.getElem_cons_succ, List.getElem_ofFn, zoneCells_length] at hq' ⊢
      rw [zr_right_offset z j (by omega)]
      exact zonedTape_right_word z ⟨j, hj'⟩ q (by omega) hq'
  · have pe : p = (zoneStart ℓ : ℤ) := by
      change p ≤ (fieldOffset fs (ℓ + 1) : ℤ) at hp'
      rw [← hlen, hend] at hp'
      rw [hend] at he
      omega
    have hjoin := length_joinFields_add_one fs (by simp only [fs, ne_eq, List.cons_ne_nil,
      not_false_eq_true])
    rw [fieldsTape_of_length_le fs (by omega), pe]
    exact zonedTape_blank_outside z _ (by rw [abs_of_nonneg (by omega)]; omega)

/-- The reversed left layout's prefix and its remaining zone extent add to the full extent.

**Proof sketch.** Each field removes one zone from the remaining extent. Its length and
separator are precisely the difference of successive zone starts. -/
private lemma zr_left_offset {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (j : ℕ)
    (hj : j ≤ ℓ) :
    fieldOffset (List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse) j +
      zoneStart (ℓ - j) = zoneStart ℓ := by
  induction j with
  | zero => rw [fieldOffset_zero, Nat.sub_zero, Nat.zero_add]
  | succ j ih =>
    rw [fieldOffset_succ _ j (by simp only [List.length_ofFn]; omega)]
    simp only [List.getElem_ofFn, List.length_reverse, zoneCells_length, Fin.val_rev]
    have hs := zoneStart_succ (ℓ - (j + 1))
    have he : ℓ - j = (ℓ - (j + 1)) + 1 := by omega
    have hp := ih (by omega)
    rw [he] at hp
    omega

/-- The left zones, reversed within each zone and in level order, form the seek-start layout.

**Proof sketch.** The prefix formula places each reversed zone exactly at its physical outer
end. The shared layout comparison then applies to the left-zone word equations. The two cells
before the layout are blank by the published extent bound. This also covers zero levels. -/
private lemma zr_zonedTape_left_fields {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) :
    ∀ p : ℤ, -2 ≤ p →
      p < (fieldOffset (List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse)
        ℓ : ℤ) →
      zonedTape z (-(fieldOffset (List.ofFn fun i : Fin ℓ =>
          (zoneCells false z i.rev).reverse) ℓ : ℤ) + p) =
        fieldsTape (List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse) p := by
  let fs := List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse
  have hlen : fs.length = ℓ := List.length_ofFn
  have htotal : fieldOffset fs ℓ + 2 = zoneStart ℓ := by
    have ht := zr_left_offset z ℓ le_rfl
    simpa only [Nat.sub_self, zoneStart_eq, pow_one, Nat.add_zero] using ht
  intro p hp hp'
  change zonedTape z (-(fieldOffset fs ℓ : ℤ) + p) = fieldsTape fs p
  by_cases h0 : 0 ≤ p
  · apply zr_fieldsTape_eq fs (fun q => zonedTape z (-(fieldOffset fs ℓ : ℤ) + q)) _ p h0
      (by simpa only [hlen] using hp')
    intro j hj q hq hq'
    have hj' : j < ℓ := by omega
    let i : Fin ℓ := (⟨j, hj'⟩ : Fin ℓ).rev
    have hi : i.val = ℓ - (j + 1) := Fin.val_rev _
    have hoff := zr_left_offset z j (by omega)
    have hs := zoneStart_succ i.val
    have he : ℓ - j = i.val + 1 := by omega
    rw [he] at hoff
    change fieldOffset fs j + zoneStart (i.val + 1) = zoneStart ℓ at hoff
    simp only [fs, List.getElem_ofFn, List.length_reverse, zoneCells_length] at hq' ⊢
    have hpos : -(fieldOffset fs ℓ : ℤ) + ((fieldOffset fs j : ℤ) + q) =
        -((zoneStart i : ℤ) + zoneCapacity i - 1) + q := by omega
    rw [hpos]
    exact zonedTape_left_word z i q (by omega) hq'
  · rw [fieldsTape_of_neg fs (by omega)]
    apply zonedTape_blank_outside
    rw [abs_of_nonpos (by omega)]
    omega

/-- A physical zone is a nonempty field, even when every virtual slot is empty. -/
private lemma zr_zoneCells_ne_nil {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ)
    (i : Fin ℓ) : zoneCells side z i ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [zoneCells_length]
  exact zr_capacity_pos i

/-- The right bridge discharges the seek-to-end contract's entire precondition. -/
private lemma zr_seekEnd_pre {k ℓ : ℕ} {x : List (ZoneSym k)}
    (z : Fin k → ZoneContents ℓ) (d : Cfg 2 (ZoneSym k) SeekPhase x)
    (hd : zoneRowPre ⟨ℓ, z⟩ d) :
    (seekEndTM_contract 0 x).pre
      ([.inr fun t => some (z t).home] :: List.ofFn (zoneCells true z)) d := by
  rw [seekEndTM_contract_pre]
  refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_cons, List.mem_ofFn] at hu
    rcases hu with rfl | ⟨i, rfl⟩
    · exact List.cons_ne_nil _ _
    · exact zr_zoneCells_ne_nil true z i
  · intro p hp he
    rw [hd.1, hd.2.1, zero_add]
    apply zr_zonedTape_right_fields z p hp
    simpa only [List.length_cons, List.length_ofFn] using he

/-- The left bridge discharges the seek-to-start contract's entire precondition. -/
private lemma zr_seekStart_pre {k ℓ : ℕ} {x : List (ZoneSym k)}
    (z : Fin k → ZoneContents ℓ) (d : Cfg 2 (ZoneSym k) SeekPhase x)
    (hd : zoneRowPre ⟨ℓ, z⟩ d) :
    (seekStartTM_contract 0 x).pre
      (List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse) d := by
  rw [seekStartTM_contract_pre]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact List.reverse_ne_nil_iff.mpr (zr_zoneCells_ne_nil false z i.rev)
  · rw [hd.1, hd.2.1, zonedTape_zero]
    exact Option.some_ne_none _
  · intro p hp he
    rw [hd.1, hd.2.1, zero_sub]
    simp only [List.length_ofFn] at he ⊢
    exact zr_zonedTape_left_fields z p hp he

/-- Two half-capacity walks from the old left layout stop one cell right of the new outer end.
This records the left-pass alignment obstruction in the continuation brief, without changing
either machine row's statement or implementing an amended route.

**Proof sketch.** The old layout starts at `2 - zoneStart ℓ`. Subtracting the new capacity
lands at `2 - zoneStart ℓ - zoneCapacity ℓ`; the new outermost cell is one cell farther left. -/
private lemma zr_left_two_walks {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) :
    -(fieldOffset (List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse) ℓ : ℤ) -
        (2 ^ ℓ : ℕ) - (2 ^ ℓ : ℕ) =
      -((zoneStart ℓ : ℤ) + zoneCapacity ℓ - 1) + 1 := by
  have ht := zr_left_offset z ℓ le_rfl
  simp only [Nat.sub_self] at ht
  have hz : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  rw [hz] at ht
  rw [zoneCapacity_eq]
  push_cast
  omega


/-- A right inward shift commutes with a left outward shift, including their guards.

**Proof sketch.** The home is fixed; each operation reads and writes only its own side.
The published field equations therefore give equal home, left and right fields. -/
private lemma zr_shift_commute {ℓ : ℕ} (i j : ℕ) (z : ZoneContents ℓ) :
    zoneShiftIn true i (zoneShiftOut false j z) =
      zoneShiftOut false j (zoneShiftIn true i z) := by
  have hl : (zoneShiftIn true i z).left = z.left := by
    funext t
    simp only [zoneShiftIn_left, if_true]
  have hr : (zoneShiftOut false j z).right = z.right := by
    funext t
    simp only [zoneShiftOut_right, Bool.false_eq_true, if_false]
  apply ZoneContents.ext'
  · simp only [zoneShiftIn_home, zoneShiftOut_home]
  · funext t
    simp only [zoneShiftIn_left, zoneShiftOut_left, Bool.false_eq_true, if_false, if_true, hl]
  · funext t
    simp only [zoneShiftIn_right, zoneShiftOut_right, Bool.false_eq_true, if_false, if_true, hr]

/-- A whole right-side pass commutes past one left-side outward shift.

**Proof sketch.** Induct on the pass list, commuting its first shift by the preceding lemma. -/
private lemma zr_inPass_out {ℓ : ℕ} (is : List ℕ) (j : ℕ) (z : ZoneContents ℓ) :
    is.foldl (fun a i => zoneShiftIn true (i + 1) a) (zoneShiftOut false j z) =
      zoneShiftOut false j (is.foldl (fun a i => zoneShiftIn true (i + 1) a) z) := by
  induction is generalizing z with
  | nil => simp only [List.foldl_nil]
  | cons i is ih =>
    rw [List.foldl_cons, zr_shift_commute, ih, List.foldl_cons]

/-- A list of guarded pairs equals its right-side pass followed by its left-side pass.

**Proof sketch.** Expand one pair by its public equation, use the induction hypothesis for
the remaining pairs, then move the first left shift past the remaining right pass. No guard
assumption is needed, so this applies to the total cascade on arbitrary zone contents. -/
private lemma zr_pair_pass {ℓ : ℕ} (is : List ℕ) (z : ZoneContents ℓ) :
    is.foldl (fun a i => zoneStepPair (i + 1) a) z =
      is.foldl (fun a i => zoneShiftOut false (i + 1) a)
        (is.foldl (fun a i => zoneShiftIn true (i + 1) a) z) := by
  induction is generalizing z with
  | nil => simp only [List.foldl_nil]
  | cons i is ih =>
    rw [List.foldl_cons, zoneStepPair_eq, ih, zr_inPass_out]
    simp only [List.foldl_cons]

/-- The total right cascade can perform each side's pass separately around the home move.

**Proof sketch.** Read the public cascade equation and apply the one shared pair-pass
reordering to the descending and ascending lists. The guarded home move stays between them. -/
private lemma zr_cascade_passes {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascadeRight j z =
      (List.range j).foldl (fun a i => zoneShiftOut false (i + 1) a)
        ((List.range j).foldl (fun a i => zoneShiftIn true (i + 1) a)
          (zoneMove true
            ((List.range j).reverse.foldl (fun a i => zoneShiftOut false (i + 1) a)
              ((List.range j).reverse.foldl (fun a i => zoneShiftIn true (i + 1) a) z)))) := by
  rw [zoneCascadeRight_eq]
  simp only [zr_pair_pass]


/-! ### The rows -/

/-- **§13d G4, the rebalance rows** (design §13d, G4; decisions 13d.2–13d.4). For every track
count `k` there is a constant `C` such that for every direction `dir` (`true` is a right head
move) and every track `t` (in finite control) there is one two-tape machine over
`Turing.ZoneSym k`, with an entry and two distinct live exits `done` and `short`, whose run is a
`Turing.Contract` with index `Turing.ZoneData k`:

* **precondition** `Turing.zoneRowPre`: the zoned tape of `⟨ℓ, z⟩` on tape `0`, head at home;
  the scratch tape blank;
* **endpoint** `Turing.zoneRebalancePost`: tape `0` holds the zoned tape of `z` with track `t`
  replaced by `Turing.zoneRebalance dir (z t)` — the **total** pure cascade at the scanned index
  `Turing.zoneShiftIndex dir (z t)` when that index is below `ℓ` (exit `done`), the identity
  when every feeding zone is empty (exit `short`, the extension's cue); every other track, every
  separator and every cell beyond the layout unchanged; the scratch tape blank again; both
  heads back; input position and output unchanged;
* **exact time** with the no-earlier-exit cut (the contract's fields), bounded by
  `C · (2^i₀ + 1)` for the scanned index `i₀`;
* **envelopes** `Turing.zoneRowLo`/`Turing.zoneRowHi` at `i₀`: the zoned head within
  `zoneStart (i₀ + 1)` of home, the scratch head within `C · (2^i₀ + 1)` of its start.

For every contents, not only the classical ones (decision 13d.3). [AB09, §1.7]: one shift of
index `i₀`, at cost `O(2^{i₀})`. Deviation: the book's machine assumes the fullness invariant;
this row realizes the guarded cascade on every input, and reports an exhausted feeding side.

**Proof sketch.** Fill plan (design note §4): scan outward on the feeding side from home: zone
`i` is nonempty on track `t` exactly when its innermost slot is occupied (inner packing), the
separators delimit the zones, and two consecutive blanks mark the end of the layout, so the
scan finds `i₀` in `O(2^{i₀})` steps or reaches the end (`short`: rewind and exit). Then run the
cascade's `2i₀ + 1` guarded steps in its order — the descending pairs `i₀, …, 1`, the home move,
the ascending pairs `1, …, i₀` — each pair at level `i` acting on zones `i - 1` and `i` of both
sides in `O(2^i)` steps: a guard is a test of one or two slots (inner packing); a pairwise move
copies the track-`t` column of the zones involved to the scratch tape with the mapped copy
(`extract := zoneSlotOf t`), re-packs it there by scans, and writes it back with the mapped copy
(`merge := zoneSlotSet t`), which keeps the other tracks and needs no save and restore, since
zones are delimited words (`Turing.zonedTape_right_word`, `Turing.zonedTape_left_word`); the
mirror side is reached through a scratch ruler of the distance to home. The scratch tape is
cleared before the exit. The sum `Σ_{i ≤ i₀} O(2^i)` is `O(2^{i₀})`
(`Turing.zoneCascade_cost_le`).

**Fill appendix (§13d G4).** The guards, scan-index facts, short identity, tape mirror, and
one-cell leaf are proved. The four inherited helpers now cite published equations. The pure
cascade's descending and ascending pair lists have a shared, checked side-pass reordering
(`zr_cascade_passes`), valid with every guard and no fullness assumption. The scan with both
exits, guarded column-move machines, machine passes, home move, and cleanup remain open.
Only this target's own body is admitted. -/
theorem exists_zoneRebalanceTM (k : ℕ) :
    ∃ C : ℕ, ∀ (dir : Bool) (t : Fin k),
      ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 2 (ZoneSym k) S)
        (entry done short : S), done ≠ short ∧
        ∀ x : List (ZoneSym k),
          ∃ R : Contract M entry {some done, some short} (ZoneData k) x,
            R.pre = zoneRowPre ∧
            R.post = zoneRebalancePost dir t done short ∧
            R.lo = zoneRowLo (zoneRebalanceIndex dir t) C ∧
            R.hi = zoneRowHi (zoneRebalanceIndex dir t) C ∧
            ∀ D d, d.state = some entry → R.pre D d →
              R.time D d ≤ C * (2 ^ zoneRebalanceIndex dir t D + 1) := by
  sorry

/-- **§13d G4, the extension row** (design §13d, decision 13d.2). For every track count `k`
there are a constant `C` and one two-tape machine over `Turing.ZoneSym k`, with an entry and a
live exit `done`, whose run is a `Turing.Contract` with index `Turing.ZoneData k`:

* **precondition** `Turing.zoneRowPre`;
* **endpoint** `Turing.zoneExtendPost`: tape `0` holds the zoned tape of the data extended by
  level `ℓ` on every track — on each side a separator and a fresh zone half full of virtual
  blanks (`Turing.zonedTape_extend` says which cells change); every other field unchanged;
* **exact time**, bounded by `C · (2^ℓ + 1)`;
* **envelopes** at level `ℓ`: the zoned head within `zoneStart (ℓ + 1)` of home, the scratch
  head within `C · (2^ℓ + 1)` of its start.

[AB09, §1.7]: zones are made half full "the first time we encounter it".

**Proof sketch.** Fill plan: walk right from home across the layout to the first of two
consecutive blanks (the separator after zone `ℓ - 1`); measure the new zone with a scratch
ruler of zone `ℓ - 1`'s length doubled (zone `ℓ` has twice its capacity; at `ℓ = 0` finite
control writes the two cells); write the inner half as all-tracks virtual blanks and the outer
half as all-`⊠` cells; return through home and do the same on the left, through a ruler of the
distance; clear the ruler and return home. Each phase is `O(2^ℓ)`.

**Fill appendix (§13d G4).** Both layout bridges, their offset formulas, and the complete
seek-contract preconditions are proved, alongside the inherited ruler-tail and one-cell kit.
The left route is stopped under ground rule 4: `zr_left_two_walks` proves that its prescribed
two half-capacity walks stop one cell right of the new zone's outermost cell (escalation E1).
The ruler builder, composed side passes, return-home rounds, and cleanup remain open. No route
amendment is implemented, and only this target's own body is admitted. -/
theorem exists_zoneExtendTM (k : ℕ) :
    ∃ (C : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (M : MultiTapeTM 2 (ZoneSym k) S) (entry done : S),
      ∀ x : List (ZoneSym k),
        ∃ R : Contract M entry {some done} (ZoneData k) x,
          R.pre = zoneRowPre ∧
          R.post = zoneExtendPost done ∧
          R.lo = zoneRowLo (fun D => D.1) C ∧
          R.hi = zoneRowHi (fun D => D.1) C ∧
          ∀ D d, d.state = some entry → R.pre D d → R.time D d ≤ C * (2 ^ D.1 + 1) := by
  sorry

/-! ### What the rows' endpoints say (proved from the definitions) -/

/-- **Rows chain**: the rebalance row's endpoint, with its state replaced (as every seam
does), satisfies the row precondition at the rebalanced data. -/
theorem zoneRowPre_rebalancePost {k : ℕ} (dir : Bool) (t : Fin k) {S S' : Type}
    {x : List (ZoneSym k)} (done short : S) (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x)
    (hp : zoneRowPre D d) (f : S → S') :
    zoneRowPre (zoneRebalanceData dir t D) ((zoneRebalancePost dir t done short D d).mapState f) :=
  ⟨rfl, hp.2.1, hp.2.2⟩

/-- **Rows chain**: the extension row's endpoint satisfies the row precondition at the
extended data. -/
theorem zoneRowPre_extendPost {k : ℕ} {S S' : Type} {x : List (ZoneSym k)} (done : S)
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) (hp : zoneRowPre D d) (f : S → S') :
    zoneRowPre (zoneExtendData D) ((zoneExtendPost done D d).mapState f) :=
  ⟨rfl, hp.2.1, hp.2.2⟩

/-- The rebalance exits at `done` exactly when its scanned index is below `ℓ`. -/
theorem zoneRebalancePost_state_done {k : ℕ} (dir : Bool) (t : Fin k) {S : Type}
    {x : List (ZoneSym k)} {done short : S} (hds : done ≠ short) (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) S x) :
    (zoneRebalancePost dir t done short D d).state = some done ↔
      zoneRebalanceIndex dir t D < D.1 := by
  simp only [zoneRebalancePost]
  split_ifs with h <;> simp [h, hds.symm]

/-- **A short exit leaves the data unchanged**: when every feeding zone of track `t` is empty
the rebalanced data is the data. -/
theorem zoneRebalanceData_of_short {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k)
    (h : ¬ zoneRebalanceIndex dir t D < D.1) : zoneRebalanceData dir t D = D := by
  obtain ⟨ℓ, z⟩ := D
  simp only [zoneRebalanceData, zoneRebalanceIndex] at h ⊢
  rw [zoneRebalance_of_le dir (z t) (by omega), Function.update_eq_self]

/-- **After a short exit, extend and retry**: the retried rebalance of the extended data scans
to the new level `ℓ`, below `ℓ + 1`, so it exits at `done`.

**Proof sketch.** A short exit means scanned index `ℓ` (`Turing.zoneShiftIndex_le`);
`Turing.zoneShiftIndex_extend`. -/
theorem zoneRebalanceIndex_extend_of_short {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k)
    (h : ¬ zoneRebalanceIndex dir t D < D.1) :
    zoneRebalanceIndex dir t (zoneExtendData D) = D.1 := by
  have hle := zoneShiftIndex_le dir (D.2 t)
  exact zoneShiftIndex_extend dir (D.2 t) (by unfold zoneRebalanceIndex at h; omega)

/-- **The rebalance frames the touched levels**: from an admissible start, its endpoint agrees
with the start outside the zoned tape's cells within `zoneStart (i₀ + 1)` of home (the levels up
to the scanned index `i₀`), and on the whole scratch tape.

**Proof sketch.** The scratch tape is the start's. On tape `0`, a cell farther out than
`zoneStart (i₀ + 1)` is a separator, beyond the layout, or owned by a zone above `i₀`, whose words
the rebalance keeps on track `t` (`Turing.zoneRebalance_frame`) and whose other tracks are
untouched. -/
theorem zoneRebalancePost_frames {k : ℕ} (dir : Bool) (t : Fin k) {S : Type}
    {x : List (ZoneSym k)} (done short : S) (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x)
    (hp : zoneRowPre D d) :
    Cfg.SameOutside (fun j => if j = 0 then
        Set.Icc (-(zoneStart (zoneRebalanceIndex dir t D + 1) : ℤ))
          (zoneStart (zoneRebalanceIndex dir t D + 1)) else ∅)
      d (zoneRebalancePost dir t done short D d) := by
  obtain ⟨ℓ, z⟩ := D
  intro j q hq
  simp only [zoneRebalancePost]
  split_ifs with hj
  · subst hj
    rw [hp.1]
    simp only [if_true, Set.mem_Icc, not_and_or, not_le] at hq
    set i₀ := zoneRebalanceIndex dir t ⟨ℓ, z⟩ with hi₀
    have key : ∀ (side : Bool) (n : ℕ), zoneStart (i₀ + 1) < n →
        zoneCellAt side (zoneRebalanceData dir t ⟨ℓ, z⟩).2 n = zoneCellAt side z n := by
      intro side n hn
      simp only [zoneCellAt, zoneRebalanceData]
      cases ho : zoneOwner ℓ n with
      | none => rfl
      | some i =>
        have hi := (Fin.find_eq_some_iff.mp ho).1
        have hgt : i₀ < i.val := by
          by_contra hle
          have := zoneStart_mono (show i.val + 1 ≤ i₀ + 1 by omega)
          have := zoneStart_succ i.val
          omega
        have hfr := zoneRebalance_frame dir (z t) i hgt
        simp only [Option.map_some]
        congr 2
        funext s
        by_cases hs : s = t
        · subst hs
          rw [Function.update_self]
          cases side
          · simp [ZoneContents.words, hfr.1]
          · simp [ZoneContents.words, hfr.2]
        · rw [Function.update_of_ne hs]
    unfold zonedTape
    have h0 : q ≠ 0 := by
      have := two_le_zoneStart (i₀ + 1)
      omega
    rw [if_neg h0, if_neg h0]
    split_ifs with hpos
    · exact key true _ (by omega)
    · exact key false _ (by omega)
  · rfl

/-- **The extension frames the new level**: from an admissible start, its endpoint agrees with
the start outside the two new zones on tape `0`, and on the whole scratch tape.

**Proof sketch.** `Turing.zonedTape_extend`: outside the new zones the extended tape is the old
one. -/
theorem zoneExtendPost_frames {k : ℕ} {S : Type} {x : List (ZoneSym k)} (done : S)
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) (hp : zoneRowPre D d) :
    Cfg.SameOutside (fun j => if j = 0 then
        {c : ℤ | (zoneStart D.1 : ℤ) ≤ |c| ∧ |c| < zoneStart D.1 + zoneCapacity D.1} else ∅)
      d (zoneExtendPost done D d) := by
  intro j q hq
  simp only [zoneExtendPost]
  split_ifs with hj
  · subst hj
    rw [hp.1]
    simp only [if_true, Set.mem_setOf_eq] at hq
    rw [zoneExtendData, zonedTape_extend, if_neg hq]
  · rfl

end Turing
