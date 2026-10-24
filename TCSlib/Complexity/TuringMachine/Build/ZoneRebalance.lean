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

/-- Restate a contract's exit set by an equality, without changing any of its fields.

**Proof sketch.** Re-wrap its segment and exit membership through the set equality. -/
private abbrev zr_exitsContract {n : ℕ} {Γ S I : Type} {x : List Γ}
    {M : MultiTapeTM n Γ S} {entry : S} {X : Set (Option S)}
    (R : Contract M entry X I x) (X' : Set (Option S)) (hX : X = X') :
    Contract M entry X' I x :=
  Contract.ofSegment R.pre R.time R.post R.lo R.hi
    (fun i d hd hp => by rw [← hX]; exact R.segment i d hd hp)
    (fun i d hd hp => by rw [← hX]; exact R.exit_mem i d hd hp)

/-- Normalize a composite's singleton exit without changing any of its contract fields. -/
private abbrev zr_singletonContract {n : ℕ} {Γ S I : Type} {x : List Γ}
    {M : MultiTapeTM n Γ S} {entry : S} {X : Set (Option S)}
    (R : Contract M entry X I x) (done : S)
    (hX : X = {some done} := by simp only [Set.image_singleton, Option.map_some]) :
    Contract M entry {some done} I x :=
  zr_exitsContract R {some done} hX

/-- The normalized composite has the composite's fields. -/
private lemma zr_singleton_fields {n : ℕ} {Γ S I : Type} {x : List Γ}
    {M : MultiTapeTM n Γ S} {entry : S} {X : Set (Option S)}
    (R : Contract M entry X I x) (done : S) (hX : X = {some done}) (i : I) (d : Cfg n Γ S x) :
    (zr_singletonContract R done hX).pre i d = R.pre i d ∧
      (zr_singletonContract R done hX).time i d = R.time i d ∧
      (zr_singletonContract R done hX).post i d = R.post i d ∧
      ∀ j, (zr_singletonContract R done hX).lo i d j = R.lo i d j ∧
        (zr_singletonContract R done hX).hi i d j = R.hi i d j := by
  simp only [zr_singletonContract, zr_exitsContract, Contract.ofSegment_pre,
    Contract.ofSegment_time, Contract.ofSegment_post, Contract.ofSegment_lo,
    Contract.ofSegment_hi, and_self, implies_true]

/-- A redirected configuration is determined by its redirected state and its other fields. -/
private lemma zr_bindState_eq {n : ℕ} {Γ S S' : Type} {x : List Γ} (e : Cfg n Γ S x)
    (r : S → Option S') (y : Cfg n Γ S' x) (hs : e.state.bind r = y.state)
    (hi : e.inputPos = y.inputPos) (ht : e.workTapes = y.workTapes)
    (hp : e.workTapePos = y.workTapePos) (ho : e.output = y.output) : e.bindState r = y :=
  Cfg.ext ((Cfg.bindState_state e r).trans hs) ((Cfg.bindState_inputPos e r).trans hi)
    (funext fun j => funext fun q =>
      (Cfg.bindState_workTapes e r j q).trans (congrFun (congrFun ht j) q))
    (funext fun j => (Cfg.bindState_workTapePos e r j).trans (congrFun hp j))
    ((Cfg.bindState_output e r).trans ho)

/-- Re-index a contract through `f`, under a precondition `P` that implies the original's at
`f j`. Every other field and the segment are the original's at `f j`. -/
private def zr_reindexContract {n : ℕ} {Γ S I J : Type} {x : List Γ}
    {M : MultiTapeTM n Γ S} {entry : S} {X : Set (Option S)}
    (R : Contract M entry X I x) (f : J → I) (P : J → Cfg n Γ S x → Prop)
    (hP : ∀ j d, P j d → R.pre (f j) d) : Contract M entry X J x :=
  Contract.ofSegment P (fun j d => R.time (f j) d) (fun j d => R.post (f j) d)
    (fun j d => R.lo (f j) d) (fun j d => R.hi (f j) d)
    (fun j d hd hp => R.segment (f j) d hd (hP j d hp))
    (fun j d hd hp => R.exit_mem (f j) d hd (hP j d hp))

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
        rw [Nat.cast_zero, zero_add, ← Nat.cast_one, FinTM.bufferTape_nat]
        simpa only [Nat.cast_one, List.getElem?_cons_succ, List.getElem?_nil] using hsep
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

/-- The left bridge discharges the seek-to-start contract's entire precondition, from two local
facts: the zoned head at home, and tape `0` agreeing with the zoned tape on `[-zoneStart ℓ, 0]`.
Nothing is required of the right half-line or of the scratch tape. -/
private lemma zr_seekStart_pre {k ℓ : ℕ} {x : List (ZoneSym k)}
    (z : Fin k → ZoneContents ℓ) (d : Cfg 2 (ZoneSym k) SeekPhase x) (h0 : d.workTapePos 0 = 0)
    (hz : ∀ q : ℤ, -(zoneStart ℓ : ℤ) ≤ q → q ≤ 0 → d.workTapes 0 q = zonedTape z q) :
    (seekStartTM_contract 0 x).pre
      (List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse) d := by
  have ht := zr_left_offset z ℓ le_rfl
  have hs : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  rw [Nat.sub_self, hs] at ht
  rw [seekStartTM_contract_pre, h0]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact List.reverse_ne_nil_iff.mpr (zr_zoneCells_ne_nil false z i.rev)
  · rw [hz 0 (by omega) le_rfl, zonedTape_zero]
    exact Option.some_ne_none _
  · intro p hp he
    simp only [List.length_ofFn] at he ⊢
    rw [zero_sub, hz (-(fieldOffset (List.ofFn fun i : Fin ℓ =>
      (zoneCells false z i.rev).reverse) ℓ : ℤ) + p) (by omega) (by omega)]
    exact zr_zonedTape_left_fields z p hp he

/-- One step and two adjusted walks by the half-capacity reach the new left zone's outermost
cell from the seek's stop, across the separating blank: `2 · 2^ℓ + 1` cells.

**Proof sketch.** The seek stops at `2 - zoneStart ℓ` (`zr_left_offset`); the new zone and its
separator span `zoneStart (ℓ + 1) - zoneStart ℓ = 2 · 2^ℓ + 1` cells. -/
private lemma zr_left_reach {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) :
    -(fieldOffset (List.ofFn fun i : Fin ℓ => (zoneCells false z i.rev).reverse) ℓ : ℤ) - 1 -
        2 * (2 ^ ℓ : ℕ) = 2 - zoneStart (ℓ + 1) := by
  have ht := zr_left_offset z ℓ le_rfl
  have hs := zoneStart_succ ℓ
  have hz : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  rw [Nat.sub_self, hz] at ht
  rw [zoneCapacity_eq] at hs
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

/-- The home followed by the existing right-zone words. -/
private def zr_rightFields {k : ℕ} (D : ZoneData k) : List (List (ZoneSym k)) :=
  [.inr fun t => some (D.2 t).home] :: List.ofFn (zoneCells true D.2)

/-- The last field of the right layout: the final right zone, or the home when no zone is laid
out. Either way its length is the new zone's half-capacity, so it measures the new zone. -/
private def zr_rightWord {k : ℕ} : ZoneData k → List (ZoneSym k)
  | ⟨0, z⟩ => [.inr fun t => some (z t).home]
  | ⟨n + 1, z⟩ => zoneCells true z ⟨n, Nat.lt_succ_self n⟩

/-- The last field has the new zone's half-capacity. -/
private lemma zr_rightWord_length {k : ℕ} (D : ZoneData k) :
    (zr_rightWord D).length = 2 ^ D.1 := by
  obtain ⟨_ | n, z⟩ := D
  · rfl
  · rw [zr_rightWord, zoneCells_length]
    exact zr_ruler_length (n + 1) (by omega)

/-- The home is the delimited one-cell field at cell `0`. -/
private lemma zr_home_word {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) :
    ∀ p : ℤ, -1 ≤ p → p ≤ 1 →
      zonedTape z p = FinTM.bufferTape [Sum.inr fun t => some (z t).home] p := by
  intro p h1 h2
  have h0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  rcases (show p = -1 ∨ p = 0 ∨ p = 1 by omega) with rfl | rfl | rfl
  · have hsep := zonedTape_left_sep z 0
    rw [h0] at hsep
    rw [FinTM.bufferTape_left]
    simpa only [Nat.cast_ofNat] using hsep
  · rw [zonedTape_zero]
    simpa only [Nat.cast_zero, List.getElem?_cons_zero] using
      (FinTM.bufferTape_nat [(Sum.inr fun t => some (z t).home : ZoneSym k)] 0).symm
  · have hsep := zonedTape_right_sep z 0
    rw [h0] at hsep
    rw [← Nat.cast_one, FinTM.bufferTape_nat]
    simpa only [Nat.cast_ofNat, List.getElem?_cons_succ, List.getElem?_nil] using hsep

/-- The last field is the delimited word ending one blank before the new zone's first cell. -/
private lemma zr_rightWord_word {k : ℕ} (D : ZoneData k) :
    ∀ p : ℤ, -1 ≤ p → p ≤ ((zr_rightWord D).length : ℤ) →
      zonedTape D.2 ((zoneStart D.1 : ℤ) - (zr_rightWord D).length - 1 + p) =
        FinTM.bufferTape (zr_rightWord D) p := by
  obtain ⟨_ | n, z⟩ := D
  · intro p h1 h2
    have h0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
    simp only [zr_rightWord, List.length_singleton, h0] at h2 ⊢
    rw [show ((2 : ℕ) : ℤ) - (1 : ℕ) - 1 + p = p by omega]
    exact zr_home_word z p h1 (by omega)
  · intro p h1 h2
    simp only [zr_rightWord, zoneCells_length] at h2 ⊢
    have hs := zoneStart_succ n
    rw [show ((zoneStart (n + 1) : ℕ) : ℤ) - zoneCapacity n - 1 + p = (zoneStart n : ℤ) + p by
      omega]
    exact zonedTape_right_word z ⟨n, Nat.lt_succ_self n⟩ p h1 h2

/-- Seeking the right end from a zoned input is a contract indexed by the zone data.
The segment constructor retains the seek row's exact time, endpoint, and envelope. -/
private def zr_rightSeekContract {k : ℕ} (x : List (ZoneSym k)) :
    Contract (seekEndTM 2 0) SeekPhase.run {some SeekPhase.done} (ZoneData k) x :=
  let R := seekEndTM_contract 0 x
  Contract.ofSegment
    (fun D d => zoneRowPre D d)
    (fun D d => R.time (zr_rightFields D) d)
    (fun D d => R.post (zr_rightFields D) d)
    (fun D d => R.lo (zr_rightFields D) d)
    (fun D d => R.hi (zr_rightFields D) d)
    (fun D d hd hp => R.segment _ d hd (zr_seekEnd_pre D.2 d hp))
    (fun D d hd hp => R.exit_mem _ d hd (zr_seekEnd_pre D.2 d hp))

/-- After seeking the right end, the last field satisfies the backward skip's premise. -/
private lemma zr_rightSeek_back_pre {k : ℕ} {x : List (ZoneSym k)}
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) SeekPhase x)
    (hp : (zr_rightSeekContract x).pre D d) :
    (skipBackTM_contract 0 x).pre (zr_rightWord D)
      (((zr_rightSeekContract x).post D d).mapState fun _ => SeekPhase.run) := by
  have hz : zoneRowPre D d := by
    simpa only [zr_rightSeekContract, Contract.ofSegment_pre] using hp
  rw [skipBackTM_contract_pre]
  intro p hleft hright
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_rightSeekContract,
    Contract.ofSegment_post, seekEndTM_contract_post, seekPost_workTapes,
    seekPost_workTapePos, Function.update_self, zr_rightFields,
    List.length_cons, List.length_ofFn] at hright ⊢
  rw [hz.1, hz.2.1, zero_add, zr_right_offset D.2 D.1 le_rfl]
  exact zr_rightWord_word D p hleft hright

/-- The first two phases reach the last old right zone through one stationary seam. -/
private def zr_rightSeekBackContract {k : ℕ} (x : List (ZoneSym k)) :
    Contract (seamCompTM (seekEndTM 2 0) SeekPhase.done (skipBackTM 2 0) SeekPhase.run)
      (Sum.inl SeekPhase.run) {some (Sum.inr SeekPhase.done)} (ZoneData k) x :=
  let R := (zr_rightSeekContract x).seq (skipBackTM_contract 0 x) zr_rightWord
    (fun D d _ hp => zr_rightSeek_back_pre D d hp)
  zr_singletonContract R (Sum.inr SeekPhase.done)

/-- The seek-and-back composite preserves all tapes and leaves the zoned head at the last
field's first cell. Its scratch head, input position, and output are unchanged.

**Proof sketch.** Read the two seek endpoints through the seam's endpoint equation. The
second displacement is the last field and its separator. -/
private lemma zr_rightSeekBack_post {k : ℕ} {x : List (ZoneSym k)}
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ SeekPhase) x)
    (hp : (zr_rightSeekBackContract x).pre D d) :
    (zr_rightSeekBackContract x).post D d =
      seekPost (Sum.inr SeekPhase.done) 0 ((zoneStart D.1 : ℤ) - (2 ^ D.1 : ℕ) - 1) d := by
  have hz : zoneRowPre D d := by
    simpa only [zr_rightSeekBackContract, Contract.ofSegment_pre, Contract.seq_pre,
      zr_rightSeekContract,
      Contract.ofSegment_pre, zoneRowPre, funext_iff, Cfg.mapState_workTapes,
      Cfg.mapState_workTapePos] using hp
  simp only [zr_rightSeekBackContract, Contract.ofSegment_post, Contract.seq_post,
    zr_rightSeekContract, seekEndTM_contract_post, skipBackTM_contract_post,
    zr_rightFields, zr_rightWord_length, List.length_cons, List.length_ofFn]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, seekPost_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos, seekPost_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes, seekPost_workTapes]
  · funext j
    simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self]
    by_cases hj : j = 0
    · subst j
      simp only [Function.update_self, hz.2.1, zero_add, zr_right_offset D.2 D.1 le_rfl]
    · simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos, seekPost_workTapePos]
  · simp only [Cfg.mapState_output, seekPost_output]

/-- Copying the last field to scratch as a constant nonblank word makes the ruler. -/
private def zr_rulerCopyContract {k : ℕ} (x : List (ZoneSym k)) :=
  copyMapTM_contract (Γ := ZoneSym k) (0 : Fin 2) 1 (by decide)
    (fun _ => ()) (fun _ _ => Sum.inl false) x

/-- The mapped ruler copy leaves its source word and both heads unchanged, so the source
can immediately be skipped. -/
private lemma zr_rulerCopy_skip_pre {k : ℕ} {x : List (ZoneSym k)}
    (w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) SweepPhase x)
    (hp : (zr_rulerCopyContract x).pre w d) :
    (skipTM_contract 0 x).pre w
      (((zr_rulerCopyContract x).post w d).mapState fun _ => SeekPhase.run) := by
  rw [zr_rulerCopyContract, copyMapTM_contract_pre] at hp
  rw [skipTM_contract_pre]
  intro p hp0 hp1
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_rulerCopyContract,
    copyMapTM_contract_post, sweepPost_workTapePos]
  simp only [sweepPost_workTapes, show (0 : Fin 2) ≠ 1 by decide, false_and, if_false]
  exact hp p (by omega) hp1

/-- Copy the source field to scratch as a ruler, then skip the source field.
The seam contributes one step beyond the two catalog rows. -/
private def zr_rulerSkipContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_rulerCopyContract x).seq (skipTM_contract 0 x) (fun w => w)
    (fun w d _ hp => zr_rulerCopy_skip_pre w d hp)

/-- The seek-and-back endpoint supplies the delimited last field for the ruler copy. -/
private lemma zr_rightSeekBack_ruler_pre {k : ℕ} {x : List (ZoneSym k)}
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ SeekPhase) x)
    (hp : (zr_rightSeekBackContract x).pre D d) :
    (zr_rulerSkipContract x).pre (zr_rightWord D)
      (((zr_rightSeekBackContract x).post D d).mapState fun _ =>
        Sum.inl SweepPhase.sweep) := by
  have hz : zoneRowPre D d := by
    simpa only [zr_rightSeekBackContract, Contract.ofSegment_pre, Contract.seq_pre,
      zr_rightSeekContract, zoneRowPre, funext_iff, Cfg.mapState_workTapes,
      Cfg.mapState_workTapePos] using hp
  rw [zr_rulerSkipContract, Contract.seq_pre, zr_rulerCopyContract,
    copyMapTM_contract_pre]
  intro p hleft hright
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
    zr_rightSeekBack_post D d hp, seekPost_workTapes, seekPost_workTapePos,
    Function.update_self, hz.1]
  have h := zr_rightWord_word D p hleft hright
  rwa [zr_rightWord_length] at h

/-- Seek the right end, return to the last field, copy its length to scratch, and skip back to
the new zone's first cell. Every phase is a public row joined by stationary seams. -/
private def zr_rightRulerContract {k : ℕ} (x : List (ZoneSym k)) :=
  let R := (zr_rightSeekBackContract x).seq (zr_rulerSkipContract x) zr_rightWord
    (fun D d _ hp => zr_rightSeekBack_ruler_pre D d hp)
  zr_singletonContract R (Sum.inr (Sum.inr SeekPhase.done))

/-- The ruler prefix requires exactly the original zoned input. -/
private lemma zr_rightRuler_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_rightRulerContract x).pre D d = zoneRowPre D d := by
  simp only [zr_rightRulerContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_rightSeekBackContract, zr_rightSeekContract, zoneRowPre, funext_iff,
    Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- A constant mapped copy writes exactly its destination interval. This single formula
covers the scratch ruler and both half-zone writes. -/
private lemma zr_constantCopy_cell {k : ℕ} {x : List (ZoneSym k)}
    (src dst : Fin 2) (hne : src ≠ dst) (a : ZoneSym k) (w : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) SweepPhase x) (j : Fin 2) (q : ℤ) :
    ((copyMapTM_contract src dst hne (fun _ => ()) (fun _ _ => a) x).post w d).workTapes
        j q =
      if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
      then some a else d.workTapes j q := by
  rw [copyMapTM_contract_post_workTapes]
  split_ifs with h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, q - d.workTapePos j = n :=
      ⟨(q - d.workTapePos j).toNat, by omega⟩
    have hnlt : n < w.length := by omega
    simp only [hn, FinTM.bufferTape_nat, List.getElem?_eq_getElem hnlt, Option.map_some]
  · rfl

/-- The ruler prefix preserves the zoned tape, writes one constant ruler on scratch, and
returns the zoned head to the new zone's first cell.

**Proof sketch.** Substitute the seek-and-back endpoint into the copy-and-skip endpoint.
The copy changes only scratch, and skipping the last field cancels the backward displacement. -/
private lemma zr_rightRuler_post {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) ((SeekPhase ⊕ SeekPhase) ⊕ (SweepPhase ⊕ SeekPhase)) x)
    (hp : (zr_rightRulerContract x).pre D d) :
    (zr_rightRulerContract x).post D d =
      { d with
        state := some (Sum.inr (Sum.inr SeekPhase.done))
        workTapes := fun j q =>
          if j = 1 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + ((2 ^ D.1 : ℕ) : ℤ)
          then some (Sum.inl false) else d.workTapes j q
        workTapePos := Function.update d.workTapePos 0 (zoneStart D.1) } := by
  have hp0 : (zr_rightSeekBackContract x).pre D
      (d.mapState fun _ => Sum.inl SeekPhase.run) := by
    simpa only [zr_rightRulerContract, Contract.ofSegment_pre, Contract.seq_pre] using hp
  rw [zr_rightRulerContract, Contract.ofSegment_post, Contract.seq_post,
    zr_rightSeekBack_post D _ hp0,
    zr_rulerSkipContract, Contract.seq_post, skipTM_contract_post]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, seekPost_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos, seekPost_inputPos, zr_rulerCopyContract,
      copyMapTM_contract_post, sweepPost_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes, seekPost_workTapes, zr_rulerCopyContract,
      zr_constantCopy_cell, Cfg.mapState_workTapePos, seekPost_workTapePos,
      zr_rightWord_length]
    by_cases hj : j = 1
    · subst j
      simp only [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Cfg.mapState_workTapePos]
    · simp only [hj, false_and, if_false]
  · funext j
    simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, zr_rulerCopyContract,
      copyMapTM_contract_post, sweepPost_workTapePos, zr_rightWord_length,
      Function.update_self]
    by_cases hj : j = 0
    · subst j
      simp only [Function.update_self]
      omega
    · simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos, seekPost_workTapePos,
        sweepPost_workTapePos]
  · simp only [Cfg.mapState_output, seekPost_output, zr_rulerCopyContract,
      copyMapTM_contract_post, sweepPost_output]

/-- Advance one work head by one cell, restricting the existing leaf's verdict to its constant
choice; the index and the precondition are the caller's. This introduces no transition or new
leaf: the fields and the segment are the leaf's. -/
private def zr_stepContract {k : ℕ} {ι : Type} (i : Fin 2) (dir : SignType)
    (x : List (ZoneSym k)) (P : ι → Cfg 2 (ZoneSym k) (Option Bool) x → Prop)
    (wr : Option (Option (ZoneSym k)) := none) :
    Contract (zr_cellTM i (fun _ => false) wr dir) none {some (some false)} ι x :=
  let C := zr_cellContract i (fun _ => false) wr dir x
  Contract.ofSegment P
    (fun _ d => C.time () d) (fun _ d => C.post () d)
    (fun _ d => C.lo () d) (fun _ d => C.hi () d)
    (fun _ d hd _ => (C.segment () d hd trivial).mono
      (fun q hq => by
        obtain rfl := Set.mem_singleton_iff.mp hq
        exact ⟨false, rfl⟩)
      (fun _ h => h))
    (fun _ _ _ _ => Set.mem_singleton_iff.mpr rfl)

/-- Advance just the scratch head once along a nonempty ruler read in direction `dir`. -/
private def zr_rulerStepContract {k : ℕ} (dir : SignType) (x : List (ZoneSym k)) :
    Contract (zr_cellTM 1 (fun _ => false) none dir) none {some (some false)}
      (List (ZoneSym k)) x :=
  zr_stepContract 1 dir x fun w d => w ≠ [] ∧ ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes 1 (d.workTapePos 1 + (dir : ℤ) * p) = FinTM.bufferTape w p

/-- After the scratch-only advance, the tail of the ruler is the walk row's directed word. -/
private lemma zr_rulerStep_walk_pre {k : ℕ} {x : List (ZoneSym k)} (dir : SignType)
    (w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) (Option Bool) x)
    (hp : (zr_rulerStepContract dir x).pre w d) :
    (walkTM_contract 1 (fun _ : Fin 2 => True) trivial dir x).pre w.tail
      (((zr_rulerStepContract dir x).post w d).mapState fun _ => SeekPhase.run) := by
  rw [zr_rulerStepContract, zr_stepContract, Contract.ofSegment_pre] at hp
  rw [walkTM_contract_pre]
  intro p hlen
  have hword : ∀ n : ℕ, n ≤ w.length →
      d.workTapes 1 (d.workTapePos 1 + (dir : ℤ) * n) = FinTM.bufferTape w n :=
    fun n hn => hp.2 n (by omega) (by omega)
  have htail := zr_ruler_tail (d.workTapes 1) (d.workTapePos 1) dir w hp.1 hword p hlen
  simpa only [zr_rulerStepContract, zr_stepContract, Contract.ofSegment_post, zr_cellContract,
    zr_cellPost, Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Function.update_self,
    FinTM.bufferTape_nat] using htail

/-- Advancing the ruler alone and walking its tail moves the zoned head by exactly the
ruler length along `dir`. The scratch head moves one cell farther, past the far delimiter. -/
private def zr_adjustedWalkContract {k : ℕ} (dir : SignType) (x : List (ZoneSym k)) :
    Contract (seamCompTM (zr_cellTM 1 (fun _ => false) none dir) (some false)
      (walkTM 2 1 (fun _ => True) dir) SeekPhase.run)
      (Sum.inl none) {some (Sum.inr SeekPhase.done)} (List (ZoneSym k)) x :=
  let R := (zr_rulerStepContract dir x).seq
    (walkTM_contract 1 (fun _ : Fin 2 => True) trivial dir x) List.tail
    (fun w d _ hp => zr_rulerStep_walk_pre dir w d hp)
  zr_singletonContract R (Sum.inr SeekPhase.done)

/-- The adjusted walk preserves the tapes and has the two advertised head displacements.

**Proof sketch.** The leaf moves only scratch. The tail walk adds the ruler length to each
head along `dir`, since a nonempty list's tail is one cell shorter. -/
private lemma zr_adjustedWalk_post {k : ℕ} {x : List (ZoneSym k)} (dir : SignType)
    (w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) ((Option Bool) ⊕ SeekPhase) x)
    (hw : w ≠ []) :
    (zr_adjustedWalkContract dir x).post w d =
      { d with
        state := some (Sum.inr SeekPhase.done)
        workTapePos := fun j =>
          d.workTapePos j + (dir : ℤ) * w.length + if j = 1 then (dir : ℤ) else 0 } := by
  have hlen : w.tail.length + 1 = w.length := by
    have hpos := List.length_pos_iff_ne_nil.mpr hw
    rw [List.length_tail]
    omega
  simp only [zr_adjustedWalkContract, Contract.ofSegment_post, Contract.seq_post,
    zr_rulerStepContract, zr_stepContract, walkTM_contract_post, zr_cellContract, zr_cellPost]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes]
  · funext j
    have hlen' : (w.length : ℤ) = w.tail.length + 1 := by
      rw [← hlen]
      push_cast
      ring
    simp only [Cfg.mapState_workTapePos, if_true]
    by_cases hj : j = 1
    · subst j
      simp only [Function.update_self, if_true]
      rw [hlen']
      ring
    · simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos, if_neg hj, add_zero]
      rw [hlen']
  · simp only [Cfg.mapState_output]

/-- The adjusted walk stops scratch exactly one blank beyond its ruler, ready for skip-back. -/
private lemma zr_adjustedWalk_back_pre {k : ℕ} {x : List (ZoneSym k)}
    (w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) ((Option Bool) ⊕ SeekPhase) x)
    (hp : (zr_adjustedWalkContract 1 x).pre w d) :
    (skipBackTM_contract 1 x).pre w
      (((zr_adjustedWalkContract 1 x).post w d).mapState fun _ => SeekPhase.run) := by
  have h := hp
  rw [zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_rulerStepContract, zr_stepContract, Contract.ofSegment_pre] at h
  rw [skipBackTM_contract_pre]
  intro p hleft hright
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
    zr_adjustedWalk_post 1 w d h.1, if_true, SignType.coe_one, one_mul]
  have he : d.workTapePos 1 + (w.length : ℤ) + 1 - w.length - 1 + p =
      d.workTapePos 1 + p := by omega
  rw [he]
  simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, SignType.coe_one, one_mul]
    using h.2 p hleft hright

/-- The adjusted walk followed by scratch rewind advances only the zoned head by one ruler
length, restoring scratch to the beginning of its delimited word. -/
private def zr_adjustedBackContract {k : ℕ} (x : List (ZoneSym k)) :=
  let R := (zr_adjustedWalkContract 1 x).seq (skipBackTM_contract 1 x) (fun w => w)
    (fun w d _ hp => zr_adjustedWalk_back_pre w d hp)
  zr_singletonContract R (Sum.inr SeekPhase.done)

/-- Rewinding scratch after the adjusted walk restores its head and keeps both tapes.
Only the zoned head remains displaced, by the ruler length.

**Proof sketch.** The contract is the adjusted walk sequenced with skip back and re-wrapped. Its
precondition gives the walk's; the walk's endpoint (`zr_adjustedWalk_post`) is skip back's
start (`skipBackTM_contract_post`). Compare the fields: the state and the input position
directly, both tapes unchanged, the scratch head back at its start and the zoned head advanced
by `|w|`. -/
private lemma zr_adjustedBack_post {k : ℕ} {x : List (ZoneSym k)}
    (w : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) (((Option Bool) ⊕ SeekPhase) ⊕ SeekPhase) x)
    (hp : (zr_adjustedBackContract x).pre w d) :
    (zr_adjustedBackContract x).post w d =
      { d with
        state := some (Sum.inr SeekPhase.done)
        workTapePos := fun j => d.workTapePos j + if j = 0 then w.length else 0 } := by
  have hp0 : (zr_adjustedWalkContract 1 x).pre w (d.mapState fun _ => Sum.inl none) := by
    simpa only [zr_adjustedBackContract, Contract.ofSegment_pre, Contract.seq_pre] using hp
  rw [zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_rulerStepContract, zr_stepContract, Contract.ofSegment_pre] at hp0
  rw [zr_adjustedBackContract, Contract.ofSegment_post, Contract.seq_post,
    zr_adjustedWalk_post 1 w _ hp0.1, skipBackTM_contract_post]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, seekPost_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos, seekPost_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes, seekPost_workTapes]
  · funext j
    by_cases hj : j = 1
    · subst j
      simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
        show (1 : Fin 2) ≠ 0 by decide, if_false, if_true, Nat.cast_zero, add_zero,
        SignType.coe_one, one_mul]
      omega
    · have hj0 : j = 0 := by omega
      subst j
      simp only [Cfg.mapState_workTapePos, seekPost_workTapePos,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
        show (0 : Fin 2) ≠ 1 by decide, if_false, if_true, add_zero, SignType.coe_one, one_mul]
  · simp only [Cfg.mapState_output, seekPost_output]

/-- A half-zone copy reads the scratch ruler and writes either stored virtual blanks or
empty slots on every track of tape zero. -/
private def zr_halfCopyContract {k : ℕ} (inner : Bool) (x : List (ZoneSym k)) :=
  copyMapTM_contract (Γ := ZoneSym k) (1 : Fin 2) 0 (by decide)
    (fun _ => ()) (fun _ _ => Sum.inr fun _ => if inner then some none else none) x

/-- The inner-half copy with a nonempty ruler, retaining the source word for the adjusted
walk. Its fields and segment are those of the mapped-copy row. -/
private def zr_innerCopyContract {k : ℕ} (x : List (ZoneSym k)) :=
  let C := zr_halfCopyContract true x
  Contract.ofSegment
    (fun w d => w ≠ [] ∧ C.pre w d) C.time C.post C.lo C.hi
    (fun w d hd hp => C.segment w d hd hp.2)
    (fun w d hd hp => C.exit_mem w d hd hp.2)

/-- The inner copy preserves the nonempty scratch ruler needed by the adjusted walk. -/
private lemma zr_innerCopy_adjusted_pre {k : ℕ} {x : List (ZoneSym k)}
    (w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) SweepPhase x)
    (hp : (zr_innerCopyContract x).pre w d) :
    (zr_adjustedBackContract x).pre w
      (((zr_innerCopyContract x).post w d).mapState fun _ => Sum.inl (Sum.inl none)) := by
  rw [zr_innerCopyContract, Contract.ofSegment_pre, zr_halfCopyContract,
    copyMapTM_contract_pre] at hp
  rw [zr_adjustedBackContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_rulerStepContract, zr_stepContract, Contract.ofSegment_pre]
  refine ⟨hp.1, ?_⟩
  intro p hleft hright
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_innerCopyContract,
    Contract.ofSegment_post, zr_halfCopyContract, copyMapTM_contract_post,
    sweepPost_workTapePos, sweepPost_workTapes, show (1 : Fin 2) ≠ 0 by decide,
    false_and, if_false]
  simpa only [SignType.coe_one, one_mul] using hp.2 p hleft hright

/-- After the adjusted walk and scratch rewind, the original ruler is ready for the
outer-half mapped copy. -/
private lemma zr_adjustedBack_copy_pre {k : ℕ} {x : List (ZoneSym k)}
    (w : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) (((Option Bool) ⊕ SeekPhase) ⊕ SeekPhase) x)
    (hp : (zr_adjustedBackContract x).pre w d) :
    (zr_halfCopyContract false x).pre w
      (((zr_adjustedBackContract x).post w d).mapState fun _ => SweepPhase.sweep) := by
  have h := hp
  rw [zr_adjustedBackContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_rulerStepContract, zr_stepContract, Contract.ofSegment_pre] at h
  rw [zr_halfCopyContract, copyMapTM_contract_pre]
  intro p hleft hright
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
    zr_adjustedBack_post w d hp, show (1 : Fin 2) ≠ 0 by decide,
    if_false, Nat.cast_zero, add_zero]
  simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, SignType.coe_one, one_mul]
    using h.2 p hleft hright

/-- Move from the inner to the outer half, rewind the ruler, and write the empty slots. -/
private def zr_outerHalfContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_adjustedBackContract x).seq (zr_halfCopyContract false x) (fun w => w)
    (fun w d _ hp => zr_adjustedBack_copy_pre w d hp)

/-- The two half-zone writes, separated by an adjusted walk and scratch rewind, as one
contract. Scratch is preserved and its head is restored by the middle composite. -/
private def zr_writeHalvesContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_innerCopyContract x).seq (zr_outerHalfContract x) (fun w => w)
    (fun w d _ hp => by
      simpa only [zr_outerHalfContract, Contract.seq_pre, zr_adjustedBackContract,
        Contract.ofSegment_pre, zr_adjustedWalkContract, zr_rulerStepContract, zr_stepContract,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using
        zr_innerCopy_adjusted_pre w d hp)

/-- The constant scratch word has the last field's length, half the new zone's capacity. -/
private def zr_rulerWord {k : ℕ} (D : ZoneData k) : List (ZoneSym k) :=
  List.replicate (2 ^ D.1) (Sum.inl false)

/-- The ruler prefix establishes the entire nonempty-word premise of the half-zone writer.

**Proof sketch.** Its scratch footprint is exactly the ruler interval. Outside that interval
scratch is still blank, including both delimiters; inside it every cell is the ruler marker. -/
private lemma zr_rightRuler_write_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) ((SeekPhase ⊕ SeekPhase) ⊕ (SweepPhase ⊕ SeekPhase)) x)
    (hp : (zr_rightRulerContract x).pre D d) :
    (zr_writeHalvesContract x).pre (zr_rulerWord D)
      (((zr_rightRulerContract x).post D d).mapState fun _ => Sum.inl SweepPhase.sweep) := by
  have hz : zoneRowPre D d := (zr_rightRuler_pre D d) ▸ hp
  rw [zr_writeHalvesContract, Contract.seq_pre, zr_innerCopyContract,
    Contract.ofSegment_pre, zr_halfCopyContract, copyMapTM_contract_pre]
  constructor
  · intro hempty
    have hlen := congrArg List.length hempty
    have hpos := Nat.two_pow_pos D.1
    simp only [zr_rulerWord, List.length_replicate, List.length_nil] at hlen
    omega
  · intro p _ _
    simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      zr_rightRuler_post D d hp, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
      zr_rulerWord, hz.2.2, true_and, FinTM.bufferTape_eq,
      List.getElem?_replicate]
    split_ifs <;> first | rfl | omega

/-- The complete right pass: build the ruler and write the new zone's inner and outer halves,
using the adjusted walk and restoring the scratch head. -/
private def zr_rightPassContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_rightRulerContract x).seq (zr_writeHalvesContract x) zr_rulerWord
    (fun D d _ hp => zr_rightRuler_write_pre D d hp)

/-- The complete right pass has exactly the original zoned-input precondition. -/
private lemma zr_rightPass_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_rightPassContract x).pre D d = zoneRowPre D d := by
  rw [zr_rightPassContract, Contract.seq_pre, zr_rightRuler_pre]
  simp only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- The right pass's exact time includes all eight stationary seam transitions.
It is the seek distance plus ten half-capacities and twenty-three control steps. -/
private lemma zr_rightPass_time {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_rightPassContract x).time D d = zoneStart D.1 + 10 * 2 ^ D.1 + 23 := by
  have hpos := Nat.two_pow_pos D.1
  simp only [zr_rightPassContract, Contract.seq_time, zr_rightRulerContract,
    Contract.ofSegment_time, zr_rightSeekBackContract, zr_rightSeekContract,
    seekEndTM_contract_time, skipBackTM_contract_time, zr_rulerSkipContract,
    zr_rulerCopyContract, copyMapTM_contract_time, skipTM_contract_time,
    zr_writeHalvesContract, zr_innerCopyContract, zr_halfCopyContract,
    zr_outerHalfContract, zr_adjustedBackContract, zr_adjustedWalkContract,
    zr_rulerStepContract, zr_stepContract, zr_cellContract, walkTM_contract_time, zr_rightFields,
    zr_rightWord_length, zr_rulerWord, List.length_cons, List.length_ofFn, List.length_replicate,
    List.length_tail, zr_right_offset D.2 D.1 le_rfl]
  omega

/-- The right pass takes at most thirty-two times the new half-capacity plus one. -/
private lemma zr_rightPass_time_le {k : ℕ} {x : List (ZoneSym k)}
    (D : ZoneData k) (d) :
    (zr_rightPassContract x).time D d ≤ 32 * (2 ^ D.1 + 1) := by
  have h := zr_extent_cost D.1
  have hm := zoneStart_mono (Nat.le_add_right D.1 1)
  rw [zr_rightPass_time]
  omega

/-- The common endpoint equation for either constant half-zone write.

**Proof sketch.** Use the mapped copy's constant-cell equation and its public field equations. -/
private lemma zr_halfCopy_post {k : ℕ} {x : List (ZoneSym k)} (inner : Bool)
    (w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) SweepPhase x) :
    (zr_halfCopyContract inner x).post w d =
      { d with
        state := some SweepPhase.done
        workTapes := fun j q =>
          if j = 0 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
          then some (.inr fun _ => if inner then some none else none)
          else d.workTapes j q } := by
  apply Cfg.ext
  · simp only [zr_halfCopyContract, copyMapTM_contract_post, sweepPost_state]
  · simp only [zr_halfCopyContract, copyMapTM_contract_post, sweepPost_inputPos]
  · funext j q
    exact zr_constantCopy_cell 1 0 (by decide) _ w d j q
  · funext j
    simp only [zr_halfCopyContract, copyMapTM_contract_post, sweepPost_workTapePos]
  · simp only [zr_halfCopyContract, copyMapTM_contract_post, sweepPost_output]

/-- Writing both halves fills one contiguous zone and leaves the head at its midpoint.

**Proof sketch.** Insert the adjusted walk's restored-scratch endpoint between the two
constant copies. Their destination intervals are adjacent and disjoint. -/
private lemma zr_writeHalves_post {k : ℕ} {x : List (ZoneSym k)} (w : List (ZoneSym k))
    (d) (hp : (zr_writeHalvesContract x).pre w d) :
    (zr_writeHalvesContract x).post w d =
      { d with
        state := some (Sum.inr (Sum.inr SweepPhase.done))
        workTapes := fun j q =>
          if j = 0 ∧ d.workTapePos 0 ≤ q ∧ q < d.workTapePos 0 + 2 * (w.length : ℤ)
          then some (.inr fun _ => if q < d.workTapePos 0 + w.length then some none else none)
          else d.workTapes j q
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + w.length) } := by
  have hi : (zr_innerCopyContract x).pre w (d.mapState fun _ => SweepPhase.sweep) := by
    simpa only [zr_writeHalvesContract, Contract.seq_pre] using hp
  have ha := zr_innerCopy_adjusted_pre w _ hi
  rw [zr_writeHalvesContract, Contract.seq_post, zr_outerHalfContract, Contract.seq_post,
    zr_adjustedBack_post w _ (by
      simpa only [zr_adjustedBackContract, Contract.ofSegment_pre, Contract.seq_pre,
        zr_adjustedWalkContract, zr_rulerStepContract, zr_stepContract,
        Cfg.mapState_workTapes,
        Cfg.mapState_workTapePos] using ha)]
  simp only [zr_halfCopy_post, zr_innerCopyContract, Contract.ofSegment_post]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    by_cases hj : j = 0
    · subst j
      simp only [Bool.false_eq_true, if_false, if_true, true_and]
      split_ifs <;> first | rfl | omega
    · simp only [hj, false_and, if_false]
  · funext j
    simp only [Cfg.mapState_workTapePos]
    by_cases hj : j = 0
    · subst j
      simp only [if_true, Function.update_self]
    · simp only [if_neg hj, Function.update_of_ne hj, Nat.cast_zero, add_zero]
  · simp only [Cfg.mapState_output]

/-- The right pass writes both halves of the new zone and a delimited scratch ruler.
The zoned head ends at the midpoint of the new zone, and the scratch head is restored.

**Proof sketch.** Substitute the ruler prefix and half-writer endpoints into the seam endpoint.
The ruler has the new half-capacity, so the two adjacent writes have the required split. -/
private lemma zr_rightPass_post {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightPassContract x).pre D d) :
    (zr_rightPassContract x).post D d =
      { d with
        state := some (Sum.inr (Sum.inr (Sum.inr SweepPhase.done)))
        workTapes := fun j q =>
          if j = 0 ∧ (zoneStart D.1 : ℤ) ≤ q ∧ q < zoneStart D.1 + zoneCapacity D.1 then
            some (.inr fun _ => if q < zoneStart D.1 + 2 ^ D.1 then some none else none)
          else if j = 1 ∧ d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + 2 ^ D.1 then
            some (.inl false)
          else d.workTapes j q
        workTapePos := Function.update d.workTapePos 0 (zoneStart D.1 + 2 ^ D.1) } := by
  have hr : (zr_rightRulerContract x).pre D
      (d.mapState fun _ => Sum.inl (Sum.inl SeekPhase.run)) := by
    simpa only [zr_rightPassContract, Contract.seq_pre] using hp
  have hw := zr_rightRuler_write_pre D _ hr
  rw [zr_rightPassContract, Contract.seq_post, zr_writeHalves_post _ _ hw,
    zr_rightRuler_post D _ hr]
  have hcap : (zoneCapacity D.1 : ℤ) = 2 * 2 ^ D.1 := by
    rw [zoneCapacity_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Function.update_self,
      zr_rulerWord, List.length_replicate, hcap, Nat.cast_pow, Nat.cast_ofNat]
    by_cases hj : j = 1
    · subst j
      rfl
    · simp only [hj, false_and, if_false]
  · funext j
    simp only [Cfg.mapState_workTapePos, zr_rulerWord, List.length_replicate,
      Function.update_self, Nat.cast_pow, Nat.cast_ofNat]
    by_cases hj : j = 0
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos]
  · simp only [Cfg.mapState_output]

/-- The right pass keeps the zoned head between the home's left separator and the end of the new
zone; scratch stays between the ruler's left delimiter and the cell just past its right one.

**Proof sketch.** The seam envelope is the hull of its phases. Substitute the catalog bounds
and head endpoints; the last field's left delimiter is at least cell `-1`. -/
private lemma zr_rightPass_bounds {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightPassContract x).pre D d) :
    -1 ≤ (zr_rightPassContract x).lo D d 0 ∧
      (zr_rightPassContract x).hi D d 0 ≤ (zoneStart D.1 : ℤ) + zoneCapacity D.1 ∧
      d.workTapePos 1 - 1 ≤ (zr_rightPassContract x).lo D d 1 ∧
      (zr_rightPassContract x).hi D d 1 ≤ d.workTapePos 1 + ((2 ^ D.1 : ℕ) : ℤ) + 1 := by
  have hz : zoneRowPre D d := (zr_rightPass_pre D d) ▸ hp
  have hc := Nat.two_pow_pos D.1
  have hs0 : 2 ^ D.1 + 1 ≤ zoneStart D.1 := by
    rw [zoneStart_eq, pow_succ]
    omega
  have hd : zoneCapacity D.1 = 2 * 2 ^ D.1 := zoneCapacity_eq D.1
  simp only [zr_rightPassContract, Contract.seq_lo, Contract.seq_hi,
    zr_rightRulerContract, Contract.ofSegment_lo, Contract.ofSegment_hi,
    zr_rightSeekBackContract, zr_rightSeekContract, seekEndTM_contract_lo,
    seekEndTM_contract_hi, skipBackTM_contract_lo, skipBackTM_contract_hi,
    zr_rulerSkipContract, zr_rulerCopyContract, copyMapTM_contract_lo,
    copyMapTM_contract_hi, skipTM_contract_lo, skipTM_contract_hi,
    zr_writeHalvesContract, zr_innerCopyContract, zr_halfCopyContract,
    zr_outerHalfContract, zr_adjustedBackContract, zr_adjustedWalkContract,
    zr_rulerStepContract, zr_stepContract, zr_cellContract, walkTM_contract_lo, walkTM_contract_hi,
    Contract.seq_post, Contract.ofSegment_post, seekEndTM_contract_post,
    skipBackTM_contract_post, copyMapTM_contract_post, skipTM_contract_post,
    walkTM_contract_post, zr_cellPost, Cfg.mapState_workTapePos, seekPost_workTapePos,
    sweepPost_workTapePos, zr_rightFields, zr_rightWord_length, zr_rulerWord,
    List.length_cons, List.length_ofFn, List.length_replicate, List.length_tail,
    zr_right_offset D.2 D.1 le_rfl, Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    if_true, if_false, or_true, true_or, hz.2.1, SignType.coe_one, one_mul]
  omega

/-- The right pass's zoned-head envelope lies inside the next level's symmetric box.

**Proof sketch.** The new zone ends before the next zone start. -/
private lemma zr_rightPass_envelope {k : ℕ} {x : List (ZoneSym k)}
    (D : ZoneData k) (d) (hp : (zr_rightPassContract x).pre D d) :
    -(zoneStart (D.1 + 1) : ℤ) ≤ (zr_rightPassContract x).lo D d 0 ∧
      (zr_rightPassContract x).hi D d 0 ≤ zoneStart (D.1 + 1) := by
  have h := zr_rightPass_bounds D d hp
  have hs := zoneStart_succ D.1
  have h2 := two_le_zoneStart (D.1 + 1)
  constructor <;> omega

/-- On the nonnegative half-line the right pass already realizes the extended zoned tape;
on the nonpositive half-line it preserves the original zoned tape.

**Proof sketch.** Compare the endpoint's interval formula with `zonedTape_extend`, using
nonnegativity to remove the absolute value. The written interval starts strictly after home. -/
private lemma zr_rightPass_tape {k : ℕ} {x : List (ZoneSym k)}
    (D : ZoneData k) (d) (hp : (zr_rightPassContract x).pre D d) :
    (∀ q : ℤ, 0 ≤ q → ((zr_rightPassContract x).post D d).workTapes 0 q =
      zonedTape (fun t => (D.2 t).extend) q) ∧
    (∀ q : ℤ, q ≤ 0 → ((zr_rightPassContract x).post D d).workTapes 0 q =
      zonedTape D.2 q) := by
  have hz : zoneRowPre D d := (zr_rightPass_pre D d) ▸ hp
  have hs := two_le_zoneStart D.1
  rw [zr_rightPass_post D d hp]
  simp only [show (0 : Fin 2) ≠ 1 by decide, false_and, if_false, true_and, hz.1]
  constructor
  · intro q hq
    rw [zonedTape_extend, abs_of_nonneg hq]
    by_cases h : (zoneStart D.1 : ℤ) ≤ q ∧ q < zoneStart D.1 + zoneCapacity D.1
    · rw [if_pos h, if_pos h]
      have he : q < (zoneStart D.1 : ℤ) + 2 ^ D.1 ↔ q.toNat - zoneStart D.1 < 2 ^ D.1 := by
        have hcast : ((2 ^ D.1 : ℕ) : ℤ) = 2 ^ D.1 := by
          simp only [Nat.cast_pow, Nat.cast_ofNat]
        omega
      simp only [he]
    · rw [if_neg h, if_neg h]
  · intro q hq
    rw [if_neg (by omega)]

/-- The characterized right pass with its nested image exit normalized to one live exit.
The normalization changes no endpoint, time or envelope. -/
private abbrev zr_rightPassRow {k : ℕ} (x : List (ZoneSym k)) :=
  zr_singletonContract (zr_rightPassContract x)
    (Sum.inr (Sum.inr (Sum.inr SweepPhase.done)))

/-- The home test: step right, read the cell there, and step back. Its verdict is `true` exactly
when that cell is blank. At the first cell of a layout field this identifies the home, the only
one-cell field, since every zone has capacity at least two. -/
private def zr_testContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_stepContract (ι := Unit) 0 1 x fun _ _ => True).seq
    (zr_cellContract 0 (fun a => a.isNone) none (-1) x) (fun _ => ()) fun _ _ _ _ => trivial

/-- The home test reads the cell right of the head, records its blankness and leaves every
other field unchanged.

**Proof sketch.** Compose the two leaf endpoints through the seam's endpoint equation; the two
head moves cancel. -/
private lemma zr_test_post {k : ℕ} {x : List (ZoneSym k)}
    (d : Cfg 2 (ZoneSym k) (Option Bool ⊕ Option Bool) x) :
    (zr_testContract x).post () d =
      { d with
        state := some (Sum.inr (some (d.workTapes 0 (d.workTapePos 0 + 1)).isNone)) } := by
  simp only [zr_testContract, Contract.seq_post, zr_stepContract, Contract.ofSegment_post,
    zr_cellContract, zr_cellPost]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some, Cfg.workTapeSymbols_eq,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Function.update_self, SignType.coe_one]
  · simp only [Cfg.mapState_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes]
  · funext j
    by_cases hj : j = 0
    · subst hj
      simp only [Function.update_self, Cfg.mapState_workTapePos, SignType.coe_one,
        SignType.coe_neg_one, add_neg_cancel_right]
    · simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos]
  · simp only [Cfg.mapState_output]

/-- The home test takes three steps: two leaves and their seam. -/
private lemma zr_test_time {k : ℕ} {x : List (ZoneSym k)}
    (d : Cfg 2 (ZoneSym k) (Option Bool ⊕ Option Bool) x) :
    (zr_testContract x).time () d = 3 := by
  simp only [zr_testContract, Contract.seq_time, zr_stepContract, Contract.ofSegment_time,
    zr_cellContract]

/-- One round's body: skip back over the field before the head, then test for the home. -/
private def zr_bodyContract {k : ℕ} (x : List (ZoneSym k)) :=
  (skipBackTM_contract 0 x).seq (zr_testContract x) (fun _ => ()) fun _ _ _ _ => by
    rw [zr_testContract, Contract.seq_pre, zr_stepContract, Contract.ofSegment_pre]
    trivial

/-- The body ends at the crossed field's first cell, with the home test's verdict on the cell
after it.

**Proof sketch.** Substitute the backward skip's endpoint into the test's endpoint. -/
private lemma zr_body_post {k : ℕ} {x : List (ZoneSym k)} (u : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ (Option Bool ⊕ Option Bool)) x) :
    (zr_bodyContract x).post u d =
      { d with
        state := some (Sum.inr (Sum.inr (some
          (d.workTapes 0 (d.workTapePos 0 - u.length)).isNone)))
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 - u.length - 1) } := by
  rw [zr_bodyContract, Contract.seq_post, zr_test_post, skipBackTM_contract_post]
  have he : d.workTapePos 0 - u.length - 1 + 1 = d.workTapePos 0 - u.length := by omega
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some, Cfg.mapState_workTapes,
      Cfg.mapState_workTapePos, seekPost_workTapes, seekPost_workTapePos, Function.update_self,
      he]
  · simp only [Cfg.mapState_inputPos, seekPost_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes, seekPost_workTapes]
  · funext j
    simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_apply]
  · simp only [Cfg.mapState_output, seekPost_output]

/-- The body takes the crossed field's length plus seven steps. -/
private lemma zr_body_time {k : ℕ} {x : List (ZoneSym k)} (u : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ (Option Bool ⊕ Option Bool)) x) :
    (zr_bodyContract x).time u d = u.length + 7 := by
  rw [zr_bodyContract, Contract.seq_time, zr_test_time, skipBackTM_contract_time]

/-- The body's zoned head stays between the crossed field's left delimiter and its start; the
scratch head does not move. -/
private lemma zr_body_bounds {k : ℕ} {x : List (ZoneSym k)} (u : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ (Option Bool ⊕ Option Bool)) x) :
    (zr_bodyContract x).lo u d 0 = d.workTapePos 0 - u.length - 2 ∧
      (zr_bodyContract x).hi u d 0 = d.workTapePos 0 ∧
      (zr_bodyContract x).lo u d 1 = d.workTapePos 1 ∧
      (zr_bodyContract x).hi u d 1 = d.workTapePos 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [zr_bodyContract, Contract.seq_lo, Contract.seq_hi, skipBackTM_contract_lo,
    skipBackTM_contract_hi, skipBackTM_contract_post, zr_testContract, zr_stepContract,
    Contract.ofSegment_lo, Contract.ofSegment_hi, Contract.ofSegment_post, zr_cellContract,
    zr_cellPost, Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), show (1 : Fin 2) ≠ 0 by decide,
    if_true, if_false, SignType.coe_one, SignType.coe_neg_one, min_self, max_self] <;>
  omega

/-- A two-phase loop host's phases: phase `false` is the one-cell leaf's, whose verdict
`some false` is the anchor and whose other states are the escapes; phase `true` is a body with
states `B`. -/
private abbrev zr_hostPh (B : Type) : Bool → Type
  | false => Option Bool
  | true => B

/-- The loop host's phase machines: the stationary leaf, and the body's machine `MB`. -/
private def zr_hostMachines {k : ℕ} {B : Type} (MB : MultiTapeTM 2 (ZoneSym k) B) :
    (b : Bool) → MultiTapeTM 2 (ZoneSym k) (zr_hostPh B b)
  | false => zr_cellTM 0 (fun _ => false) none 0
  | true => MB

/-- The loop host's redirects: the anchor starts the body at `e`, and a body state `s` with
`back s = some v` is sent to the anchor-phase state `v`. -/
private def zr_hostRed {B : Type} (e : B) (back : B → Option (Option Bool)) :
    (b : Bool) → zr_hostPh B b → Option (Σ b, zr_hostPh B b)
  | false, some false => some ⟨true, e⟩
  | false, _ => none
  | true, s => (back s).map fun v => ⟨false, v⟩

/-- **A loop host**, an instance of the public phase host started at its anchor. -/
private abbrev zr_hostTM {k : ℕ} {B : Type} (MB : MultiTapeTM 2 (ZoneSym k) B) (e : B)
    (back : B → Option (Option Bool)) : MultiTapeTM 2 (ZoneSym k) (Σ b, zr_hostPh B b) :=
  phaseHostTM (zr_hostMachines MB) ⟨false, some false⟩ (zr_hostRed e back)

/-- The return loop's phases: the anchor phase, and the body's states. -/
private abbrev zr_loopPh : Bool → Type := zr_hostPh (SeekPhase ⊕ (Option Bool ⊕ Option Bool))

/-- The return loop's body machine: skip back over a field, step, and test for the home. -/
private abbrev zr_loopBodyTM (k : ℕ) :
    MultiTapeTM 2 (ZoneSym k) (SeekPhase ⊕ (Option Bool ⊕ Option Bool)) :=
  seamCompTM (skipBackTM 2 0) SeekPhase.done
    (seamCompTM (zr_cellTM 0 (fun _ => false) none 1) (some false)
      (zr_cellTM 0 (fun a => a.isNone) none (-1)) none) (Sum.inl none)

/-- The return loop's way back: the body's verdict selects the anchor (not yet home) or the home
exit. -/
private def zr_loopBack : SeekPhase ⊕ (Option Bool ⊕ Option Bool) → Option (Option Bool)
  | .inr (.inr (some v)) => some (some v)
  | _ => none

/-- **The return loop**: from its anchor it repeats the body until the home test succeeds. -/
private abbrev zr_loopTM (k : ℕ) : MultiTapeTM 2 (ZoneSym k) (Σ b, zr_loopPh b) :=
  zr_hostTM (zr_loopBodyTM k) (Sum.inl .run) zr_loopBack

/-- The anchor phase's stationary leaf as a zero-time contract at the anchor. -/
private def zr_anchorContract {k : ℕ} (x : List (ZoneSym k)) :
    Contract (zr_cellTM (k := k) 0 (fun _ => false) none 0) (some false) {some (some false)}
      Unit x :=
  Contract.ofSegment (fun _ _ => True) (fun _ _ => 0) (fun _ d => d)
    (fun _ d => d.workTapePos) (fun _ d => d.workTapePos)
    (fun _ d _ _ => Segment.zero
      ((headBox_iff _ _ _).mpr fun _ => Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩))
    (fun _ d hd _ => by rw [hd]; exact Set.mem_singleton _)

/-- The anchor's dispatch inside a loop host: one stationary step to the body's entry. -/
private def zr_hostDispatchContract {k : ℕ} {B : Type} (MB : MultiTapeTM 2 (ZoneSym k) B)
    (e : B) (back : B → Option (Option Bool)) (x : List (ZoneSym k)) :=
  Contract.inPhase (zr_hostMachines MB) ⟨false, some false⟩ (zr_hostRed e back) false
    (zr_anchorContract x)
    (fun h => by cases Set.mem_singleton_iff.mp h)
    (fun s hs => by
      match s, hs with
      | none, _ => rfl
      | some false, hs => exact absurd (Set.mem_singleton _) hs
      | some true, _ => rfl)
    (fun s hs => by
      obtain rfl := Option.some_injective _ (Set.mem_singleton_iff.mp hs)
      exact ⟨⟨true, e⟩, rfl, Bool.false_ne_true.symm⟩)

/-- A body inside a loop host: its exits are exactly the states that `back` sends to the
anchor phase. -/
private def zr_hostBodyContract {k : ℕ} {B I : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X I x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) :=
  Contract.inPhase (zr_hostMachines MB) ⟨false, some false⟩ (zr_hostRed e back) true C hnone
    (fun s hs => by
      show (back s).map _ = none
      rw [not_not.mp (mt (hX s).mpr hs), Option.map_none])
    (fun s hs => by
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((hX s).mp hs)
      refine ⟨⟨false, v⟩, ?_, Bool.false_ne_true⟩
      show (back s).map _ = _
      rw [hv, Option.map_some])

/-- **The dispatch step**: from the anchor, one step of a loop host reaches the body's entry
and changes nothing else.

**Proof sketch.** Run the dispatch contract for its one step and read its endpoint. -/
private lemma zr_host_dispatch_run {k : ℕ} {B : Type} {x : List (ZoneSym k)}
    (MB : MultiTapeTM 2 (ZoneSym k) B) (e : B) (back : B → Option (Option Bool))
    (c : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh B b) x) (hc : c.state = some ⟨false, some false⟩) :
    (zr_hostTM MB e back).runFrom c 1 = { c with state := some ⟨true, e⟩ } := by
  have hD0 : (zr_hostDispatchContract MB e back x).pre () c := by
    rw [zr_hostDispatchContract, Contract.inPhase_pre, zr_anchorContract,
      Contract.ofSegment_pre]
    trivial
  have hDt : (zr_hostDispatchContract MB e back x).time () c = 1 := by
    rw [zr_hostDispatchContract, Contract.inPhase_time, zr_anchorContract,
      Contract.ofSegment_time]
  rw [← hDt, (zr_hostDispatchContract MB e back x).run () c hc hD0, zr_hostDispatchContract,
    Contract.inPhase_post, zr_anchorContract, Contract.ofSegment_post]
  refine zr_bindState_eq _ _ _ ?_ (Cfg.mapState_inputPos _ _)
    (funext fun j => funext fun q => Cfg.mapState_workTapes _ _ j q)
    (funext fun j => Cfg.mapState_workTapePos _ _ j) (Cfg.mapState_output _ _)
  rw [Cfg.mapState_state, hc]
  rfl

/-- The body's exits are exactly its verdict states. -/
private lemma zr_body_exit_iff
    (s : SeekPhase ⊕ (Option Bool ⊕ Option Bool)) :
    some s ∈ (Option.map Sum.inr '' (Option.map Sum.inr '' Set.range fun b : Bool =>
        some (some b)) : Set (Option (SeekPhase ⊕ (Option Bool ⊕ Option Bool)))) ↔
      ∃ v : Bool, s = Sum.inr (Sum.inr (some v)) := by
  constructor
  · rintro ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, h⟩
    exact ⟨v, (Option.some_injective _ h).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩

/-- The body inside the loop host: its two verdicts are redirected to the anchor and to the home
exit. -/
private def zr_bodyPhaseContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_hostBodyContract zr_loopBack (zr_bodyContract x)
    (fun h => by
      obtain ⟨_, ⟨_, ⟨_, rfl⟩, h₁⟩, h₂⟩ := h
      cases h₁
      cases h₂)
    (fun s => by
      rw [zr_body_exit_iff]
      constructor
      · rintro ⟨v, rfl⟩
        exact Option.some_ne_none _
      · intro h
        match s, h with
        | .inl _, h => exact absurd rfl h
        | .inr (.inl _), h => exact absurd rfl h
        | .inr (.inr none), h => exact absurd rfl h
        | .inr (.inr (some v)), _ => exact ⟨v, rfl⟩)

/-- **A dispatch step and a body make a round**: on any machine, one step from the anchor `a` to
a configuration at the body's entry, then the body's contract, whose exits contain the anchor and
every escape, form one round ending at the body's endpoint, provided the head relation holds at
the start and inside the body's envelope.

**Proof sketch.** The run splits after the dispatch step. Strictly inside the body, its cut and
liveness keep the run off its exits and off halting, hence off the round's stop set. -/
private lemma zr_round_of_body {n : ℕ} {Γ S I : Type} {x : List Γ} {M : MultiTapeTM n Γ S}
    {a entry : S} {E X : Set (Option S)} {P : (Fin n → ℤ) → Prop} (C : Contract M entry X I x)
    (i : I) (c c₁ : Cfg n Γ S x) (hc : c.state = some a) (h1 : M.runFrom c 1 = c₁)
    (hc₁ : c₁.state = some entry) (hp : C.pre i c₁) (haX : some a ∈ X) (hEX : E ⊆ X)
    (hend : (C.post i c₁).state ∈ insert (some a) E) (hP0 : P c.workTapePos)
    (hPC : ∀ p, HeadBox (C.lo i c₁) (C.hi i c₁) p → P p) :
    Round M a E P c (C.post i c₁) (1 + C.time i c₁) := by
  rw [round_iff]
  refine ⟨hc, by omega, ?_, hend, ?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add, h1, C.run i c₁ hc₁ hp]
  · intro u hu0 hu
    obtain ⟨v, rfl⟩ : ∃ v, u = 1 + v := ⟨u - 1, by omega⟩
    rw [MultiTapeTM.runFrom_add, h1]
    have hv : v < C.time i c₁ := by omega
    have hcut := C.cut i c₁ hc₁ hp v hv
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (C.live i c₁ hc₁ hp hv)
    rw [not_mem_roundStop]
    refine ⟨s, hs, ?_, ?_⟩
    · rintro rfl
      exact hcut (hs ▸ haX)
    · intro hm
      exact hcut (hs ▸ hEX hm)
  · intro u hu
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · rw [MultiTapeTM.runFrom_zero]
      exact hP0
    · obtain ⟨v, rfl⟩ : ∃ v, u = 1 + v := ⟨u - 1, by omega⟩
      rw [MultiTapeTM.runFrom_add, h1]
      exact hPC _ fun j => C.env i c₁ hc₁ hp v (by omega) j

/-- **One round of the return loop**: from the anchor, with a delimited field `u` ending one
blank before the zoned head, the loop dispatches, skips back over `u`, tests the cell after
`u`'s first cell, and stops at the anchor or at the home exit after `|u| + 9` steps. Strictly in
between it is live and off both; the zoned head stays between `u`'s left delimiter and its start,
and the scratch head is fixed.

**Proof sketch.** The dispatch and the body are phase contracts of the host
(`Turing.Contract.inPhase`): run the first for its one step and the second from its endpoint.
The body's cut and liveness give the round's cut; the two envelopes give the head relation. -/
private lemma zr_loop_round {k : ℕ} {x : List (ZoneSym k)} (u : List (ZoneSym k))
    (c : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (hc : c.state = some ⟨false, some false⟩)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      c.workTapes 0 (c.workTapePos 0 - u.length - 1 + p) = FinTM.bufferTape u p)
    (P : (Fin 2 → ℤ) → Prop)
    (hP : ∀ p : Fin 2 → ℤ, c.workTapePos 0 - u.length - 2 ≤ p 0 → p 0 ≤ c.workTapePos 0 →
      p 1 = c.workTapePos 1 → P p) :
    Round (zr_loopTM k) ⟨false, some false⟩ {some ⟨false, some true⟩} P c
      { c with
        state := some ⟨false, some (c.workTapes 0 (c.workTapePos 0 - u.length)).isNone⟩
        workTapePos := Function.update c.workTapePos 0 (c.workTapePos 0 - u.length - 1) }
      (u.length + 9) := by
  have hrun1 : (zr_loopTM k).runFrom c 1 = { c with state := some ⟨true, .inl .run⟩ } :=
    zr_host_dispatch_run _ _ _ c hc
  set c₁ : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x := { c with state := some ⟨true, .inl .run⟩ }
    with hc₁
  have hc₁s : c₁.state = some ⟨true, .inl .run⟩ := rfl
  have hB0 : (zr_bodyPhaseContract x).pre u c₁ := by
    rw [zr_bodyPhaseContract, zr_hostBodyContract, Contract.inPhase_pre, zr_bodyContract, Contract.seq_pre,
      skipBackTM_contract_pre]
    intro p h1 h2
    simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using hu p h1 h2
  have hBt : (zr_bodyPhaseContract x).time u c₁ = u.length + 8 := by
    rw [zr_bodyPhaseContract, zr_hostBodyContract, Contract.inPhase_time, zr_body_time]
  have hBpost : (zr_bodyPhaseContract x).post u c₁ =
      { c with
        state := some ⟨false, some (c.workTapes 0 (c.workTapePos 0 - u.length)).isNone⟩
        workTapePos := Function.update c.workTapePos 0 (c.workTapePos 0 - u.length - 1) } := by
    rw [zr_bodyPhaseContract, zr_hostBodyContract, Contract.inPhase_post, zr_body_post]
    let f : (Σ b, zr_loopPh b) → zr_loopPh true := fun _ => Sum.inl SeekPhase.run
    refine zr_bindState_eq _ _ _ ?_ (Cfg.mapState_inputPos f c₁)
      (funext fun j => funext fun q => Cfg.mapState_workTapes f c₁ j q) ?_
      (Cfg.mapState_output f c₁)
    · simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      rfl
    · funext j
      simp only [Function.update_apply, Cfg.mapState_workTapePos]
      rfl
  have hmem : ∀ v : Bool, some (⟨false, some v⟩ : Σ b, zr_loopPh b) ∈
      {q | ∃ s, some s ∈ (Option.map Sum.inr '' (Option.map Sum.inr '' Set.range fun b : Bool =>
        some (some b)) : Set (Option (SeekPhase ⊕ (Option Bool ⊕ Option Bool)))) ∧
          q = zr_hostRed (Sum.inl .run) zr_loopBack true s} :=
    fun v => ⟨Sum.inr (Sum.inr (some v)), (zr_body_exit_iff _).mpr ⟨v, rfl⟩, rfl⟩
  have hend : ((zr_bodyPhaseContract x).post u c₁).state ∈
      (insert (some ⟨false, some false⟩) {some ⟨false, some true⟩} :
        Set (Option (Σ b, zr_loopPh b))) := by
    rw [hBpost]
    cases (c.workTapes 0 (c.workTapePos 0 - u.length)).isNone
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  have hPC : ∀ p, HeadBox ((zr_bodyPhaseContract x).lo u c₁) ((zr_bodyPhaseContract x).hi u c₁)
      p → P p := by
    intro p hb
    have hlo : ∀ j, (zr_bodyPhaseContract x).lo u c₁ j =
        (zr_bodyContract x).lo u (c₁.mapState fun _ => Sum.inl SeekPhase.run) j := fun j => by
      rw [zr_bodyPhaseContract, zr_hostBodyContract, Contract.inPhase_lo]
    have hhi : ∀ j, (zr_bodyPhaseContract x).hi u c₁ j =
        (zr_bodyContract x).hi u (c₁.mapState fun _ => Sum.inl SeekPhase.run) j := fun j => by
      rw [zr_bodyPhaseContract, zr_hostBodyContract, Contract.inPhase_hi]
    obtain ⟨b₁, b₂, b₃, b₄⟩ := zr_body_bounds u (c₁.mapState fun _ => Sum.inl SeekPhase.run)
    have h0 := hb 0
    have h1 := hb 1
    rw [hlo, hhi, Finset.mem_Icc] at h0 h1
    rw [b₁, b₂, Cfg.mapState_workTapePos] at h0
    rw [b₃, b₄, Cfg.mapState_workTapePos] at h1
    exact hP _ h0.1 h0.2 (le_antisymm h1.2 h1.1)
  have hR := zr_round_of_body (zr_bodyPhaseContract x) u c c₁ hc hrun1 hc₁s hB0 (hmem false)
    (fun q hq => by rw [Set.mem_singleton_iff.mp hq]; exact hmem true) hend
    (hP _ (by omega) le_rfl rfl) hPC
  rwa [hBt, hBpost, show 1 + (u.length + 8) = u.length + 9 by omega] at hR

/-- The return loop's precondition at the data `Z`: the zoned head one past the separator after
the last right zone, and tape `0` agreeing with the zoned tape of `Z` from cell `-1` up to the
head. -/
private def zr_loopPre {k : ℕ} {x : List (ZoneSym k)} (Z : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) : Prop :=
  d.workTapePos 0 = zoneStart Z.1 ∧
    ∀ q : ℤ, -1 ≤ q → q < zoneStart Z.1 → d.workTapes 0 q = zonedTape Z.2 q

open Classical in
/-- The length of the layout field that ends one blank before the cell `p`: zone `i` when `p`
starts zone `i + 1`, and otherwise `1`, the home's. It times the return loop's rounds. -/
private noncomputable def zr_fieldLen (p : ℤ) : ℕ :=
  if h : ∃ i, (zoneStart (i + 1) : ℤ) = p then zoneCapacity (Nat.find h) else 1

/-- The field before zone `i + 1` is zone `i`. -/
private lemma zr_fieldLen_succ (i : ℕ) : zr_fieldLen (zoneStart (i + 1)) = zoneCapacity i := by
  have h : ∃ j, (zoneStart (j + 1) : ℤ) = zoneStart (i + 1) := ⟨i, rfl⟩
  rw [zr_fieldLen, dif_pos h]
  congr 1
  rw [Nat.find_eq_iff]
  refine ⟨rfl, fun n hn he => ?_⟩
  have := zoneStart_add_lt (show n + 1 < i + 1 by omega)
  omega

/-- The field before zone `0` is the home. -/
private lemma zr_fieldLen_zero : zr_fieldLen (zoneStart 0) = 1 := by
  rw [zr_fieldLen, dif_neg]
  rintro ⟨i, hi⟩
  have := zoneStart_add_lt (show 0 < i + 1 by omega)
  omega

/-- The loop's rounds add up to the extent and eight steps per field.

**Proof sketch.** Induct on the level count, splitting off the first round, across the last
zone; the zone-start recurrence absorbs its capacity. -/
private lemma zr_loop_time_sum (L : ℕ) :
    ∑ r ∈ Finset.range (L + 1), (zr_fieldLen (zoneStart (L - r)) + 9) =
      zoneStart L + 8 * (L + 1) := by
  induction L with
  | zero =>
    rw [Finset.sum_range_one, Nat.sub_zero, zr_fieldLen_zero, zoneStart_eq]
    norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ', Nat.sub_zero, zr_fieldLen_succ, zoneStart_succ]
    have he : ∀ r ∈ Finset.range (L + 1),
        zr_fieldLen (zoneStart (L + 1 - (r + 1))) + 9 = zr_fieldLen (zoneStart (L - r)) + 9 := by
      intro r _
      rw [Nat.add_sub_add_right]
    rw [Finset.sum_congr rfl he, ih]
    omega

/-- The loop's configuration with the zoned head moved to `p`. -/
private def zr_loopAt {k : ℕ} {x : List (ZoneSym k)} (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x)
    (p : ℤ) : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x :=
  { d with workTapePos := Function.update d.workTapePos 0 p }

/-- Zone `i` is the delimited field before the start of zone `i + 1`. -/
private lemma zr_loop_zone_word {k : ℕ} {x : List (ZoneSym k)} (Z : ZoneData k) (i : Fin Z.1)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (hp : zr_loopPre Z d) :
    ∀ p : ℤ, -1 ≤ p → p ≤ ((zoneCells true Z.2 i).length : ℤ) →
      (zr_loopAt d (zoneStart (i + 1))).workTapes 0
          ((zr_loopAt d (zoneStart (i + 1))).workTapePos 0 - (zoneCells true Z.2 i).length -
            1 + p) = FinTM.bufferTape (zoneCells true Z.2 i) p := by
  intro p h1 h2
  rw [zoneCells_length] at h2 ⊢
  have hs := zoneStart_succ i.val
  have hm := zoneStart_mono (show i.val + 1 ≤ Z.1 by omega)
  simp only [zr_loopAt, Function.update_self]
  rw [show ((zoneStart (i + 1) : ℕ) : ℤ) - zoneCapacity i - 1 + p = (zoneStart i : ℤ) + p by
    omega, hp.2 _ (by omega) (by omega)]
  exact zonedTape_right_word Z.2 i p h1 h2

/-- At a zone's first cell the home test fails: the zone's second cell is a zone cell. -/
private lemma zr_loop_zone_test {k : ℕ} {x : List (ZoneSym k)} (Z : ZoneData k) (i : Fin Z.1)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (hp : zr_loopPre Z d) :
    ((zr_loopAt d (zoneStart (i + 1))).workTapes 0
        ((zr_loopAt d (zoneStart (i + 1))).workTapePos 0 -
          (zoneCells true Z.2 i).length)).isNone = false := by
  have hs := zoneStart_succ i.val
  have hm := zoneStart_mono (show i.val + 1 ≤ Z.1 by omega)
  have hc : 1 < zoneCapacity i := by
    rw [zoneCapacity_eq]
    have := Nat.two_pow_pos i.val
    omega
  simp only [zr_loopAt, Function.update_self, zoneCells_length]
  rw [show ((zoneStart (i + 1) : ℕ) : ℤ) - zoneCapacity i = ((zoneStart i + 1 : ℕ) : ℤ) by
    omega, hp.2 _ (by omega) (by omega), zonedTape_right Z.2 i 1 hc, Option.isNone_some]

/-- The home is the delimited one-cell field before zone `0`. -/
private lemma zr_loop_home_word {k : ℕ} {x : List (ZoneSym k)} (Z : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (hp : zr_loopPre Z d) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (([Sum.inr fun t => some (Z.2 t).home] : List (ZoneSym k)).length : ℤ) →
      (zr_loopAt d (zoneStart 0)).workTapes 0 ((zr_loopAt d (zoneStart 0)).workTapePos 0 -
          ([Sum.inr fun t => some (Z.2 t).home] : List (ZoneSym k)).length - 1 + p) =
        FinTM.bufferTape [Sum.inr fun t => some (Z.2 t).home] p := by
  intro p h1 h2
  have h0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  have hL := two_le_zoneStart Z.1
  simp only [zr_loopAt, Function.update_self, List.length_singleton, h0] at h2 ⊢
  rw [show ((2 : ℕ) : ℤ) - (1 : ℕ) - 1 + p = p by omega, hp.2 p (by omega) (by omega)]
  exact zr_home_word Z.2 p h1 h2

/-- At the home the test succeeds: the cell after it is the right separator. -/
private lemma zr_loop_home_test {k : ℕ} {x : List (ZoneSym k)} (Z : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (hp : zr_loopPre Z d) :
    ((zr_loopAt d (zoneStart 0)).workTapes 0 ((zr_loopAt d (zoneStart 0)).workTapePos 0 -
        ([Sum.inr fun t => some (Z.2 t).home] : List (ZoneSym k)).length)).isNone = true := by
  have h0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  have hL := two_le_zoneStart Z.1
  have hsep := zonedTape_right_sep Z.2 0
  rw [h0] at hsep
  simp only [zr_loopAt, Function.update_self, List.length_singleton, h0]
  rw [show ((2 : ℕ) : ℤ) - (1 : ℕ) = (2 : ℕ) - 1 by omega, hp.2 _ (by omega) (by omega), hsep,
    Option.isNone_none]

/-- The return loop's orbit: before its last round, round `r` starts at the anchor with the
zoned head at the start of zone `Z.1 - r`.

**Proof sketch.** Induct on `r`: each round's run (`zr_loop_round`) crosses zone `Z.1 - r - 1`,
whose test fails, so it ends at the anchor at that zone's start. -/
private lemma zr_loop_orbit {k : ℕ} {x : List (ZoneSym k)} (Z : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (hd : d.state = some ⟨false, some false⟩)
    (hp : zr_loopPre Z d) :
    ∀ r ≤ Z.1, roundOrbit (zr_loopTM k) (fun c => zr_fieldLen (c.workTapePos 0) + 9) d r =
      zr_loopAt d (zoneStart (Z.1 - r)) := by
  intro r
  induction r with
  | zero =>
    intro _
    rw [roundOrbit_zero, Nat.sub_zero, ← hp.1]
    apply Cfg.ext <;> simp only [zr_loopAt, Function.update_eq_self]
  | succ r ih =>
    intro hr
    obtain ⟨i, hi⟩ : ∃ i : Fin Z.1, Z.1 - r = i.val + 1 := ⟨⟨Z.1 - r - 1, by omega⟩, by
      simp only
      omega⟩
    rw [roundOrbit_succ, ih (by omega), hi]
    have hR := zr_loop_round (zoneCells true Z.2 i) (zr_loopAt d (zoneStart (i + 1))) hd
      (zr_loop_zone_word Z i d hp) (fun _ => True) (fun _ _ _ _ => trivial)
    have hrun := ((round_iff _ _ _ _ _ _ _).mp hR).2.2.1
    rw [zr_loop_zone_test Z i d hp, zoneCells_length] at hrun
    simp only [zr_loopAt, Function.update_self]
    rw [zr_fieldLen_succ]
    simp only [zr_loopAt, Function.update_self] at hrun
    rw [hrun, show Z.1 - (r + 1) = i.val by omega]
    have hs := zoneStart_succ i.val
    apply Cfg.ext
    · simp only [hd]
    · rfl
    · rfl
    · funext j
      simp only [Function.update_idem]
      congr 1
      omega
    · rfl

/-- The loop configuration's fields: only the zoned head moves. -/
private lemma zr_loopAt_fields {k : ℕ} {x : List (ZoneSym k)}
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (p : ℤ) :
    (zr_loopAt d p).state = d.state ∧ (zr_loopAt d p).workTapes = d.workTapes ∧
      (zr_loopAt d p).workTapePos 0 = p ∧ (zr_loopAt d p).workTapePos 1 = d.workTapePos 1 :=
  ⟨rfl, rfl, by simp only [zr_loopAt, Function.update_self],
    by simp only [zr_loopAt, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]⟩

/-- **The return loop's run**, as a segment against its home exit inside the box
`[-1, zoneStart Z.1]` for the zoned head, the other head fixed.

**Proof sketch.** `Turing.Round.iterate` over the `Z.1 + 1` rounds of `zr_loop_round`, timed
by the field before the zoned head: before the last, round `r` crosses zone `Z.1 - r - 1`
(`zr_loop_orbit`); the last crosses the home and stops at the home exit. The round times add
up by `zr_loop_time_sum`. -/
private lemma zr_loop_segment {k : ℕ} {x : List (ZoneSym k)} (Z : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x) (hd : d.state = some ⟨false, some false⟩)
    (hp : zr_loopPre Z d) :
    Segment (zr_loopTM k) {some ⟨false, some true⟩}
      (HeadBox (fun j => if j = 0 then -1 else d.workTapePos j)
        (fun j => if j = 0 then (zoneStart Z.1 : ℤ) else d.workTapePos j))
      d { d with
        state := some ⟨false, some true⟩
        workTapePos := Function.update d.workTapePos 0 0 }
      (zoneStart Z.1 + 8 * (Z.1 + 1)) := by
  set τ : Cfg 2 (ZoneSym k) (Σ b, zr_loopPh b) x → ℕ :=
    fun c => zr_fieldLen (c.workTapePos 0) + 9 with hτ
  have hbox : ∀ p : Fin 2 → ℤ, -1 ≤ p 0 → p 0 ≤ zoneStart Z.1 → p 1 = d.workTapePos 1 →
      HeadBox (fun j => if j = 0 then -1 else d.workTapePos j)
        (fun j => if j = 0 then (zoneStart Z.1 : ℤ) else d.workTapePos j) p := by
    intro p h0 h1 h2
    rw [headBox_iff]
    intro j
    rw [Finset.mem_Icc]
    match j with
    | 0 => exact ⟨h0, h1⟩
    | 1 =>
      simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, h2]
      exact ⟨le_rfl, le_rfl⟩
  have hL := two_le_zoneStart Z.1
  have h0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  have hhome := zr_loop_round [Sum.inr fun t => some (Z.2 t).home] (zr_loopAt d (zoneStart 0))
    hd (zr_loop_home_word Z d hp)
    (HeadBox (fun j => if j = 0 then -1 else d.workTapePos j)
      (fun j => if j = 0 then (zoneStart Z.1 : ℤ) else d.workTapePos j))
    (fun p h₀ h₁ h₂ => by
      obtain ⟨-, -, e0, e1⟩ := zr_loopAt_fields d (zoneStart 0)
      have hm := zoneStart_mono (Nat.zero_le Z.1)
      have hlen : ([Sum.inr fun t => some (Z.2 t).home] : List (ZoneSym k)).length = 1 :=
        List.length_singleton
      exact hbox p (by omega) (by omega) (h₂.trans e1))
  have ht0 : τ (zr_loopAt d (zoneStart 0)) =
      ([Sum.inr fun t => some (Z.2 t).home] : List (ZoneSym k)).length + 9 := by
    simp only [hτ, (zr_loopAt_fields d _).2.2.1, zr_fieldLen_zero, List.length_singleton]
  have hround : ∀ r < Z.1 + 1,
      Round (zr_loopTM k) ⟨false, some false⟩ {some ⟨false, some true⟩}
        (HeadBox (fun j => if j = 0 then -1 else d.workTapePos j)
          (fun j => if j = 0 then (zoneStart Z.1 : ℤ) else d.workTapePos j))
        (roundOrbit (zr_loopTM k) τ d r) (roundOrbit (zr_loopTM k) τ d (r + 1))
        (τ (roundOrbit (zr_loopTM k) τ d r)) := by
    intro r hr
    rw [roundOrbit_succ, zr_loop_orbit Z d hd hp r (by omega)]
    rcases Nat.lt_or_ge r Z.1 with hlt | hge
    · obtain ⟨i, hi⟩ : ∃ i : Fin Z.1, Z.1 - r = i.val + 1 :=
        ⟨⟨Z.1 - r - 1, by omega⟩, by simp only; omega⟩
      rw [hi]
      have hs := zoneStart_succ i.val
      have hm := zoneStart_mono (show i.val + 1 ≤ Z.1 by omega)
      have hR := zr_loop_round (zoneCells true Z.2 i) (zr_loopAt d (zoneStart (i + 1))) hd
        (zr_loop_zone_word Z i d hp)
        (HeadBox (fun j => if j = 0 then -1 else d.workTapePos j)
          (fun j => if j = 0 then (zoneStart Z.1 : ℤ) else d.workTapePos j))
        (fun p h₀ h₁ h₂ => by
          obtain ⟨-, -, e0, e1⟩ := zr_loopAt_fields d (zoneStart (i + 1))
          have hlen := zoneCells_length true Z.2 i
          exact hbox p (by omega) (by omega) (h₂.trans e1))
      have ht : τ (zr_loopAt d (zoneStart (i + 1))) = (zoneCells true Z.2 i).length + 9 := by
        simp only [hτ, (zr_loopAt_fields d _).2.2.1, zr_fieldLen_succ, zoneCells_length]
      rw [ht, ((round_iff _ _ _ _ _ _ _).mp hR).2.2.1]
      exact hR
    · obtain rfl : r = Z.1 := by omega
      rw [Nat.sub_self, ht0, ((round_iff _ _ _ _ _ _ _).mp hhome).2.2.1]
      exact hhome
  have hseg := Round.iterate τ d
    (fun h => by
      have h' := Option.some_injective _ (Set.mem_singleton_iff.mp h)
      simp only [Sigma.mk.injEq, heq_eq_eq, Option.some.injEq, Bool.false_eq_true,
        and_false] at h')
    (hbox _ (by rw [hp.1]; omega) (by rw [hp.1]) rfl) (Z.1 + 1) hround
  have hend : roundOrbit (zr_loopTM k) τ d (Z.1 + 1) =
      { d with
        state := some ⟨false, some true⟩
        workTapePos := Function.update d.workTapePos 0 0 } := by
    rw [roundOrbit_succ, zr_loop_orbit Z d hd hp Z.1 le_rfl, Nat.sub_self, ht0,
      ((round_iff _ _ _ _ _ _ _).mp hhome).2.2.1, zr_loop_home_test Z d hp]
    obtain ⟨-, e1, e0, -⟩ := zr_loopAt_fields d (zoneStart 0)
    apply Cfg.ext
    · rfl
    · rfl
    · exact e1
    · funext j
      rw [e0, List.length_singleton, h0]
      simp only [zr_loopAt, Function.update_idem]
      congr 1
    · rfl
  have htime : ∑ r ∈ Finset.range (Z.1 + 1), τ (roundOrbit (zr_loopTM k) τ d r) =
      zoneStart Z.1 + 8 * (Z.1 + 1) := by
    rw [← zr_loop_time_sum Z.1]
    apply Finset.sum_congr rfl
    intro r hr
    rw [zr_loop_orbit Z d hd hp r (by rw [Finset.mem_range] at hr; omega)]
    simp only [hτ, (zr_loopAt_fields d _).2.2.1]
  rw [hend, htime] at hseg
  exact hseg

/-- **The return loop as a contract**: from the anchor, with the zoned head one past the last
right zone of `Z` and tape `0` agreeing with `Z`'s zoned tape from cell `-1`, the loop crosses
the `Z.1` zones and the home in `zoneStart Z.1 + 8 (Z.1 + 1)` steps and stops at the home exit,
the zoned head at home and nothing else changed. The zoned head stays in `[-1, zoneStart Z.1]`;
the other head is fixed. -/
private def zr_loopContract {k : ℕ} (x : List (ZoneSym k)) :
    Contract (zr_loopTM k) ⟨false, some false⟩ {some ⟨false, some true⟩} (ZoneData k) x :=
  Contract.ofSegment zr_loopPre (fun Z _ => zoneStart Z.1 + 8 * (Z.1 + 1))
    (fun _ d => { d with
      state := some ⟨false, some true⟩
      workTapePos := Function.update d.workTapePos 0 0 })
    (fun _ d j => if j = 0 then -1 else d.workTapePos j)
    (fun Z d j => if j = 0 then (zoneStart Z.1 : ℤ) else d.workTapePos j)
    (fun Z d hd hp => zr_loop_segment Z d hd hp) (fun _ _ _ _ => Set.mem_singleton _)

/-- The return home's first row: skip over the rest of the last right zone. Its precondition
carries the loop's: the skip ends one past the last zone of `Z`, and tape `0` agrees with `Z`'s
zoned tape from cell `-1`. The fields and the segment are the skip row's. -/
private def zr_returnSkipContract {k : ℕ} (x : List (ZoneSym k)) :
    Contract (skipTM 2 0) SeekPhase.run {some SeekPhase.done}
      (List (ZoneSym k) × ZoneData k) x :=
  let C := skipTM_contract 0 x
  Contract.ofSegment
    (fun i d => C.pre i.1 d ∧ d.workTapePos 0 + i.1.length + 1 = zoneStart i.2.1 ∧
      ∀ q : ℤ, -1 ≤ q → q < zoneStart i.2.1 → d.workTapes 0 q = zonedTape i.2.2 q)
    (fun i d => C.time i.1 d) (fun i d => C.post i.1 d) (fun i d => C.lo i.1 d)
    (fun i d => C.hi i.1 d)
    (fun i d hd hp => C.segment i.1 d hd hp.1) (fun i d hd hp => C.exit_mem i.1 d hd hp.1)

/-- **The return home**: skip over the rest of the last right zone of `Z`, then run the loop
home. -/
private def zr_returnContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_returnSkipContract x).seq (zr_loopContract x) Prod.snd fun i d _ hp => by
    rw [zr_returnSkipContract, Contract.ofSegment_pre] at hp
    rw [zr_loopContract, Contract.ofSegment_pre, zr_loopPre, zr_returnSkipContract,
      Contract.ofSegment_post, skipTM_contract_post]
    simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, seekPost_workTapes,
      seekPost_workTapePos, Function.update_self]
    exact ⟨hp.2.1, hp.2.2⟩

/-- The return home ends at the loop's home exit with the zoned head at home; the tapes, the
other head, the input position and the output are the start's.

**Proof sketch.** Substitute the skip's endpoint into the loop's endpoint. -/
private lemma zr_return_post {k : ℕ} {x : List (ZoneSym k)} (i : List (ZoneSym k) × ZoneData k)
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ (Σ b, zr_loopPh b)) x) :
    (zr_returnContract x).post i d =
      { d with
        state := some (Sum.inr ⟨false, some true⟩)
        workTapePos := Function.update d.workTapePos 0 0 } := by
  rw [zr_returnContract, Contract.seq_post, zr_loopContract, Contract.ofSegment_post,
    zr_returnSkipContract, Contract.ofSegment_post, skipTM_contract_post]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos, seekPost_inputPos]
  · funext j q
    simp only [Cfg.mapState_workTapes, seekPost_workTapes]
  · funext j
    simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_apply]
    split_ifs <;> rfl
  · simp only [Cfg.mapState_output, seekPost_output]

/-- The return home takes the skip, its seam and the loop. -/
private lemma zr_return_time {k : ℕ} {x : List (ZoneSym k)} (i : List (ZoneSym k) × ZoneData k)
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ (Σ b, zr_loopPh b)) x) :
    (zr_returnContract x).time i d =
      i.1.length + 2 + (zoneStart i.2.1 + 8 * (i.2.1 + 1)) := by
  rw [zr_returnContract, Contract.seq_time, zr_loopContract, Contract.ofSegment_time,
    zr_returnSkipContract, Contract.ofSegment_time, skipTM_contract_time]

/-- During the return home the zoned head stays in `[-1, zoneStart Z.1]` and the scratch head
is fixed, from any admissible start at or right of cell `-1`. -/
private lemma zr_return_bounds {k : ℕ} {x : List (ZoneSym k)} (i : List (ZoneSym k) × ZoneData k)
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ (Σ b, zr_loopPh b)) x)
    (hp : (zr_returnContract x).pre i d) (h0 : -1 ≤ d.workTapePos 0) :
    -1 ≤ (zr_returnContract x).lo i d 0 ∧ (zr_returnContract x).hi i d 0 ≤ zoneStart i.2.1 ∧
      (zr_returnContract x).lo i d 1 = d.workTapePos 1 ∧
      (zr_returnContract x).hi i d 1 = d.workTapePos 1 := by
  rw [zr_returnContract, Contract.seq_pre, zr_returnSkipContract, Contract.ofSegment_pre] at hp
  have he := hp.2.1
  simp only [Cfg.mapState_workTapePos] at he
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [zr_returnContract, Contract.seq_lo, Contract.seq_hi, zr_loopContract,
    Contract.ofSegment_lo, Contract.ofSegment_hi, zr_returnSkipContract,
    Contract.ofSegment_post, skipTM_contract_lo, skipTM_contract_hi, skipTM_contract_post,
    Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), show (1 : Fin 2) ≠ 0 by decide,
    if_true, if_false, min_self, max_self] <;>
  omega

/-- The right pass's index's outer half: the cells from its zoned endpoint to the separator. -/
private def zr_outerWord {k : ℕ} (D : ZoneData k) : List (ZoneSym k) :=
  List.replicate (2 ^ D.1) (Sum.inr fun _ => none)

/-- After the right pass, the outer half from the zoned head is followed by a blank: the skip
row's premise for `zr_outerWord`.

**Proof sketch.** Inside the new zone's outer half the endpoint formula gives the constant cell;
the next cell lies beyond the old layout (`Turing.zonedTape_blank_outside`). -/
private lemma zr_returnSkip_premise {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightPassContract x).pre D d) :
    ∀ p : ℤ, 0 ≤ p → p ≤ ((zr_outerWord D).length : ℤ) →
      ((zr_rightPassContract x).post D d).workTapes 0
          (((zr_rightPassContract x).post D d).workTapePos 0 + p) =
        FinTM.bufferTape (zr_outerWord D) p := by
  intro p hp0 hpl
  have hz : zoneRowPre D d := (zr_rightPass_pre D d) ▸ hp
  rw [zr_outerWord, List.length_replicate] at hpl
  rw [zr_outerWord]
  have hM : ((2 ^ D.1 : ℕ) : ℤ) = (2 : ℤ) ^ D.1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have hc : (zoneCapacity D.1 : ℤ) = 2 * (2 : ℤ) ^ D.1 := by
    rw [zoneCapacity_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hm : (0 : ℤ) < (2 : ℤ) ^ D.1 := by positivity
  rw [zr_rightPass_post D d hp]
  simp only [Function.update_self, true_and, show (0 : Fin 2) ≠ 1 by decide, false_and,
    if_false]
  rcases lt_or_eq_of_le hpl with hlt | heq
  · have hin : (zoneStart D.1 : ℤ) ≤ zoneStart D.1 + 2 ^ D.1 + p ∧
        zoneStart D.1 + 2 ^ D.1 + p < zoneStart D.1 + zoneCapacity D.1 := by
      constructor <;> omega
    rw [if_pos hin]
    have hout : ¬ (zoneStart D.1 + 2 ^ D.1 + p : ℤ) < zoneStart D.1 + 2 ^ D.1 := by omega
    simp only [hout, if_false]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, (Int.toNat_of_nonneg hp0).symm⟩
    rw [FinTM.bufferTape_nat, List.getElem?_replicate_of_lt (by omega)]
  · have hnin : ¬ ((zoneStart D.1 : ℤ) ≤ zoneStart D.1 + 2 ^ D.1 + p ∧
        zoneStart D.1 + 2 ^ D.1 + p < zoneStart D.1 + zoneCapacity D.1) := by
      omega
    rw [if_neg hnin, hz.1, zonedTape_blank_outside]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, (Int.toNat_of_nonneg hp0).symm⟩
      rw [FinTM.bufferTape_nat,
        List.getElem?_eq_none (by simp only [List.length_replicate]; omega)]
    · dsimp only
      have hs : (0 : ℤ) ≤ zoneStart D.1 := by positivity
      rw [abs_of_nonneg (by omega)]
      omega

/-- The re-wrapped right pass has the pass's precondition and endpoint. -/
private lemma zr_rightPassRow_eq {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_rightPassRow x).pre D d = (zr_rightPassContract x).pre D d ∧
      (zr_rightPassRow x).post D d = (zr_rightPassContract x).post D d :=
  ⟨(zr_singleton_fields _ _ _ D d).1, (zr_singleton_fields _ _ _ D d).2.2.1⟩

/-- **The seam into the return home**: the right pass's endpoint satisfies the return home's
precondition at the outer half and the extended data.

**Proof sketch.** The skip premise is `zr_returnSkip_premise`. The outer half ends one before
the separator after the new zone, the start of the next zone. On the nonnegative half-line the
endpoint is the extended zoned tape (`zr_rightPass_tape`); cell `-1` is the original's, which
the extension keeps (`Turing.zonedTape_extend`). -/
private lemma zr_rightReturn_link {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightPassRow x).pre D d) :
    (zr_returnContract x).pre (zr_outerWord D, zoneExtendData D)
      (((zr_rightPassRow x).post D d).mapState fun _ => Sum.inl SeekPhase.run) := by
  rw [(zr_rightPassRow_eq D d).1] at hp
  have hs := zoneStart_succ D.1
  have hc : zoneCapacity D.1 = 2 * 2 ^ D.1 := zoneCapacity_eq D.1
  have hM : ((2 ^ D.1 : ℕ) : ℤ) = (2 : ℤ) ^ D.1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have hs1 := two_le_zoneStart D.1
  rw [zr_returnContract, Contract.seq_pre, zr_returnSkipContract, Contract.ofSegment_pre,
    skipTM_contract_pre, (zr_rightPassRow_eq D d).2]
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
  refine ⟨zr_returnSkip_premise D d hp, ?_, ?_⟩
  · rw [zr_rightPass_post D d hp]
    simp only [Function.update_self, zr_outerWord, List.length_replicate, zoneExtendData]
    omega
  · intro q hq1 hq2
    simp only [zoneExtendData]
    rcases lt_or_ge q 0 with hneg | hnn
    · obtain rfl : q = -1 := by omega
      rw [(zr_rightPass_tape D d hp).2 _ (by omega), zonedTape_extend, if_neg]
      rw [show |(-1 : ℤ)| = 1 by norm_num]
      omega
    · exact (zr_rightPass_tape D d hp).1 q hnn

set_option synthInstance.maxSize 256 in
/-- Decidable equality of the right pass's twelve-leaf state type, given once, since the
default search for it gives up. -/
private def zr_decEqRP : DecidableEq (((SeekPhase ⊕ SeekPhase) ⊕ (SweepPhase ⊕ SeekPhase)) ⊕
    (SweepPhase ⊕ (((Option Bool ⊕ SeekPhase) ⊕ SeekPhase) ⊕ SweepPhase))) :=
  inferInstance

/-- **The right pass and the return home** as one contract: the right pass, then the skip over
the new zone's outer half and the loop home. -/
private def zr_rightReturnContract {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqRP
  (zr_rightPassRow x).seq (zr_returnContract x)
    (fun D => (zr_outerWord D, zoneExtendData D))
    fun D d _ hp => zr_rightReturn_link D d hp

/-- The right pass and the return home need exactly the original zoned input. -/
private lemma zr_rightReturn_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_rightReturnContract x).pre D d ↔ zoneRowPre D d := by
  letI := zr_decEqRP
  rw [zr_rightReturnContract, Contract.seq_pre, (zr_rightPassRow_eq D _).1, zr_rightPass_pre]
  simp only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- **After the right pass and the return home**: tape `0` is the extended zoned tape on the
nonnegative half-line and the original on the nonpositive one; scratch holds the ruler
`[q, q + 2^ℓ)` of `inl false` from its head `q`, blank elsewhere; both heads, the input
position and the output are the start's.

**Proof sketch.** The return home changes only the zoned head and the state
(`zr_return_post`); the right pass's endpoint gives the tapes (`zr_rightPass_post`,
`zr_rightPass_tape`). -/
private lemma zr_rightReturn_post {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightReturnContract x).pre D d) :
    (zr_rightReturnContract x).post D d =
      ⟨some (Sum.inr (Sum.inr ⟨false, some true⟩)), d.inputPos,
        fun j q =>
          if j = 0 then
            (if 0 ≤ q then zonedTape (fun t => (D.2 t).extend) q else zonedTape D.2 q)
          else if d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + 2 ^ D.1 then
            some (Sum.inl false)
          else none,
        d.workTapePos, d.output⟩ := by
  letI := zr_decEqRP
  have hz := (zr_rightReturn_pre D d).mp hp
  have hp' : (zr_rightPassContract x).pre D (d.mapState fun _ =>
      Sum.inl (Sum.inl (Sum.inl SeekPhase.run))) := by
    rw [zr_rightPass_pre]
    simpa only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      using hz
  have ht := zr_rightPass_tape D _ hp'
  rw [zr_rightReturnContract, Contract.seq_post, zr_return_post, (zr_rightPassRow_eq D _).2]
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos, zr_rightPass_post D _ hp']
  · funext j q
    simp only [Cfg.mapState_workTapes]
    by_cases hj : j = 0
    · rw [if_pos hj]
      subst hj
      by_cases hq : 0 ≤ q
      · rw [if_pos hq]
        exact ht.1 q hq
      · rw [if_neg hq]
        exact ht.2 q (by omega)
    · rw [if_neg hj]
      have hj1 : j = 1 := by omega
      subst hj1
      rw [zr_rightPass_post D _ hp']
      simp only [show (1 : Fin 2) ≠ 0 by decide, false_and, if_false, true_and,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hz.2.2]
  · funext j
    simp only [Cfg.mapState_workTapePos, Function.update_apply, zr_rightPass_post D _ hp']
    split_ifs with hj
    · subst hj
      exact hz.2.1.symm
    · rfl
  · simp only [Cfg.mapState_output, zr_rightPass_post D _ hp']

/-- The right pass and the return home take the pass, the seam, the skip over the outer half,
its seam and the loop over the extended layout. -/
private lemma zr_rightReturn_time {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_rightReturnContract x).time D d =
      zoneStart D.1 + 10 * 2 ^ D.1 + 23 + 1 +
        (2 ^ D.1 + 2 + (zoneStart (D.1 + 1) + 8 * (D.1 + 2))) := by
  letI := zr_decEqRP
  rw [zr_rightReturnContract, Contract.seq_time, zr_return_time, zr_rightPassRow,
    zr_singletonContract, Contract.ofSegment_time, zr_rightPass_time]
  simp only [zr_outerWord, List.length_replicate, zoneExtendData]

/-- The right pass and the return home keep the zoned head in `[-1, zoneStart (ℓ + 1)]` and the
scratch head between the ruler's left delimiter and the cell past its right one. -/
private lemma zr_rightReturn_bounds {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightReturnContract x).pre D d) :
    -1 ≤ (zr_rightReturnContract x).lo D d 0 ∧
      (zr_rightReturnContract x).hi D d 0 ≤ zoneStart (D.1 + 1) ∧
      d.workTapePos 1 - 1 ≤ (zr_rightReturnContract x).lo D d 1 ∧
      (zr_rightReturnContract x).hi D d 1 ≤ d.workTapePos 1 + ((2 ^ D.1 : ℕ) : ℤ) + 1 := by
  letI := zr_decEqRP
  have hz := (zr_rightReturn_pre D d).mp hp
  have hp' : (zr_rightPassContract x).pre D (d.mapState fun _ =>
      Sum.inl (Sum.inl (Sum.inl SeekPhase.run))) := by
    rw [zr_rightPass_pre]
    simpa only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      using hz
  have hb := zr_rightPass_bounds D _ hp'
  have he := zr_rightPass_envelope D _ hp'
  have hl := zr_rightReturn_link (x := x) D (d.mapState fun _ =>
    Sum.inl (Sum.inl (Sum.inl SeekPhase.run))) (by rw [(zr_rightPassRow_eq D _).1]; exact hp')
  have hpos : (((zr_rightPassRow x).post D (d.mapState fun _ =>
      Sum.inl (Sum.inl (Sum.inl SeekPhase.run)))).mapState fun _ =>
        (Sum.inl SeekPhase.run : SeekPhase ⊕ (Σ b, zr_loopPh b))).workTapePos =
          Function.update (d.workTapePos) 0 (zoneStart D.1 + 2 ^ D.1) := by
    funext j
    rw [Cfg.mapState_workTapePos, (zr_rightPassRow_eq D _).2, zr_rightPass_post D _ hp']
    simp only [Function.update_apply, Cfg.mapState_workTapePos]
  have h2 : (0 : ℤ) ≤ 2 ^ D.1 := by positivity
  have h3 : (0 : ℤ) ≤ ((2 : ℕ) : ℤ) ^ D.1 := by positivity
  have hr := zr_return_bounds _ _ hl (by rw [hpos, Function.update_self]; omega)
  have hlh := fun j => (zr_singleton_fields (zr_rightPassContract x)
    (Sum.inr (Sum.inr (Sum.inr SweepPhase.done)))
    (by simp only [Set.image_singleton, Option.map_some]) D
    (d.mapState fun _ => Sum.inl (Sum.inl (Sum.inl SeekPhase.run)))).2.2.2 j
  have hs := zoneStart_succ D.1
  rw [hpos, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] at hr
  simp only [Cfg.mapState_workTapePos] at hb hr
  simp only [zr_rightReturnContract, Contract.seq_lo, Contract.seq_hi, (hlh _).1, (hlh _).2]
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have hext : (zoneExtendData D).1 = D.1 + 1 := rfl
  rw [hext] at r2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_min (by omega) r1
  · exact max_le (by omega) r2
  · rw [r3]
    exact le_min hb.2.2.1 (by omega)
  · rw [r4]
    exact max_le hb.2.2.2 (by omega)

/-- The scratch tape of a constant ruler: `n` cells `inl false` from cell `q`, blank elsewhere. -/
private def zr_rulerTape {k : ℕ} (n : ℕ) (q : ℤ) (r : ℤ) : Option (ZoneSym k) :=
  if q ≤ r ∧ r < q + n then some (Sum.inl false) else none

/-- The constant ruler word, as a delimited buffer, is the ruler tape read from its first cell
rightward, and also from its last cell leftward. -/
private lemma zr_rulerTape_word {k : ℕ} (n : ℕ) (q p : ℤ) :
    FinTM.bufferTape (List.replicate n (Sum.inl false : ZoneSym k)) p =
        zr_rulerTape n q (q + p) ∧
      FinTM.bufferTape (List.replicate n (Sum.inl false : ZoneSym k)) p =
        zr_rulerTape n q (q + n - 1 - p) := by
  have h : FinTM.bufferTape (List.replicate n (Sum.inl false : ZoneSym k)) p =
      if 0 ≤ p ∧ p < n then some (Sum.inl false) else none := by
    rw [FinTM.bufferTape_eq]
    by_cases h0 : 0 ≤ p
    · rw [if_pos h0]
      by_cases h1 : p < n
      · rw [if_pos ⟨h0, h1⟩, List.getElem?_replicate_of_lt (by omega)]
      · rw [if_neg (fun h => h1 h.2),
          List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
    · rw [if_neg h0, if_neg (fun h => h0 h.1)]
  rw [h, zr_rulerTape, zr_rulerTape]
  constructor <;> split_ifs <;> first | rfl | omega

/-- Scratch holds the constant ruler of `n ≥ 1` cells, starting `c` cells left of its head. -/
private def zr_scratchAt {k : ℕ} {S : Type} {x : List (ZoneSym k)} (c : ℤ) (n : ℕ)
    (d : Cfg 2 (ZoneSym k) S x) : Prop :=
  0 < n ∧ ∀ r, d.workTapes 1 r = zr_rulerTape n (d.workTapePos 1 - c) r

/-- The ruler premise follows the scratch head over an unchanged scratch tape. -/
private lemma zr_scratchAt_move {k : ℕ} {S S' : Type} {x : List (ZoneSym k)} {c : ℤ} {n : ℕ}
    {d : Cfg 2 (ZoneSym k) S x} (c' : ℤ) (e : Cfg 2 (ZoneSym k) S' x)
    (hp : zr_scratchAt c n d) (ht : ∀ r, e.workTapes 1 r = d.workTapes 1 r)
    (hh : e.workTapePos 1 - c' = d.workTapePos 1 - c) : zr_scratchAt c' n e :=
  ⟨hp.1, fun r => by rw [ht, hp.2, hh]⟩

/-- With the ruler at the scratch head, scratch read from its head is the ruler's delimited
word: the premise of every row that reads the ruler from its first cell. -/
private lemma zr_scratchAt_word {k : ℕ} {S : Type} {x : List (ZoneSym k)} {n : ℕ}
    {d : Cfg 2 (ZoneSym k) S x} (hp : zr_scratchAt 0 n d) (p : ℤ) :
    d.workTapes 1 (d.workTapePos 1 + p) =
      FinTM.bufferTape (List.replicate n (Sum.inl false)) p := by
  rw [hp.2, sub_zero, ← (zr_rulerTape_word n _ p).1]

/-- From the ruler's first cell, its word is the skip row's premise. -/
private lemma zr_scratchSkip_pre {k : ℕ} {x : List (ZoneSym k)} (n : ℕ)
    (d : Cfg 2 (ZoneSym k) SeekPhase x) (hp : zr_scratchAt 0 n d) :
    (skipTM_contract 1 x).pre (List.replicate n (Sum.inl false)) d := by
  rw [skipTM_contract_pre]
  exact fun p _ _ => zr_scratchAt_word hp p

/-- Skip the scratch ruler from its first cell to the cell past its right delimiter. -/
private def zr_scratchSkipContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (skipTM_contract 1 x) (fun n => List.replicate n (Sum.inl false))
    (fun n d => zr_scratchAt 0 n d) zr_scratchSkip_pre

/-- Two scratch steps along `dir`; the ruler premise moves with the head. -/
private def zr_twoStepsContract {k : ℕ} (dir : SignType) (off : ℕ → ℤ)
    (x : List (ZoneSym k)) :=
  zr_singletonContract
    ((zr_stepContract 1 dir x fun n d => zr_scratchAt (off n) n d).seq
      (zr_stepContract 1 dir x fun n d => zr_scratchAt (off n + dir) n d) (fun n => n)
      fun n d _ hp => by
        simp only [zr_stepContract, Contract.ofSegment_pre, Contract.ofSegment_post] at hp ⊢
        refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_ <;>
        simp only [zr_cellContract, zr_cellPost, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Function.update_self]
        ring)
    (Sum.inr (some false))

/-- Two scratch steps move only the scratch head, by `2 dir`; they take three steps, and the
scratch head stays between its two ends. -/
private lemma zr_twoSteps_fields {k : ℕ} {x : List (ZoneSym k)} (dir : SignType)
    (off : ℕ → ℤ) (n : ℕ) (d : Cfg 2 (ZoneSym k) (Option Bool ⊕ Option Bool) x) :
    (zr_twoStepsContract dir off x).time n d = 3 ∧
      (zr_twoStepsContract dir off x).post n d =
        { d with
          state := some (Sum.inr (some false))
          workTapePos := Function.update d.workTapePos 1 (d.workTapePos 1 + 2 * (dir : ℤ)) } ∧
      (zr_twoStepsContract dir off x).lo n d 0 = d.workTapePos 0 ∧
      (zr_twoStepsContract dir off x).hi n d 0 = d.workTapePos 0 ∧
      (zr_twoStepsContract dir off x).lo n d 1 = d.workTapePos 1 + min 0 (2 * (dir : ℤ)) ∧
      (zr_twoStepsContract dir off x).hi n d 1 = d.workTapePos 1 + max 0 (2 * (dir : ℤ)) := by
  rw [zr_twoStepsContract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zr_singletonContract, Contract.ofSegment_time, Contract.seq_time,
      zr_stepContract, zr_cellContract]
  · simp only [zr_singletonContract, Contract.ofSegment_post, Contract.seq_post,
      zr_stepContract, zr_cellContract, zr_cellPost]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos]
    · funext j q
      simp only [Cfg.mapState_workTapes]
    · funext j
      by_cases hj : j = 1
      · subst hj
        simp only [Cfg.mapState_workTapePos, Function.update_self]
        ring
      · simp only [Cfg.mapState_workTapePos, Function.update_of_ne hj]
    · simp only [Cfg.mapState_output]
  all_goals
    simp only [zr_singletonContract, Contract.ofSegment_lo, Contract.ofSegment_hi,
      Contract.seq_lo, Contract.seq_hi, zr_stepContract,
      Contract.ofSegment_post, zr_cellContract, zr_cellPost, Cfg.mapState_workTapePos,
      Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), min_self,
      max_self]
  all_goals
    rcases dir with _ | _ | _ <;> simp only [SignType.zero_eq_zero, SignType.neg_eq_neg_one,
      SignType.pos_eq_one, SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one] <;> omega

/-- From the ruler's last cell, its word read leftward is the adjusted walk's premise. -/
private lemma zr_leftWalk_pre {k : ℕ} {x : List (ZoneSym k)} (n : ℕ)
    (d : Cfg 2 (ZoneSym k) ((Option Bool) ⊕ SeekPhase) x)
    (hp : zr_scratchAt ((n : ℤ) - 1) n d) :
    (zr_adjustedWalkContract (-1) x).pre (List.replicate n (Sum.inl false)) d := by
  rw [zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre,
    zr_rulerStepContract, zr_stepContract, Contract.ofSegment_pre]
  refine ⟨List.ne_nil_of_length_pos (by rw [List.length_replicate]; exact hp.1), ?_⟩
  intro p _ _
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hp.2, SignType.coe_neg_one]
  rw [(zr_rulerTape_word n (d.workTapePos 1 - ((n : ℤ) - 1)) p).2]
  congr 1
  ring

/-- The leftward adjusted walk over the scratch ruler from its last cell, indexed by the ruler
length. -/
private def zr_leftWalkContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (zr_adjustedWalkContract (-1) x)
    (fun n => List.replicate n (Sum.inl false)) (fun n d => zr_scratchAt ((n : ℤ) - 1) n d)
    zr_leftWalk_pre

/-- The leftward walk takes the ruler length plus two steps and moves both heads left by the
length, scratch one cell more; the zoned head stays between its ends, scratch between its end
and its start. -/
private lemma zr_leftWalk_fields {k : ℕ} {x : List (ZoneSym k)} (n : ℕ) (hn : 0 < n)
    (d : Cfg 2 (ZoneSym k) ((Option Bool) ⊕ SeekPhase) x) :
    (zr_leftWalkContract x).time n d = n + 2 ∧
      (zr_leftWalkContract x).post n d =
        { d with
          state := some (Sum.inr SeekPhase.done)
          workTapePos := fun j => d.workTapePos j - n - if j = 1 then 1 else 0 } ∧
      (zr_leftWalkContract x).lo n d 0 = d.workTapePos 0 - n ∧
      (zr_leftWalkContract x).hi n d 0 = d.workTapePos 0 ∧
      (zr_leftWalkContract x).lo n d 1 = d.workTapePos 1 - n - 1 ∧
      (zr_leftWalkContract x).hi n d 1 = d.workTapePos 1 := by
  have hw : List.replicate n (Sum.inl false : ZoneSym k) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [List.length_replicate]; exact hn)
  rw [zr_leftWalkContract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zr_reindexContract, Contract.ofSegment_time, zr_adjustedWalkContract,
      zr_singletonContract, Contract.seq_time, zr_rulerStepContract, zr_stepContract,
      zr_cellContract, walkTM_contract_time, List.length_tail, List.length_replicate]
    omega
  · rw [zr_reindexContract, Contract.ofSegment_post, zr_adjustedWalk_post (-1) _ d hw]
    congr 1
    funext j
    simp only [List.length_replicate, SignType.coe_neg_one]
    split_ifs <;> ring
  all_goals
    simp only [zr_reindexContract, Contract.ofSegment_lo, Contract.ofSegment_hi,
      zr_adjustedWalkContract, zr_singletonContract, Contract.seq_lo, Contract.seq_hi,
      Contract.seq_post, zr_rulerStepContract, zr_stepContract, Contract.ofSegment_post,
      zr_cellContract, zr_cellPost, walkTM_contract_lo, walkTM_contract_hi,
      Cfg.mapState_workTapePos, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), List.length_tail,
      List.length_replicate, SignType.coe_neg_one, if_true]
    omega

/-- After skipping the ruler, scratch is two cells right of the ruler's last cell. -/
private lemma zr_leftMove_link₁ {k : ℕ} {x : List (ZoneSym k)} (n : ℕ)
    (d : Cfg 2 (ZoneSym k) SeekPhase x) (hp : (zr_scratchSkipContract x).pre n d) :
    zr_scratchAt ((n : ℤ) + 1) n ((zr_scratchSkipContract x).post n d) := by
  rw [zr_scratchSkipContract, zr_reindexContract, Contract.ofSegment_pre] at hp
  rw [zr_scratchSkipContract, zr_reindexContract, Contract.ofSegment_post,
    skipTM_contract_post]
  refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_
  · simp only [seekPost_workTapes]
  · simp only [seekPost_workTapePos, Function.update_self, List.length_replicate]
    ring

/-- **The left move**: skip the scratch ruler, step back onto its last cell, walk left over it
with the zoned head, and step scratch back to the ruler's first cell. Only the zoned head
moves, by the ruler length. -/
private def zr_leftMoveContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_scratchSkipContract x).seq
    ((zr_twoStepsContract (-1) (fun n => (n : ℤ) + 1) x).seq
      ((zr_leftWalkContract x).seq (zr_twoStepsContract 1 (fun _ => -2) x) (fun n => n)
        fun n d _ hp => by
          rw [zr_leftWalkContract, zr_reindexContract, Contract.ofSegment_pre] at hp
          rw [zr_twoStepsContract, (zr_singleton_fields _ _ _ _ _).1, Contract.seq_pre,
            zr_stepContract, Contract.ofSegment_pre,
            (zr_leftWalk_fields n hp.1 d).2.1]
          refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_ <;>
          simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, if_true]
          ring)
      (fun n => n) fun n d _ hp => by
        rw [zr_twoStepsContract, (zr_singleton_fields _ _ _ _ _).1, Contract.seq_pre,
          zr_stepContract, Contract.ofSegment_pre] at hp
        rw [Contract.seq_pre, zr_leftWalkContract, zr_reindexContract, Contract.ofSegment_pre,
          (zr_twoSteps_fields (-1) _ n d).2.1]
        refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_ <;>
        simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Function.update_self,
          SignType.coe_neg_one]
        ring)
    (fun n => n) fun n d _ hp => by
      rw [Contract.seq_pre, zr_twoStepsContract, (zr_singleton_fields _ _ _ _ _).1,
        Contract.seq_pre, zr_stepContract, Contract.ofSegment_pre]
      exact zr_scratchAt_move _ _ (zr_leftMove_link₁ n d hp)
        (fun r => by simp only [Cfg.mapState_workTapes])
        (by simp only [Cfg.mapState_workTapePos])

/-- The left move takes twice the ruler length plus twelve steps and moves only the zoned head,
left by the ruler length. The zoned head stays between its two ends; scratch between two cells
left of its start and the cell past the ruler's right delimiter. -/
private lemma zr_leftMove_fields {k : ℕ} {x : List (ZoneSym k)} (n : ℕ) (hn : 0 < n) (d) :
    (zr_leftMoveContract x).time n d = 2 * n + 12 ∧
      (zr_leftMoveContract x).post n d =
        { d with
          state := some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (some false)))))
          workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 - n) } ∧
      (zr_leftMoveContract x).lo n d 0 = d.workTapePos 0 - n ∧
      (zr_leftMoveContract x).hi n d 0 = d.workTapePos 0 ∧
      (zr_leftMoveContract x).lo n d 1 = d.workTapePos 1 - 2 ∧
      (zr_leftMoveContract x).hi n d 1 = d.workTapePos 1 + n + 1 := by
  rw [zr_leftMoveContract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Contract.seq_time, zr_twoSteps_fields, zr_leftWalk_fields n hn,
      zr_scratchSkipContract, zr_reindexContract, Contract.ofSegment_time,
      skipTM_contract_time, List.length_replicate]
    omega
  · simp only [Contract.seq_post, zr_twoSteps_fields, zr_leftWalk_fields n hn,
      zr_scratchSkipContract, zr_reindexContract, Contract.ofSegment_post, skipTM_contract_post]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos, seekPost_inputPos]
    · funext j q
      simp only [Cfg.mapState_workTapes, seekPost_workTapes]
    · funext j
      by_cases hj : j = 1
      · subst hj
        simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
          Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), if_true, List.length_replicate,
          SignType.coe_one, SignType.coe_neg_one]
        ring
      · have hj0 : j = 0 := by omega
        subst hj0
        simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
          Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), show (0 : Fin 2) ≠ 1 by decide,
          if_false, sub_zero]
    · simp only [Cfg.mapState_output, seekPost_output]
  all_goals
    simp only [Contract.seq_lo, Contract.seq_hi, zr_twoSteps_fields,
      zr_leftWalk_fields n hn, zr_scratchSkipContract, zr_reindexContract,
      Contract.ofSegment_lo, Contract.ofSegment_hi, Contract.ofSegment_post,
      skipTM_contract_lo, skipTM_contract_hi, skipTM_contract_post, Cfg.mapState_workTapePos,
      seekPost_workTapePos, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), show (0 : Fin 2) ≠ 1 by decide,
      if_true, if_false, List.length_replicate, SignType.coe_one, SignType.coe_neg_one]
    omega

/-- The left move with its nested exit normalized, for sequencing. -/
private abbrev zr_leftMoveRow {k : ℕ} (x : List (ZoneSym k)) :=
  zr_singletonContract (zr_leftMoveContract x)
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr (some false)))))

/-- The left move needs only the ruler at the scratch head. -/
private lemma zr_leftMove_pre {k : ℕ} {x : List (ZoneSym k)} (n : ℕ) (d) :
    (zr_leftMoveRow x).pre n d ↔ zr_scratchAt 0 n d := by
  rw [(zr_singleton_fields _ _ _ n d).1, zr_leftMoveContract, Contract.seq_pre,
    zr_scratchSkipContract, zr_reindexContract, Contract.ofSegment_pre]
  simp only [zr_scratchAt, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- With the ruler at the scratch head, its word is the half-zone copy's premise. -/
private lemma zr_halfWrite_pre {k : ℕ} {x : List (ZoneSym k)} (inner : Bool) (n : ℕ)
    (d : Cfg 2 (ZoneSym k) SweepPhase x) (hp : zr_scratchAt 0 n d) :
    (zr_halfCopyContract inner x).pre (List.replicate n (Sum.inl false)) d := by
  rw [zr_halfCopyContract, copyMapTM_contract_pre]
  exact fun p _ _ => zr_scratchAt_word hp p

/-- One half-zone copy from the scratch ruler, indexed by the ruler length. -/
private def zr_halfWriteContract {k : ℕ} (inner : Bool) (x : List (ZoneSym k)) :=
  zr_reindexContract (zr_halfCopyContract inner x) (fun n => List.replicate n (Sum.inl false))
    (fun n d => zr_scratchAt 0 n d) (zr_halfWrite_pre inner)

set_option synthInstance.maxSize 256 in
/-- Decidable equality of the left move's state type, given once for its seams, since the
default search for it gives up. -/
private def zr_decEqLM : DecidableEq (SeekPhase ⊕ ((Option Bool ⊕ Option Bool) ⊕
    ((Option Bool ⊕ SeekPhase) ⊕ (Option Bool ⊕ Option Bool)))) :=
  inferInstance

/-- **The left zone writer**: from the zoned head at the cell right of the separator to be
written, step onto it, move left by the ruler, write the inner half, move left again and write
the outer half. The zoned head ends at the zone's outer end; scratch is unchanged. -/
private def zr_leftWriteContract {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqLM
  (zr_stepContract 0 (-1) x fun n d => zr_scratchAt 0 n d).seq
    ((zr_leftMoveRow x).seq
      ((zr_halfWriteContract true x).seq
        ((zr_leftMoveRow x).seq (zr_halfWriteContract false x) (fun n => n)
          fun n d _ hp => by
            rw [zr_leftMove_pre] at hp
            rw [zr_halfWriteContract, zr_reindexContract, Contract.ofSegment_pre,
              (zr_singleton_fields _ _ _ _ _).2.2.1, (zr_leftMove_fields n hp.1 d).2.1]
            refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_ <;>
            simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
              Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)])
        (fun n => n) fun n d _ hp => by
          rw [zr_halfWriteContract, zr_reindexContract, Contract.ofSegment_pre] at hp
          rw [Contract.seq_pre, zr_leftMove_pre, zr_halfWriteContract, zr_reindexContract,
            Contract.ofSegment_post, zr_halfCopy_post]
          refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_ <;>
          simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
            show (1 : Fin 2) ≠ 0 by decide, false_and, if_false])
      (fun n => n) fun n d _ hp => by
        rw [zr_leftMove_pre] at hp
        rw [Contract.seq_pre, zr_halfWriteContract, zr_reindexContract, Contract.ofSegment_pre,
          (zr_singleton_fields _ _ _ _ _).2.2.1, (zr_leftMove_fields n hp.1 d).2.1]
        refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_ <;>
        simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
          Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)])
    (fun n => n) fun n d _ hp => by
      rw [zr_stepContract, Contract.ofSegment_pre] at hp
      rw [Contract.seq_pre, zr_leftMove_pre, zr_stepContract, Contract.ofSegment_post]
      refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_ <;>
      simp only [zr_cellContract, zr_cellPost, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- The left zone writer needs only the ruler at the scratch head. -/
private lemma zr_leftWrite_pre {k : ℕ} {x : List (ZoneSym k)} (n : ℕ) (d) :
    (zr_leftWriteContract x).pre n d ↔ zr_scratchAt 0 n d := by
  letI := zr_decEqLM
  rw [zr_leftWriteContract, Contract.seq_pre, zr_stepContract, Contract.ofSegment_pre]
  simp only [zr_scratchAt, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- **The left zone writer's fields**: `8n + 33` steps; tape `0` gets the zone of `2n` cells
ending at the cell left of the start, its outer half empty slots and its inner half stored
virtual blanks; the zoned head ends at the zone's outer end, everything else unchanged. The
zoned head stays within the zone and its delimiter cells, scratch within two cells left of its
start and the cell past the ruler's right delimiter. -/
private lemma zr_leftWrite_fields {k : ℕ} {x : List (ZoneSym k)} (n : ℕ) (hn : 0 < n) (d) :
    (zr_leftWriteContract x).time n d = 8 * n + 33 ∧
      (zr_leftWriteContract x).post n d =
        { d with
          state := some (Sum.inr (Sum.inr (Sum.inr (Sum.inr SweepPhase.done))))
          workTapes := fun j r =>
            if j = 0 ∧ d.workTapePos 0 - 1 - 2 * n ≤ r ∧ r < d.workTapePos 0 - 1 then
              some (.inr fun _ => if r < d.workTapePos 0 - 1 - n then none else some none)
            else d.workTapes j r
          workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 - 1 - 2 * n) } ∧
      (zr_leftWriteContract x).lo n d 0 = d.workTapePos 0 - 2 - 2 * n ∧
      (zr_leftWriteContract x).hi n d 0 = d.workTapePos 0 ∧
      (zr_leftWriteContract x).lo n d 1 = d.workTapePos 1 - 2 ∧
      (zr_leftWriteContract x).hi n d 1 = d.workTapePos 1 + n + 1 := by
  letI := zr_decEqLM
  rw [zr_leftWriteContract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Contract.seq_time, zr_stepContract, Contract.ofSegment_time, zr_cellContract,
      zr_leftMove_fields n hn, zr_halfWriteContract, zr_reindexContract,
      zr_halfCopyContract, copyMapTM_contract_time, List.length_replicate]
    omega
  · simp only [Contract.seq_post, zr_stepContract, Contract.ofSegment_post, zr_cellContract,
      zr_cellPost, zr_leftMove_fields n hn, zr_halfWriteContract,
      zr_reindexContract, zr_halfCopy_post]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos]
    · funext j r
      by_cases hj : j = 0
      · subst hj
        simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Function.update_self,
          List.length_replicate, SignType.coe_neg_one, Bool.false_eq_true, if_true, if_false,
          true_and]
        split_ifs <;> first | rfl | omega
      · simp only [Cfg.mapState_workTapes, hj, false_and, if_false]
    · funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Cfg.mapState_workTapePos, Function.update_self, SignType.coe_neg_one]
        ring
      · simp only [Cfg.mapState_workTapePos, Function.update_of_ne hj]
    · simp only [Cfg.mapState_output]
  all_goals
    simp only [Contract.seq_lo, Contract.seq_hi, zr_stepContract,
      Contract.ofSegment_lo, Contract.ofSegment_hi, Contract.ofSegment_post, zr_cellContract,
      zr_cellPost, zr_leftMove_fields n hn, zr_halfWriteContract,
      zr_reindexContract, zr_halfCopyContract, copyMapTM_contract_lo, copyMapTM_contract_hi,
      copyMapTM_contract_post, sweepPost_workTapePos, Cfg.mapState_workTapePos,
      Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
      List.length_replicate, SignType.coe_neg_one, or_true, true_or, if_true]
    omega

/-- The left zones as fields read rightward from the outermost cell: each zone reversed, the
outermost zone first. -/
private def zr_leftFields {k : ℕ} (D : ZoneData k) : List (List (ZoneSym k)) :=
  List.ofFn fun i : Fin D.1 => (zoneCells false D.2 i.rev).reverse

/-- **The left pass's precondition**, by local facts: the zoned head at home; tape `0` agreeing
with the zoned tape on `[-zoneStart ℓ, 0]`; scratch holding the ruler of the new half-capacity
`2^ℓ` from its head, blank elsewhere. -/
private def zr_leftPre {k : ℕ} {S : Type} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) S x) : Prop :=
  d.workTapePos 0 = 0 ∧
    (∀ q : ℤ, -(zoneStart D.1 : ℤ) ≤ q → q ≤ 0 → d.workTapes 0 q = zonedTape D.2 q) ∧
    zr_scratchAt 0 (2 ^ D.1) d

/-- Seeking the left layout's outermost cell from home, indexed by the zone data. -/
private def zr_leftSeekContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (seekStartTM_contract 0 x) zr_leftFields (fun D d => zr_leftPre D d)
    fun D d hp => zr_seekStart_pre D.2 d hp.1 hp.2.1

/-- **The left pass**: seek the left layout's outermost cell, then write the new left zone past
it with the scratch ruler of the new half-capacity. -/
private def zr_leftPassContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_leftSeekContract x).seq (zr_leftWriteContract x) (fun D => 2 ^ D.1) fun D d _ hp => by
    rw [zr_leftSeekContract, zr_reindexContract, Contract.ofSegment_pre] at hp
    rw [zr_leftWrite_pre, zr_leftSeekContract, zr_reindexContract, Contract.ofSegment_post,
      seekStartTM_contract_post]
    refine zr_scratchAt_move _ _ hp.2.2 (fun r => ?_) ?_ <;>
    simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, seekPost_workTapes,
      seekPost_workTapePos, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- **The left pass's fields**: from home, `zoneStart ℓ + 8 · 2^ℓ + 36` steps; tape `0` gets the
new left zone `[2 - zoneStart (ℓ + 1), -zoneStart ℓ]`, its outer half empty slots and its inner
half stored virtual blanks; the zoned head ends at the zone's outer end, everything else
unchanged. The zoned head stays in `[1 - zoneStart (ℓ + 1), 0]`; scratch within two cells left
of its start and the cell past the ruler's right delimiter. -/
private lemma zr_leftPass_fields {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_leftPassContract x).pre D d) :
    (zr_leftPassContract x).time D d = zoneStart D.1 + 8 * 2 ^ D.1 + 36 ∧
      (zr_leftPassContract x).post D d =
        { d with
          state := some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr SweepPhase.done)))))
          workTapes := fun j r =>
            if j = 0 ∧ 2 - (zoneStart (D.1 + 1) : ℤ) ≤ r ∧
                r < 2 - zoneStart (D.1 + 1) + 2 * 2 ^ D.1 then
              some (.inr fun _ => if r < 2 - zoneStart (D.1 + 1) + 2 ^ D.1 then none
                else some none)
            else d.workTapes j r
          workTapePos := Function.update d.workTapePos 0 (2 - zoneStart (D.1 + 1)) } ∧
      (zr_leftPassContract x).lo D d 0 = 1 - zoneStart (D.1 + 1) ∧
      (zr_leftPassContract x).hi D d 0 = 0 ∧
      (zr_leftPassContract x).lo D d 1 = d.workTapePos 1 - 2 ∧
      (zr_leftPassContract x).hi D d 1 = d.workTapePos 1 + 2 ^ D.1 + 1 := by
  have hz : zr_leftPre D (d.mapState fun _ => SeekPhase.run) := by
    rw [zr_leftPassContract, Contract.seq_pre, zr_leftSeekContract, zr_reindexContract,
      Contract.ofSegment_pre] at hp
    exact hp
  have h0 : d.workTapePos 0 = 0 := by
    simpa only [Cfg.mapState_workTapePos] using hz.1
  have hreach := zr_left_reach D.2
  have hoff := zr_left_offset D.2 D.1 le_rfl
  have hs0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  rw [Nat.sub_self, hs0] at hoff
  have hn : 0 < 2 ^ D.1 := Nat.two_pow_pos D.1
  have hcast : ((2 ^ D.1 : ℕ) : ℤ) = 2 ^ D.1 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [zr_leftPassContract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Contract.seq_time, (zr_leftWrite_fields _ hn _).1, zr_leftSeekContract,
      zr_reindexContract, Contract.ofSegment_time, seekStartTM_contract_time]
    simp only [zr_leftFields, List.length_ofFn]
    omega
  · rw [Contract.seq_post, (zr_leftWrite_fields _ hn _).2.1, zr_leftSeekContract,
      zr_reindexContract, Contract.ofSegment_post, seekStartTM_contract_post]
    simp only [zr_leftFields, List.length_ofFn]
    generalize fieldOffset (List.ofFn fun i : Fin D.1 => (zoneCells false D.2 i.rev).reverse)
      D.1 = fo at hreach ⊢
    have key : ∀ r : ℤ, r < -(fo : ℤ) - 1 - 2 ^ D.1 ↔
        r < 2 - zoneStart (D.1 + 1) + 2 ^ D.1 := fun r => by omega
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos, seekPost_inputPos]
    · funext j r
      by_cases hj : j = 0
      · subst hj
        simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, seekPost_workTapes,
          seekPost_workTapePos, Function.update_self, true_and, h0, zero_sub, hcast, key]
        split_ifs <;> first | rfl | omega
      · simp only [Cfg.mapState_workTapes, seekPost_workTapes, hj, false_and, if_false]
    · funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self, h0,
          zero_sub]
        omega
      · simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_of_ne hj]
    · simp only [Cfg.mapState_output, seekPost_output]
  all_goals
    simp only [Contract.seq_lo, Contract.seq_hi, (zr_leftWrite_fields _ hn _).2.2,
      zr_leftSeekContract, zr_reindexContract, Contract.ofSegment_lo, Contract.ofSegment_hi,
      Contract.ofSegment_post, seekStartTM_contract_lo, seekStartTM_contract_hi,
      seekStartTM_contract_post, Cfg.mapState_workTapePos, seekPost_workTapePos,
      Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
      show (1 : Fin 2) ≠ 0 by decide, if_true, if_false, zr_leftFields, List.length_ofFn, h0]
    omega

/-- **The left pass at level one** ends at cell `-8`, the outermost cell of the new left zone
`[-8, -5]`: one cell beyond the seek's stop `-3` for the separator `-4`, then twice the
half-capacity `2`. -/
private lemma zr_leftPass_one {k : ℕ} {x : List (ZoneSym k)} (z : Fin k → ZoneContents 1) (d)
    (hp : (zr_leftPassContract x).pre ⟨1, z⟩ d) :
    ((zr_leftPassContract x).post ⟨1, z⟩ d).workTapePos 0 = -8 := by
  rw [(zr_leftPass_fields _ d hp).2.1]
  simp only [Function.update_self]
  norm_num [zoneStart_eq]

/-- On the nonpositive half-line the left pass realizes the extended zoned tape, from a start
agreeing with the original there: the mirror of `zr_rightPass_tape`'s first part.

**Proof sketch.** Compare the endpoint's interval formula with `zonedTape_extend`, using
nonpositivity to remove the absolute value; the new zone's inner half is the one nearer home.
The written interval ends strictly before home. -/
private lemma zr_leftPass_tape {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_leftPassContract x).pre D d)
    (hz : ∀ q : ℤ, q ≤ 0 → d.workTapes 0 q = zonedTape D.2 q) :
    ∀ q : ℤ, q ≤ 0 → ((zr_leftPassContract x).post D d).workTapes 0 q =
      zonedTape (fun t => (D.2 t).extend) q := by
  have hs := zoneStart_succ D.1
  have hc : zoneCapacity D.1 = 2 * 2 ^ D.1 := zoneCapacity_eq D.1
  have hcast : ((2 ^ D.1 : ℕ) : ℤ) = 2 ^ D.1 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  intro q hq
  rw [(zr_leftPass_fields D d hp).2.1, zonedTape_extend, abs_of_nonpos hq]
  simp only [true_and]
  by_cases h : 2 - (zoneStart (D.1 + 1) : ℤ) ≤ q ∧ q < 2 - zoneStart (D.1 + 1) + 2 * 2 ^ D.1
  · have h' : (zoneStart D.1 : ℤ) ≤ -q ∧ -q < zoneStart D.1 + zoneCapacity D.1 := by omega
    have he : (-q).toNat - zoneStart D.1 < 2 ^ D.1 ↔
        ¬ q < 2 - zoneStart (D.1 + 1) + 2 ^ D.1 := by omega
    rw [if_pos h, if_pos h']
    simp only [he, ite_not]
  · have h' : ¬ ((zoneStart D.1 : ℤ) ≤ -q ∧ -q < zoneStart D.1 + zoneCapacity D.1) := by
      omega
    rw [if_neg h, if_neg h', hz q hq]

/-- **The seam into the left pass**: after the right pass and the return home, the left pass's
local facts hold. The zoned head is home; on the nonpositive half-line tape `0` is the original
zoned tape (home is not a new zone's cell, `Turing.zonedTape_extend`); scratch is the ruler. -/
private lemma zr_rightLeft_link {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightReturnContract x).pre D d) :
    (zr_leftPassContract x).pre D
      (((zr_rightReturnContract x).post D d).mapState fun _ => Sum.inl SeekPhase.run) := by
  have hz := (zr_rightReturn_pre D d).mp hp
  have hs := two_le_zoneStart D.1
  rw [zr_leftPassContract, Contract.seq_pre, zr_leftSeekContract, zr_reindexContract,
    Contract.ofSegment_pre, zr_rightReturn_post D d hp]
  simp only [zr_leftPre, zr_scratchAt, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
  refine ⟨hz.2.1, fun q _ h2 => ?_, Nat.two_pow_pos D.1, fun r => ?_⟩
  · simp only [if_true]
    split_ifs with hq
    · obtain rfl : q = 0 := le_antisymm h2 hq
      rw [zonedTape_extend, if_neg (by rw [abs_zero]; omega)]
    · rfl
  · simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, zr_rulerTape, sub_zero, Nat.cast_pow,
      Nat.cast_ofNat]

/-- Offsets in a concatenated layout: up to the first layout's end they are the first's; past
it, the first's end offset plus the second's.

**Proof sketch.** Induct on the field index with `Turing.fieldOffset_succ`; the concatenation's
field is the first's or the second's. -/
private lemma zr_fieldOffset_append {Γ : Type} (L R : List (List Γ)) :
    (∀ j, j ≤ L.length → fieldOffset (L ++ R) j = fieldOffset L j) ∧
      ∀ j, j ≤ R.length →
        fieldOffset (L ++ R) (L.length + j) = fieldOffset L L.length + fieldOffset R j := by
  have h1 : ∀ j, j ≤ L.length → fieldOffset (L ++ R) j = fieldOffset L j := by
    intro j hj
    induction j with
    | zero => rw [fieldOffset_zero, fieldOffset_zero]
    | succ j ih =>
      rw [fieldOffset_succ _ j (by rw [List.length_append]; omega), fieldOffset_succ _ j (by omega),
        ih (by omega), List.getElem_append_left (by omega)]
  refine ⟨h1, fun j hj => ?_⟩
  induction j with
  | zero => rw [Nat.add_zero, fieldOffset_zero, Nat.add_zero, h1 _ le_rfl]
  | succ j ih =>
    have he : (L ++ R)[L.length + j]'(by rw [List.length_append]; omega) = R[j] := by
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
    rw [← Nat.add_assoc, fieldOffset_succ _ _ (by rw [List.length_append]; omega), ih (by omega),
      fieldOffset_succ R j (by omega), he]
    omega

/-- The whole extended layout from the outermost left cell: the left zones reversed, then the
home and the right zones. -/
private def zr_wholeFields {k : ℕ} (D : ZoneData k) : List (List (ZoneSym k)) :=
  zr_leftFields D ++ zr_rightFields D

/-- **The whole layout bridge**: from the outermost left cell `2 - zoneStart ℓ`, the zoned tape
is the whole layout, which ends at the separator past the last right zone, `zoneStart ℓ`.

**Proof sketch.** By the shared layout comparison over the concatenated fields: a left field is
a field of the left layout (`zr_zonedTape_left_fields`), a right field one of the right layout
(`zr_zonedTape_right_fields`), at the offsets of the concatenation (`zr_fieldOffset_append`);
the left layout ends at home. The end cell is blank in both. -/
private lemma zr_wholeFields_tape {k : ℕ} (D : ZoneData k) :
    fieldOffset (zr_wholeFields D) (zr_wholeFields D).length + 2 = 2 * zoneStart D.1 ∧
    ∀ p : ℤ, 0 ≤ p → p ≤ (fieldOffset (zr_wholeFields D) (zr_wholeFields D).length : ℤ) →
      zonedTape D.2 (2 - zoneStart D.1 + p) = fieldsTape (zr_wholeFields D) p := by
  have hL : (zr_leftFields D).length = D.1 := List.length_ofFn
  have hR : (zr_rightFields D).length = D.1 + 1 := by
    rw [zr_rightFields, List.length_cons, List.length_ofFn]
  have hLend : fieldOffset (zr_leftFields D) D.1 + 2 = zoneStart D.1 := by
    have h := zr_left_offset D.2 D.1 le_rfl
    rw [Nat.sub_self, show zoneStart 0 = 2 by norm_num [zoneStart_eq]] at h
    exact h
  have hRend : fieldOffset (zr_rightFields D) (D.1 + 1) = zoneStart D.1 :=
    zr_right_offset D.2 D.1 le_rfl
  have hWlen : (zr_wholeFields D).length =
      (zr_leftFields D).length + (zr_rightFields D).length := List.length_append
  have hA1 : ∀ j, j ≤ (zr_leftFields D).length →
      fieldOffset (zr_wholeFields D) j = fieldOffset (zr_leftFields D) j :=
    (zr_fieldOffset_append (zr_leftFields D) (zr_rightFields D)).1
  have hA2 : ∀ j, j ≤ (zr_rightFields D).length →
      fieldOffset (zr_wholeFields D) ((zr_leftFields D).length + j) =
        fieldOffset (zr_leftFields D) (zr_leftFields D).length +
          fieldOffset (zr_rightFields D) j :=
    (zr_fieldOffset_append (zr_leftFields D) (zr_rightFields D)).2
  have hend : fieldOffset (zr_wholeFields D) (zr_wholeFields D).length =
      zoneStart D.1 - 2 + zoneStart D.1 := by
    rw [hWlen, hA2 _ le_rfl, hL, hR, hRend]
    omega
  refine ⟨by omega, fun p hp0 hp1 => ?_⟩
  rw [hend] at hp1
  rcases lt_or_eq_of_le hp1 with hlt | heq
  · apply zr_fieldsTape_eq (zr_wholeFields D) (fun q => zonedTape D.2 (2 - zoneStart D.1 + q)) _
      p hp0 (by rw [hend]; exact hlt)
    intro j hj q hq0 hq1
    rcases lt_or_ge j (zr_leftFields D).length with hjL | hjR
    · have hfj : (zr_wholeFields D)[j]'hj = (zr_leftFields D)[j]'hjL :=
        List.getElem_append_left hjL
      rw [hfj] at hq1 ⊢
      rw [hA1 j hjL.le, ← fieldsTape_field _ j hjL q (by omega) hq1]
      have h2 : (fieldOffset (zr_leftFields D) j : ℤ) + q < fieldOffset (zr_leftFields D) D.1 := by
        have h3 := fieldOffset_succ _ j hjL
        have h4 : fieldOffset (zr_leftFields D) (j + 1) + zoneStart (D.1 - (j + 1)) =
            zoneStart D.1 := zr_left_offset D.2 (j + 1) (by omega)
        have h5 := two_le_zoneStart (D.1 - (j + 1))
        omega
      have hz : zonedTape D.2 (-(fieldOffset (zr_leftFields D) D.1 : ℤ) +
          ((fieldOffset (zr_leftFields D) j : ℤ) + q)) =
          fieldsTape (zr_leftFields D) ((fieldOffset (zr_leftFields D) j : ℤ) + q) :=
        zr_zonedTape_left_fields D.2 _ (by omega) h2
      rw [← hz]
      beta_reduce
      congr 1
      omega
    · obtain ⟨j', rfl⟩ : ∃ j', j = (zr_leftFields D).length + j' :=
        ⟨j - (zr_leftFields D).length, by omega⟩
      have hj' : j' < (zr_rightFields D).length := by omega
      have hfj : (zr_wholeFields D)[(zr_leftFields D).length + j']'hj =
          (zr_rightFields D)[j']'hj' := by
        have h := List.getElem_append_right (as := zr_leftFields D) (bs := zr_rightFields D)
          (i := (zr_leftFields D).length + j') (by omega) (h₂ := hj)
        simp only [Nat.add_sub_cancel_left] at h
        exact h
      rw [hfj] at hq1 ⊢
      rw [hA2 j' hj'.le, ← fieldsTape_field _ j' hj' q (by omega) hq1]
      have h2 : (fieldOffset (zr_rightFields D) j' : ℤ) + q ≤
          fieldOffset (zr_rightFields D) (D.1 + 1) := by
        have h3 := fieldOffset_succ _ j' hj'
        have h4 : fieldOffset (zr_rightFields D) (j' + 1) = zoneStart j' :=
          zr_right_offset D.2 j' (by omega)
        have h5 := zoneStart_mono (show j' ≤ D.1 by omega)
        omega
      have hz : zonedTape D.2 ((fieldOffset (zr_rightFields D) j' : ℤ) + q) =
          fieldsTape (zr_rightFields D) ((fieldOffset (zr_rightFields D) j' : ℤ) + q) :=
        zr_zonedTape_right_fields D.2 _ (by omega) h2
      rw [← hz]
      beta_reduce
      congr 1
      rw [hL]
      push_cast
      omega
  · have hne : zr_wholeFields D ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    have hj := length_joinFields_add_one (zr_wholeFields D) hne
    have hs := two_le_zoneStart D.1
    rw [fieldsTape_of_length_le _ (by rw [hend] at hj; omega), zonedTape_blank_outside]
    rw [abs_of_nonneg (by omega)]
    omega

/-- **The final return's precondition**: the zoned head at the outermost cell of the extended
layout, tape `0` the extended zoned tape on the extended extent, and the ruler at the scratch
head. -/
private def zr_finalPre {k : ℕ} {S : Type} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) S x) : Prop :=
  d.workTapePos 0 = 2 - zoneStart (D.1 + 1) ∧
    (∀ q : ℤ, -(zoneStart (D.1 + 1) : ℤ) ≤ q → q ≤ zoneStart (D.1 + 1) →
      d.workTapes 0 q = zonedTape (zoneExtendData D).2 q) ∧
    zr_scratchAt 0 (2 ^ D.1) d

/-- From the outermost cell, the whole extended layout is the seek-to-end row's premise. -/
private lemma zr_finalSeek_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) SeekPhase x) (hp : zr_finalPre D d) :
    (seekEndTM_contract 0 x).pre (zr_wholeFields (zoneExtendData D)) d := by
  obtain ⟨hend, hw⟩ := zr_wholeFields_tape (zoneExtendData D)
  rw [seekEndTM_contract_pre]
  refine ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), ?_, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact List.reverse_ne_nil_iff.mpr (zr_zoneCells_ne_nil false _ i.rev)
    · simp only [zr_rightFields, List.mem_cons, List.mem_ofFn] at hu
      rcases hu with rfl | ⟨i, rfl⟩
      · exact List.cons_ne_nil _ _
      · exact zr_zoneCells_ne_nil true _ i
  · intro p hp0 hp1
    have hend' : fieldOffset (zr_wholeFields (zoneExtendData D))
        (zr_wholeFields (zoneExtendData D)).length + 2 = 2 * zoneStart (D.1 + 1) := hend
    have hw' : ∀ p : ℤ, 0 ≤ p →
        p ≤ (fieldOffset (zr_wholeFields (zoneExtendData D))
          (zr_wholeFields (zoneExtendData D)).length : ℤ) →
        zonedTape (zoneExtendData D).2 (2 - zoneStart (D.1 + 1) + p) =
          fieldsTape (zr_wholeFields (zoneExtendData D)) p := hw
    rw [hp.1, hp.2.1 _ (by omega) (by omega), hw' p hp0 hp1]

/-- Seek across the whole extended layout, from its outermost left cell to the separator past
its last right zone, indexed by the original data. -/
private def zr_finalSeekContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (seekEndTM_contract 0 x) (fun D => zr_wholeFields (zoneExtendData D))
    (fun D d => zr_finalPre D d) zr_finalSeek_pre

/-- The return loop over the extended layout, carrying the ruler at the scratch head. -/
private def zr_finalLoopContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (zr_loopContract x) zoneExtendData
    (fun (D : ZoneData k) d => zr_loopPre (zoneExtendData D) d ∧ zr_scratchAt 0 (2 ^ D.1) d)
    fun _ _ hp => by
      rw [zr_loopContract, Contract.ofSegment_pre]
      exact hp.1

/-- With the ruler at the scratch head, its word is the clear row's premise. -/
private lemma zr_rulerClear_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) SweepPhase x) (hp : zr_scratchAt 0 (2 ^ D.1) d) :
    (clearTM_contract 1 x).pre (List.replicate (2 ^ D.1) (Sum.inl false)) d := by
  rw [clearTM_contract_pre]
  exact fun p _ _ => zr_scratchAt_word hp p

/-- Clear the scratch ruler. -/
private def zr_rulerClearContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (clearTM_contract 1 x)
    (fun D : ZoneData k => List.replicate (2 ^ D.1) (Sum.inl false))
    (fun (D : ZoneData k) d => zr_scratchAt 0 (2 ^ D.1) d) zr_rulerClear_pre

set_option synthInstance.maxSize 256 in
/-- Decidable equality of the return loop's phases, by cases on the phase index. -/
private def zr_decEqLoopPh : (b : Bool) → DecidableEq (zr_loopPh b)
  | false => inferInstanceAs (DecidableEq (Option Bool))
  | true => inferInstanceAs (DecidableEq (SeekPhase ⊕ (Option Bool ⊕ Option Bool)))

/-- **The final return**: seek across the whole extended layout, run the return loop home, and
clear the ruler. -/
private def zr_finalContract {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqLoopPh
  (zr_finalSeekContract x).seq
    ((zr_finalLoopContract x).seq (zr_rulerClearContract x) (fun D => D) fun D d _ hp => by
      rw [zr_finalLoopContract, zr_reindexContract, Contract.ofSegment_pre] at hp
      rw [zr_rulerClearContract, zr_reindexContract, Contract.ofSegment_pre,
        zr_finalLoopContract, zr_reindexContract, Contract.ofSegment_post, zr_loopContract,
        Contract.ofSegment_post]
      refine zr_scratchAt_move _ _ hp.2 (fun r => ?_) ?_ <;>
      simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)])
    (fun D => D) fun D d _ hp => by
      rw [zr_finalSeekContract, zr_reindexContract, Contract.ofSegment_pre] at hp
      have hend : fieldOffset (zr_wholeFields (zoneExtendData D))
          (zr_wholeFields (zoneExtendData D)).length + 2 = 2 * zoneStart (D.1 + 1) :=
        (zr_wholeFields_tape (zoneExtendData D)).1
      have he : (zoneExtendData D).1 = D.1 + 1 := rfl
      rw [Contract.seq_pre, zr_finalLoopContract, zr_reindexContract, Contract.ofSegment_pre,
        zr_finalSeekContract, zr_reindexContract, Contract.ofSegment_post,
        seekEndTM_contract_post]
      refine ⟨⟨?_, fun q h1 h2 => ?_⟩, zr_scratchAt_move _ _ hp.2.2 (fun r => ?_) ?_⟩
      · simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self, hp.1,
          he]
        omega
      · simp only [Cfg.mapState_workTapes, seekPost_workTapes]
        exact hp.2.1 q (by omega) (by rw [he] at h2; omega)
      · simp only [Cfg.mapState_workTapes, seekPost_workTapes]
      · simp only [Cfg.mapState_workTapePos, seekPost_workTapePos,
          Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
/-- **The final return's fields**: the seek across the extended layout, the loop home and the
clear take `3 · zoneStart (ℓ + 1) + 2 · 2^ℓ + 8ℓ + 19` steps; the endpoint has the zoned head at
home and scratch blank, everything else unchanged. The zoned head stays in
`[2 - zoneStart (ℓ + 1), zoneStart (ℓ + 1)]`, scratch within one cell left of its start and the
ruler's right delimiter. -/
private lemma zr_final_fields {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_finalContract x).pre D d) :
    (zr_finalContract x).time D d = 3 * zoneStart (D.1 + 1) + 2 * 2 ^ D.1 + 8 * D.1 + 19 ∧
      (zr_finalContract x).post D d =
        { d with
          state := some (Sum.inr (Sum.inr SweepPhase.done))
          workTapes := fun j q => if j = 1 then none else d.workTapes j q
          workTapePos := Function.update d.workTapePos 0 0 } ∧
      (zr_finalContract x).lo D d 0 = 2 - zoneStart (D.1 + 1) ∧
      (zr_finalContract x).hi D d 0 = zoneStart (D.1 + 1) ∧
      (zr_finalContract x).lo D d 1 = d.workTapePos 1 - 1 ∧
      (zr_finalContract x).hi D d 1 = d.workTapePos 1 + 2 ^ D.1 := by
  letI := zr_decEqLoopPh
  have hz : zr_finalPre D (d.mapState fun _ => SeekPhase.run) := by
    rw [zr_finalContract, Contract.seq_pre, zr_finalSeekContract, zr_reindexContract,
      Contract.ofSegment_pre] at hp
    exact hp
  have h0 : d.workTapePos 0 = 2 - zoneStart (D.1 + 1) := by
    simpa only [Cfg.mapState_workTapePos] using hz.1
  have hs1 : ∀ r, d.workTapes 1 r = zr_rulerTape (2 ^ D.1) (d.workTapePos 1) r := by
    intro r
    have h := hz.2.2.2 r
    simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, sub_zero] using h
  have hend : fieldOffset (zr_wholeFields (zoneExtendData D))
      (zr_wholeFields (zoneExtendData D)).length + 2 = 2 * zoneStart (D.1 + 1) :=
    (zr_wholeFields_tape (zoneExtendData D)).1
  have he : (zoneExtendData D).1 = D.1 + 1 := rfl
  have hs := two_le_zoneStart D.1
  have hs' := zoneStart_succ D.1
  have hcast : ((2 ^ D.1 : ℕ) : ℤ) = 2 ^ D.1 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hpos : (0 : ℤ) < 2 ^ D.1 := by positivity
  rw [zr_finalContract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Contract.seq_time, zr_finalSeekContract, zr_finalLoopContract,
      zr_rulerClearContract, zr_reindexContract, Contract.ofSegment_time, seekEndTM_contract_time,
      zr_loopContract, clearTM_contract_time, List.length_replicate, he]
    omega
  · simp only [Contract.seq_post, zr_finalSeekContract, zr_finalLoopContract,
      zr_rulerClearContract, zr_reindexContract, Contract.ofSegment_post,
      seekEndTM_contract_post, zr_loopContract, clearTM_contract_post]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, sweepPost_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos, sweepPost_inputPos, seekPost_inputPos]
    · funext j q
      by_cases hj : j = 1
      · subst hj
        simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, sweepPost_workTapes,
          seekPost_workTapes, seekPost_workTapePos, true_and, if_true,
          Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), List.length_replicate]
        split_ifs with hq
        · rfl
        · rw [hs1, zr_rulerTape, if_neg hq]
      · simp only [Cfg.mapState_workTapes, sweepPost_workTapes, seekPost_workTapes, hj,
          false_and, if_false]
    · funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Cfg.mapState_workTapePos, sweepPost_workTapePos, Function.update_self]
      · simp only [Cfg.mapState_workTapePos, sweepPost_workTapePos, seekPost_workTapePos,
          Function.update_of_ne hj]
    · simp only [Cfg.mapState_output, sweepPost_output, seekPost_output]
  all_goals
    simp only [Contract.seq_lo, Contract.seq_hi, zr_finalSeekContract,
      zr_finalLoopContract, zr_rulerClearContract, zr_reindexContract, Contract.ofSegment_lo,
      Contract.ofSegment_hi, Contract.ofSegment_post, seekEndTM_contract_lo,
      seekEndTM_contract_hi, seekEndTM_contract_post, zr_loopContract, clearTM_contract_lo,
      clearTM_contract_hi, Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), show (1 : Fin 2) ≠ 0 by decide,
      show (0 : Fin 2) ≠ 1 by decide, if_true, if_false, List.length_replicate, he, h0, hcast]
    omega
/-- The right pass and the return home with their nested exit normalized, for sequencing. -/
private abbrev zr_rightReturnRow {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqRP
  zr_singletonContract (zr_rightReturnContract x) (Sum.inr (Sum.inr ⟨false, some true⟩))

set_option synthInstance.maxSize 256 in
/-- Decidable equality of the right pass and return home's state type, from its parts. -/
private def zr_decEqRR : DecidableEq ((((SeekPhase ⊕ SeekPhase) ⊕ (SweepPhase ⊕ SeekPhase)) ⊕
    (SweepPhase ⊕ (((Option Bool ⊕ SeekPhase) ⊕ SeekPhase) ⊕ SweepPhase))) ⊕
      (SeekPhase ⊕ (Σ b, zr_loopPh b))) :=
  letI := zr_decEqRP
  letI := zr_decEqLoopPh
  inferInstance

/-- **The right pass, the return home and the left pass** as one contract. -/
private def zr_rightLeftContract {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqRR
  (zr_rightReturnRow x).seq (zr_leftPassContract x) (fun D => D) fun D d _ hp => by
    rw [(zr_singleton_fields _ _ _ D d).1] at hp
    rw [(zr_singleton_fields _ _ _ D d).2.2.1]
    exact zr_rightLeft_link D d hp

/-- The right pass, the return home and the left pass need exactly the original zoned input. -/
private lemma zr_rightLeft_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_rightLeftContract x).pre D d ↔ zoneRowPre D d := by
  letI := zr_decEqRR
  rw [zr_rightLeftContract, Contract.seq_pre, (zr_singleton_fields _ _ _ _ _).1,
    zr_rightReturn_pre]
  simp only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- **After the right pass, the return home and the left pass**: tape `0` is the extended zoned
tape; scratch holds the ruler `[q, q + 2^ℓ)` from its start `q`, blank elsewhere; the zoned head
is at the new left zone's outer end, everything else unchanged.

**Proof sketch.** On the nonpositive half-line the left pass's mirror statement
(`zr_leftPass_tape`); on the positive one the left pass writes nothing and the right pass's
tape is the extended one (`zr_rightReturn_post`); scratch is untouched by the left pass. -/
private lemma zr_rightLeft_post {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightLeftContract x).pre D d) :
    (zr_rightLeftContract x).post D d =
      { d with
        state := some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          SweepPhase.done))))))
        workTapes := fun j q =>
          if j = 0 then zonedTape (zoneExtendData D).2 q
          else zr_rulerTape (2 ^ D.1) (d.workTapePos 1) q
        workTapePos := Function.update d.workTapePos 0 (2 - zoneStart (D.1 + 1)) } := by
  letI := zr_decEqRR
  have hz := (zr_rightLeft_pre D d).mp hp
  have hr : (zr_rightReturnContract x).pre D
      (d.mapState fun _ => Sum.inl (Sum.inl (Sum.inl (Sum.inl SeekPhase.run)))) := by
    rw [zr_rightReturn_pre]
    simpa only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      using hz
  have hl := zr_rightLeft_link D _ hr
  have hs := zoneStart_succ D.1
  have hc : zoneCapacity D.1 = 2 * 2 ^ D.1 := zoneCapacity_eq D.1
  have hs2 := two_le_zoneStart D.1
  have hpos : (0 : ℤ) < 2 ^ D.1 := by positivity
  have hcast : ((2 ^ D.1 : ℕ) : ℤ) = 2 ^ D.1 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [zr_rightLeftContract, Contract.seq_post, (zr_singleton_fields _ _ _ _ _).2.2.1]
  have ht := zr_leftPass_tape D _ hl (fun q hq => by
    rw [Cfg.mapState_workTapes, zr_rightReturn_post D _ hr]
    simp only [if_true]
    split_ifs with h0
    · obtain rfl : q = 0 := le_antisymm hq h0
      rw [zonedTape_extend, if_neg (by rw [abs_zero]; omega)]
    · rfl)
  rw [(zr_leftPass_fields D _ hl).2.1] at ht ⊢
  apply Cfg.ext
  · simp only [Cfg.mapState_state, Option.map_some]
  · simp only [Cfg.mapState_inputPos, zr_rightReturn_post D _ hr]
  · funext j q
    by_cases hj : j = 0
    · subst hj
      show _ = if (0 : Fin 2) = 0 then zonedTape (zoneExtendData D).2 q
        else zr_rulerTape (2 ^ D.1) (d.workTapePos 1) q
      refine Eq.trans ?_ (if_pos rfl).symm
      by_cases hq : q ≤ 0
      · rw [Cfg.mapState_workTapes]
        exact ht q hq
      · have hn : ¬ (2 - (zoneStart (D.1 + 1) : ℤ) ≤ q ∧
            q < 2 - zoneStart (D.1 + 1) + 2 * 2 ^ D.1) := by omega
        have hq' : (0 : ℤ) ≤ q := by omega
        simp only [Cfg.mapState_workTapes, true_and, hn, if_false, zr_rightReturn_post D _ hr,
          if_true, hq']
        rfl
    · have hj1 : j = 1 := by omega
      subst hj1
      simp only [Cfg.mapState_workTapes, hj, false_and, if_false, zr_rightReturn_post D _ hr,
        zr_rulerTape]
      rw [Cfg.mapState_workTapePos]
      by_cases hc : d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + 2 ^ D.1
      · have hc' : d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + ((2 ^ D.1 : ℕ) : ℤ) := by
          rw [hcast]
          exact hc
        rw [if_pos hc, if_pos hc']
      · have hc' : ¬ (d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + ((2 ^ D.1 : ℕ) : ℤ)) := by
          rw [hcast]
          exact hc
        rw [if_neg hc, if_neg hc']
  · funext j
    by_cases hj : j = 0
    · subst hj
      simp only [Cfg.mapState_workTapePos, Function.update_self]
    · simp only [Cfg.mapState_workTapePos, Function.update_of_ne hj, zr_rightReturn_post D _ hr]
  · simp only [Cfg.mapState_output, zr_rightReturn_post D _ hr]
/-- The right pass, the return home and the left pass: their times add up with one seam; the
zoned head stays in `[1 - zoneStart (ℓ + 1), zoneStart (ℓ + 1)]`, scratch within two cells left
of its start and the cell past the ruler's right delimiter. -/
private lemma zr_rightLeft_fields {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightLeftContract x).pre D d) :
    (zr_rightLeftContract x).time D d = zoneStart D.1 + 10 * 2 ^ D.1 + 23 + 1 +
        (2 ^ D.1 + 2 + (zoneStart (D.1 + 1) + 8 * (D.1 + 2))) + 1 +
        (zoneStart D.1 + 8 * 2 ^ D.1 + 36) ∧
      1 - (zoneStart (D.1 + 1) : ℤ) ≤ (zr_rightLeftContract x).lo D d 0 ∧
      (zr_rightLeftContract x).hi D d 0 ≤ zoneStart (D.1 + 1) ∧
      d.workTapePos 1 - 2 ≤ (zr_rightLeftContract x).lo D d 1 ∧
      (zr_rightLeftContract x).hi D d 1 ≤ d.workTapePos 1 + 2 ^ D.1 + 1 := by
  letI := zr_decEqRR
  have hz := (zr_rightLeft_pre D d).mp hp
  have hr : (zr_rightReturnContract x).pre D
      (d.mapState fun _ => Sum.inl (Sum.inl (Sum.inl (Sum.inl SeekPhase.run)))) := by
    rw [zr_rightReturn_pre]
    simpa only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      using hz
  have hl := zr_rightLeft_link D _ hr
  have hb := zr_rightReturn_bounds D _ hr
  have hf := zr_leftPass_fields D _ hl
  have hcast : ((2 ^ D.1 : ℕ) : ℤ) = 2 ^ D.1 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hs := zoneStart_succ D.1
  have hs2 := two_le_zoneStart D.1
  simp only [Cfg.mapState_workTapePos] at hb
  rw [zr_rightLeftContract]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Contract.seq_time, (zr_singleton_fields _ _ _ _ _).2.1,
      (zr_singleton_fields _ _ _ _ _).2.2.1, hf.1, zr_rightReturn_time]
  · rw [Contract.seq_lo, ((zr_singleton_fields _ _ _ _ _).2.2.2 0).1,
      (zr_singleton_fields _ _ _ _ _).2.2.1, hf.2.2.1]
    exact le_min (by omega) le_rfl
  · rw [Contract.seq_hi, ((zr_singleton_fields _ _ _ _ _).2.2.2 0).2,
      (zr_singleton_fields _ _ _ _ _).2.2.1, hf.2.2.2.1]
    exact max_le hb.2.1 (by omega)
  · rw [Contract.seq_lo, ((zr_singleton_fields _ _ _ _ _).2.2.2 1).1,
      (zr_singleton_fields _ _ _ _ _).2.2.1, hf.2.2.2.2.1]
    simp only [Cfg.mapState_workTapePos, zr_rightReturn_post D _ hr]
    exact le_min (by omega) le_rfl
  · rw [Contract.seq_hi, ((zr_singleton_fields _ _ _ _ _).2.2.2 1).2,
      (zr_singleton_fields _ _ _ _ _).2.2.1, hf.2.2.2.2.2]
    simp only [Cfg.mapState_workTapePos, zr_rightReturn_post D _ hr]
    exact max_le (by omega) le_rfl

/-- The right pass, the return home and the left pass with their nested exit normalized. -/
private abbrev zr_rightLeftRow {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqRR
  zr_singletonContract (zr_rightLeftContract x)
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr SweepPhase.done))))))

set_option synthInstance.maxSize 512 in
/-- Decidable equality of the right pass, the return home and the left pass's state type, from
its parts. -/
private def zr_decEqRL : DecidableEq (((((SeekPhase ⊕ SeekPhase) ⊕ (SweepPhase ⊕ SeekPhase)) ⊕
    (SweepPhase ⊕ (((Option Bool ⊕ SeekPhase) ⊕ SeekPhase) ⊕ SweepPhase))) ⊕
      (SeekPhase ⊕ (Σ b, zr_loopPh b))) ⊕
    (SeekPhase ⊕ (Option Bool ⊕ ((SeekPhase ⊕ ((Option Bool ⊕ Option Bool) ⊕
      ((Option Bool ⊕ SeekPhase) ⊕ (Option Bool ⊕ Option Bool)))) ⊕ (SweepPhase ⊕
        ((SeekPhase ⊕ ((Option Bool ⊕ Option Bool) ⊕
          ((Option Bool ⊕ SeekPhase) ⊕ (Option Bool ⊕ Option Bool)))) ⊕ SweepPhase)))))) :=
  letI := zr_decEqRR
  letI := zr_decEqLM
  inferInstance

/-- **The seam into the final return**: after the right pass, the return home and the left pass,
the final return's precondition holds — the zoned head at the extended layout's outermost cell,
tape `0` the extended zoned tape (`zr_rightLeft_post`), the ruler at the scratch head. -/
private lemma zr_rightLeftFinal_link {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_rightLeftContract x).pre D d) :
    (zr_finalContract x).pre D
      (((zr_rightLeftContract x).post D d).mapState fun _ => Sum.inl SeekPhase.run) := by
  letI := zr_decEqLoopPh
  rw [zr_finalContract, Contract.seq_pre, zr_finalSeekContract, zr_reindexContract,
    Contract.ofSegment_pre, zr_rightLeft_post D d hp]
  rw [zr_finalPre, zr_scratchAt]
  refine ⟨?_, fun q _ _ => ?_, Nat.two_pow_pos D.1, fun r => ?_⟩
  · simp only [Cfg.mapState_workTapePos, Function.update_self]
  · simp only [Cfg.mapState_workTapes, if_true]
  · simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), show (1 : Fin 2) ≠ 0 by decide,
      if_false, sub_zero]

/-- **The extension machine's run**: the right pass, the return home, the left pass and the
final return, as one contract. -/
private def zr_extendContract {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqRL
  (zr_rightLeftRow x).seq (zr_finalContract x) (fun D => D) fun D d _ hp => by
    rw [(zr_singleton_fields _ _ _ D d).1] at hp
    rw [(zr_singleton_fields _ _ _ D d).2.2.1]
    exact zr_rightLeftFinal_link D d hp

/-- The extension machine's run needs exactly the original zoned input. -/
private lemma zr_extend_pre {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d) :
    (zr_extendContract x).pre D d ↔ zoneRowPre D d := by
  letI := zr_decEqRL
  rw [zr_extendContract, Contract.seq_pre, (zr_singleton_fields _ _ _ _ _).1, zr_rightLeft_pre]
  simp only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- **The extension machine's run, characterized**: its time is the right part's, one seam and
the final return's; its endpoint is the extension row's (`Turing.zoneExtendPost`); the zoned head
stays within `zoneStart (ℓ + 1)` of home, scratch within two cells left of its start and the cell
past the ruler's right delimiter.

**Proof sketch.** Substitute the right part's endpoint (`zr_rightLeft_post`) into the final
return's (`zr_final_fields`): the zoned head ends at home, scratch is blank again, tape `0` is
the extended zoned tape. The envelopes are the hull of the two parts'. -/
private lemma zr_extend_fields {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_extendContract x).pre D d) :
    (zr_extendContract x).time D d = zoneStart D.1 + 10 * 2 ^ D.1 + 23 + 1 +
        (2 ^ D.1 + 2 + (zoneStart (D.1 + 1) + 8 * (D.1 + 2))) + 1 +
        (zoneStart D.1 + 8 * 2 ^ D.1 + 36) + 1 +
        (3 * zoneStart (D.1 + 1) + 2 * 2 ^ D.1 + 8 * D.1 + 19) ∧
      (zr_extendContract x).post D d =
        zoneExtendPost (Sum.inr (Sum.inr (Sum.inr SweepPhase.done))) D d ∧
      -(zoneStart (D.1 + 1) : ℤ) ≤ (zr_extendContract x).lo D d 0 ∧
      (zr_extendContract x).hi D d 0 ≤ zoneStart (D.1 + 1) ∧
      d.workTapePos 1 - 2 ≤ (zr_extendContract x).lo D d 1 ∧
      (zr_extendContract x).hi D d 1 ≤ d.workTapePos 1 + 2 ^ D.1 + 1 := by
  letI := zr_decEqRL
  have hz := (zr_extend_pre D d).mp hp
  have hr : (zr_rightLeftContract x).pre D (d.mapState fun _ =>
      Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl SeekPhase.run))))) := by
    rw [zr_rightLeft_pre]
    simpa only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      using hz
  have hl := zr_rightLeftFinal_link D _ hr
  have hb := zr_rightLeft_fields D _ hr
  have hf := zr_final_fields D _ hl
  simp only [Cfg.mapState_workTapePos] at hb
  rw [zr_extendContract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Contract.seq_time, (zr_singleton_fields _ _ _ _ _).2.1,
      (zr_singleton_fields _ _ _ _ _).2.2.1, hf.1, hb.1]
  · rw [Contract.seq_post, (zr_singleton_fields _ _ _ _ _).2.2.1, hf.2.1, zoneExtendPost]
    rw [zr_rightLeft_post D _ hr]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos]
    · funext j q
      by_cases hj : j = 1
      · subst hj
        simp only [Cfg.mapState_workTapes, if_true, show (1 : Fin 2) ≠ 0 by decide, if_false,
          hz.2.2]
      · simp only [Cfg.mapState_workTapes, hj, if_false]
        have hj0 : j = 0 := by omega
        subst hj0
        simp only [if_true]
    · funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Cfg.mapState_workTapePos, Function.update_self, hz.2.1]
      · simp only [Cfg.mapState_workTapePos, Function.update_of_ne hj]
    · simp only [Cfg.mapState_output]
  all_goals
    simp only [Contract.seq_lo, Contract.seq_hi, ((zr_singleton_fields _ _ _ _ _).2.2.2 _).1,
      ((zr_singleton_fields _ _ _ _ _).2.2.2 _).2, (zr_singleton_fields _ _ _ _ _).2.2.1,
      hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2]
    try simp only [Cfg.mapState_workTapePos, zr_rightLeft_post D _ hr,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    omega

/-- The extension machine's time is at most `135 · (2^ℓ + 1)`. -/
private lemma zr_extend_time_le {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k) (d)
    (hp : (zr_extendContract x).pre D d) :
    (zr_extendContract x).time D d ≤ 135 * (2 ^ D.1 + 1) := by
  have h := zr_extent_cost D.1
  have hm := zoneStart_mono (Nat.le_add_right D.1 1)
  have hl : D.1 < 2 ^ D.1 := Nat.lt_two_pow_self
  rw [(zr_extend_fields D d hp).1]
  omega

/-- The machine of a contract, read off its type. -/
private abbrev zr_machineOf {n : ℕ} {Γ S I : Type} {x : List Γ} {M : MultiTapeTM n Γ S}
    {entry : S} {X : Set (Option S)} (_ : Contract M entry X I x) : MultiTapeTM n Γ S :=
  M

/-- The entry state of a contract, read off its type. -/
private abbrev zr_entryOf {n : ℕ} {Γ S I : Type} {x : List Γ} {M : MultiTapeTM n Γ S}
    {entry : S} {X : Set (Option S)} (_ : Contract M entry X I x) : S :=
  entry

set_option synthInstance.maxSize 256 in
/-- The return loop's phases are finite, by cases on the phase index. -/
private def zr_fintypeLoopPh : (b : Bool) → Fintype (zr_loopPh b)
  | false => inferInstanceAs (Fintype (Option Bool))
  | true => inferInstanceAs (Fintype (SeekPhase ⊕ (Option Bool ⊕ Option Bool)))
/-- The rebalance scan's slot test: `true` on a blank cell or on a cell whose track-`t` slot is
`⊠`. At a zone's innermost cell it detects an empty zone (`zr_inner_empty_iff`). -/
private def zr_slotEmpty {k : ℕ} (t : Fin k) : Option (ZoneSym k) → Bool
  | some c => (zoneSlotOf t c).isNone
  | none => true

/-- The one-cell leaf's verdict set is the pair of its verdicts. -/
private lemma zr_verdicts_pair :
    (Set.range fun b : Bool => some (some b) : Set (Option (Option Bool))) =
      {some (some true), some (some false)} := by
  ext q
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, rfl⟩
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩

/-- The word `w` lies at the zoned head, followed by a blank: the skip row's premise. -/
private def zr_wordAt {k : ℕ} {S : Type} {x : List (ZoneSym k)} (w : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) S x) : Prop :=
  ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p

/-- A stationary test of the zoned cell, with its two verdicts as exits, indexed by the word at
the zoned head. -/
private def zr_wordTestContract {k : ℕ} (choose : Option (ZoneSym k) → Bool)
    (x : List (ZoneSym k)) :=
  zr_reindexContract (zr_exitsContract (zr_cellContract 0 choose none 0 x) _ zr_verdicts_pair)
    (fun _ => ()) (fun w d => zr_wordAt w d) fun _ _ _ => trivial

/-- A stationary test keeps the word at the zoned head. -/
private lemma zr_wordTest_wordAt {k : ℕ} {S : Type} {x : List (ZoneSym k)}
    (choose : Option (ZoneSym k) → Bool) (w : List (ZoneSym k))
    (d : Cfg 2 (ZoneSym k) (Option Bool) x) (hp : zr_wordAt w d) (f : Option Bool → S) :
    zr_wordAt w (((zr_wordTestContract choose x).post w d).mapState f) := by
  intro p h0 h1
  simp only [zr_wordTestContract, zr_reindexContract, zr_exitsContract, Contract.ofSegment_post,
    zr_cellContract, zr_cellPost, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
    SignType.coe_zero, add_zero, Function.update_eq_self]
  exact hp p h0 h1

/-- The scan's inner branch: on an empty track-`t` slot, skip the zone; otherwise stop. -/
private def zr_slotBranchContract {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  Contract.branch (by decide : (some true : Option Bool) ≠ some false)
    (zr_wordTestContract (zr_slotEmpty t) x) (skipTM_contract 0 x) (zr_anchorContract x)
    (fun w => w) (fun _ => ())
    (fun w d _ hp _ => by
      rw [zr_wordTestContract, zr_reindexContract, Contract.ofSegment_pre] at hp
      rw [skipTM_contract_pre]
      exact zr_wordTest_wordAt _ w d hp _)
    (fun _ _ _ _ _ => by
      rw [zr_anchorContract, Contract.ofSegment_pre]
      trivial)

/-- The scan's outer branch: on a blank cell, stop; otherwise test the slot. -/
private def zr_blankBranchContract {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  Contract.branch (by decide : (some true : Option Bool) ≠ some false)
    (zr_wordTestContract Option.isNone x) (zr_anchorContract x) (zr_slotBranchContract t x)
    (fun _ => ()) (fun w => w)
    (fun _ _ _ _ _ => by
      rw [zr_anchorContract, Contract.ofSegment_pre]
      trivial)
    (fun w d _ hp _ => by
      rw [zr_wordTestContract, zr_reindexContract, Contract.ofSegment_pre] at hp
      rw [zr_slotBranchContract, Contract.branch_pre, zr_wordTestContract, zr_reindexContract,
        Contract.ofSegment_pre]
      have h := zr_wordTest_wordAt Option.isNone w d hp (fun _ => (none : Option Bool))
      intro p h0 h1
      simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using h p h0 h1)

/-- **The scan's body**: mark one scratch cell, then stop on a blank zoned cell, stop on a
nonempty track-`t` slot, or skip the zone. -/
private def zr_scanBodyContract {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  (zr_stepContract 1 1 x (fun w d => zr_wordAt w d) (some (some (Sum.inl true)))).seq
    (zr_blankBranchContract t x) (fun w => w) fun w d _ hp => by
      rw [zr_stepContract, Contract.ofSegment_pre] at hp
      rw [zr_blankBranchContract, Contract.branch_pre, zr_wordTestContract, zr_reindexContract,
        Contract.ofSegment_pre]
      intro p h0 h1
      simp only [zr_stepContract, Contract.ofSegment_post, zr_cellContract, zr_cellPost,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      exact hp p h0 h1
/-- The scan body's endpoint after its mark: scratch's cell marked and its head one cell right. -/
private abbrev zr_scanMarked {k : ℕ} {S : Type} {x : List (ZoneSym k)}
    (d : Cfg 2 (ZoneSym k) S x) (s : S) (p0 : ℤ) : Cfg 2 (ZoneSym k) S x :=
  { d with
    state := some s
    workTapes := Function.update d.workTapes 1
      (Function.update (d.workTapes 1) (d.workTapePos 1) (some (Sum.inl true)))
    workTapePos := fun j => if j = 0 then p0 else d.workTapePos 1 + 1 }

/-- **The scan body's fields**, by the zoned cell: on a blank cell it stops at its first exit
after 4 steps; on a nonempty track-`t` slot at its third exit after 6; on an empty slot it skips
the zone `w` and stops at its second exit after `|w| + 7`. Each time it has marked scratch's
cell and moved scratch one cell right; tape `0` is unchanged. -/
private lemma zr_scanBody_fields {k : ℕ} {x : List (ZoneSym k)} (t : Fin k)
    (w : List (ZoneSym k)) (d) (hp : (zr_scanBodyContract t x).pre w d) :
    (zr_scanBodyContract t x).time w d =
        (if (d.workTapes 0 (d.workTapePos 0)).isNone then 4
          else if zr_slotEmpty t (d.workTapes 0 (d.workTapePos 0)) then w.length + 7 else 6) ∧
      (zr_scanBodyContract t x).post w d =
        zr_scanMarked d
          (if (d.workTapes 0 (d.workTapePos 0)).isNone then
            Sum.inr (Sum.inl (Sum.inr (some false)))
          else if zr_slotEmpty t (d.workTapes 0 (d.workTapePos 0)) then
            Sum.inr (Sum.inr (Sum.inl (Sum.inr SeekPhase.done)))
          else Sum.inr (Sum.inr (Sum.inr (some false))))
          (if ¬ (d.workTapes 0 (d.workTapePos 0)).isNone ∧
              zr_slotEmpty t (d.workTapes 0 (d.workTapePos 0)) then
            d.workTapePos 0 + w.length + 1
          else d.workTapePos 0) := by
  have hw : zr_wordAt w (d.mapState fun _ => (none : Option Bool)) := by
    rw [zr_scanBodyContract, Contract.seq_pre, zr_stepContract, Contract.ofSegment_pre] at hp
    exact hp
  generalize hc : d.workTapes 0 (d.workTapePos 0) = c
  cases h1 : c.isNone <;> cases h2 : zr_slotEmpty t c <;>
  simp only [zr_scanBodyContract, Contract.seq_time, Contract.seq_post, zr_stepContract,
    Contract.ofSegment_time, Contract.ofSegment_post, zr_cellContract, zr_cellPost,
    zr_blankBranchContract, Contract.branch_time, Contract.branch_post, zr_wordTestContract,
    zr_reindexContract, zr_exitsContract, zr_slotBranchContract, zr_anchorContract,
    skipTM_contract_time, skipTM_contract_post, Cfg.mapState_workTapes, Cfg.mapState_inputPos,
    Cfg.mapState_output, Cfg.workTapeSymbols_eq, Cfg.mapState_workTapePos, Function.update_of_ne
      (by decide : (0 : Fin 2) ≠ 1), SignType.coe_zero, add_zero, Function.update_eq_self, hc,
    h1, h2, Option.some.injEq, Bool.false_eq_true, if_true, if_false, not_true_eq_false,
    not_false_eq_true, true_and, and_true, false_and]
  all_goals first | refine ⟨by omega, ?_⟩ | skip
  all_goals
    apply Cfg.ext
    · simp only [Cfg.mapState_state, seekPost_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos, seekPost_inputPos]
    · funext j q
      simp only [Cfg.mapState_workTapes, seekPost_workTapes]
      by_cases hj : j = 1
      · subst j
        simp only [Function.update_self, Function.update_apply, Cfg.mapState_workTapes]
      · simp only [Function.update_of_ne hj, Cfg.mapState_workTapes]
    · funext j
      simp only [Cfg.mapState_workTapePos, seekPost_workTapePos]
      by_cases hj : j = 0
      · subst j
        simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
          Cfg.mapState_workTapePos, if_true]
      · have hj1 : j = 1 := by omega
        subst j
        simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
          Cfg.mapState_workTapePos, SignType.coe_one, if_neg hj]
    · simp only [Cfg.mapState_output, seekPost_output]

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

**Implementation status.** The slot guards, scan-index facts, short identity, tape mirror,
and one-cell leaf are proved. The pure cascade has a checked side-pass reordering valid for
every guard and without a fullness assumption. The scan with both exits, guarded column-move
machines, machine passes, home move, and cleanup remain open. Only this target's body is
admitted. -/
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

**Implementation.** Four contracts composed through stationary seams, from the catalog rows
(`seekEndTM`, `seekStartTM`, `skipTM`, `skipBackTM`, the mapped copy, `walkTM`, `clearTM`), the
one-cell leaf and the phase host. *Right pass:* seek the right end; copy the last field (the last
zone, or the home at level zero, both of the new half-capacity `2^ℓ`) to scratch as a ruler;
write the new right zone's two halves, an adjusted walk by the ruler between them. *Return
home:* skip the outer half, then a phase-host loop whose round skips back over one field and
tests for the home, the only one-cell field. *Left pass:* seek the left layout's outermost cell,
step across the separator, and make two left moves by the ruler (skip the ruler on scratch, step
back onto its last cell, walk left over it, step back), writing the inner half after the first
and the outer half after the second. *Final return:* seek across the whole extended layout, run
the loop home, clear the ruler. The time is at most `135 · (2^ℓ + 1)`. -/
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
  refine ⟨135, _, ?_, ?_, zr_machineOf (zr_extendContract ([] : List (ZoneSym k))),
    zr_entryOf (zr_extendContract ([] : List (ZoneSym k))),
    Sum.inr (Sum.inr (Sum.inr SweepPhase.done)), fun x => ⟨Contract.ofSegment zoneRowPre
      (fun D d => (zr_extendContract x).time D d)
      (zoneExtendPost (Sum.inr (Sum.inr (Sum.inr SweepPhase.done))))
      (zoneRowLo (fun D => D.1) 135) (zoneRowHi (fun D => D.1) 135) (fun D d hd hp => ?_)
      (fun D d _ _ => ?_), ?_, ?_, ?_, ?_, ?_⟩⟩
  · letI := zr_fintypeLoopPh
    set_option synthInstance.maxSize 1024 in exact inferInstance
  · letI := zr_decEqRL
    letI := zr_decEqLoopPh
    exact inferInstance
  · have hp' := (zr_extend_pre D d).mpr hp
    obtain ⟨-, hpost, h0l, h0h, h1l, h1h⟩ := zr_extend_fields D d hp'
    have hseg := (zr_extendContract x).segment D d hd hp'
    rw [hpost] at hseg
    refine hseg.mono (by simp only [Set.image_singleton, Option.map_some]; exact le_rfl)
      fun p hb => ?_
    have hpos : (0 : ℤ) < 2 ^ D.1 := by positivity
    rw [headBox_iff] at hb ⊢
    intro j
    have h := Finset.mem_Icc.mp (hb j)
    rw [Finset.mem_Icc]
    simp only [zoneRowLo, zoneRowHi]
    by_cases hj : j = 0
    · subst hj
      simp only [if_true]
      omega
    · have hj1 : j = 1 := by omega
      subst hj1
      simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
      push_cast
      omega
  · simp only [zoneExtendPost, Set.mem_singleton_iff]
  · funext D d
    rw [Contract.ofSegment_pre]
  · funext D d
    rw [Contract.ofSegment_post]
  · funext D d j
    rw [Contract.ofSegment_lo]
  · funext D d j
    rw [Contract.ofSegment_hi]
  · intro D d _ hp
    rw [Contract.ofSegment_pre] at hp
    rw [Contract.ofSegment_time]
    exact zr_extend_time_le D d ((zr_extend_pre D d).mpr hp)

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
