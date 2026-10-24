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
      exact hPC _ ((headBox_iff _ _ _).mpr fun j => C.env i c₁ hc₁ hp v (by omega) j)

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
    rw [zr_bodyPhaseContract, zr_hostBodyContract, Contract.inPhase_pre, zr_bodyContract,
      Contract.seq_pre, skipBackTM_contract_pre]
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
    have h0 := (headBox_iff _ _ _).mp hb 0
    have h1 := (headBox_iff _ _ _).mp hb 1
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
private lemma zr_rulerClear_pre {k : ℕ} {x : List (ZoneSym k)} (n : ℕ)
    (d : Cfg 2 (ZoneSym k) SweepPhase x) (hp : zr_scratchAt 0 n d) :
    (clearTM_contract 1 x).pre (List.replicate n (Sum.inl false)) d := by
  rw [clearTM_contract_pre]
  exact fun p _ _ => zr_scratchAt_word hp p

/-- Clear the scratch ruler, of length `len j` at the index `j`. -/
private def zr_rulerClearContract {k : ℕ} {J : Type} (len : J → ℕ) (x : List (ZoneSym k)) :=
  zr_reindexContract (clearTM_contract 1 x) (fun j => List.replicate (len j) (Sum.inl false))
    (fun j d => zr_scratchAt 0 (len j) d) fun j => zr_rulerClear_pre (len j)

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
    ((zr_finalLoopContract x).seq (zr_rulerClearContract (fun D : ZoneData k => 2 ^ D.1) x)
      (fun D => D) fun D d _ hp => by
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
    (fun _ => ()) (fun w d => zr_wordAt w d) fun _ _ _ => by
      rw [zr_exitsContract, Contract.ofSegment_pre]
      trivial

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
  (zr_stepContract 1 1 x (fun w d => zr_wordAt w d) (some (some (Sum.inl false)))).seq
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
      (Function.update (d.workTapes 1) (d.workTapePos 1) (some (Sum.inl false)))
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

/-- The scan body's states: the mark's, then the blank test's, the anchor's, the slot test's,
the skip's and the anchor's again. -/
private abbrev zr_scanSt : Type :=
  Option Bool ⊕ (Option Bool ⊕ Option Bool) ⊕ (Option Bool ⊕ SeekPhase) ⊕ Option Bool

/-- The scan's way back: the body's blank exit to the short escape `some true`, its skip to the
anchor, and its occupied-slot exit to the found escape `none`. -/
private def zr_scanBack : zr_scanSt → Option (Option Bool)
  | .inr (.inl (.inr (some false))) => some (some true)
  | .inr (.inr (.inl (.inr .done))) => some (some false)
  | .inr (.inr (.inr (some false))) => some none
  | _ => none

/-- **The rebalance scan**: the loop host over the scan body. -/
private abbrev zr_scanTM {k : ℕ} (t : Fin k) :
    MultiTapeTM 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) :=
  zr_hostTM (zr_machineOf (zr_scanBodyContract t ([] : List (ZoneSym k)))) (Sum.inl none)
    zr_scanBack

/-- The scan body with its three exits listed. -/
private def zr_scanBodyRow {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_exitsContract (zr_scanBodyContract t x)
    {some (.inr (.inl (.inr (some false)))), some (.inr (.inr (.inl (.inr .done)))),
      some (.inr (.inr (.inr (some false))))}
    (by
      simp only [Set.image_singleton, Set.image_insert_eq, Option.map_some, Function.comp_apply,
        Set.singleton_union])

/-- The scan body inside the scan host: each of its three exits is redirected to the anchor
phase. -/
private def zr_scanPhaseContract {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_hostBodyContract zr_scanBack (zr_scanBodyRow t x)
    (fun h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq, or_self] at h)
    (fun s => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq]
      constructor
      · rintro (rfl | rfl | rfl) <;> exact Option.some_ne_none _
      · intro h
        match s, h with
        | .inr (.inl (.inr (some false))), _ => exact Or.inl rfl
        | .inr (.inr (.inl (.inr .done))), _ => exact Or.inr (Or.inl rfl)
        | .inr (.inr (.inr (some false))), _ => exact Or.inr (Or.inr rfl)
        | .inl _, h => exact absurd rfl h
        | .inr (.inl (.inl _)), h => exact absurd rfl h
        | .inr (.inl (.inr none)), h => exact absurd rfl h
        | .inr (.inl (.inr (some true))), h => exact absurd rfl h
        | .inr (.inr (.inl (.inl _))), h => exact absurd rfl h
        | .inr (.inr (.inl (.inr .run))), h => exact absurd rfl h
        | .inr (.inr (.inr none)), h => exact absurd rfl h
        | .inr (.inr (.inr (some true))), h => exact absurd rfl h)

/-- The scan body's zoned head stays between its start and one past the skipped zone's right
delimiter; the scratch head between its start and the next cell. -/
private lemma zr_scanBody_bounds {k : ℕ} {x : List (ZoneSym k)} (t : Fin k)
    (w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) zr_scanSt x) :
    d.workTapePos 0 ≤ (zr_scanBodyContract t x).lo w d 0 ∧
      (zr_scanBodyContract t x).hi w d 0 ≤ d.workTapePos 0 + w.length + 1 ∧
      d.workTapePos 1 ≤ (zr_scanBodyContract t x).lo w d 1 ∧
      (zr_scanBodyContract t x).hi w d 1 ≤ d.workTapePos 1 + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [zr_scanBodyContract, Contract.seq_lo, Contract.seq_hi, zr_stepContract,
    Contract.ofSegment_lo, Contract.ofSegment_hi, Contract.ofSegment_post, zr_cellContract,
    zr_cellPost, zr_blankBranchContract, Contract.branch_lo, Contract.branch_hi,
    zr_wordTestContract, zr_reindexContract, zr_exitsContract, zr_slotBranchContract,
    zr_anchorContract, skipTM_contract_lo, skipTM_contract_hi, Cfg.mapState_workTapePos,
    Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    SignType.coe_zero, SignType.coe_one, add_zero, Function.update_eq_self, if_true,
    show (1 : Fin 2) ≠ 0 by decide, if_false, min_self, max_self] <;>
  split_ifs <;> omega

/-- **One round of the scan**: from the anchor, with the word `w` at the zoned head, the scan
dispatches, marks scratch's cell and moves scratch right, then stops at the short escape on a
blank cell after 6 steps, at the found escape on an occupied track-`t` slot after 8, or skips
`w` and stops at the anchor after `|w| + 9`. Strictly in between it is live and off all three;
the zoned head stays between its start and one past `w`'s delimiter, scratch within one cell.

**Proof sketch.** The dispatch step and the body's phase contract make a round
(`zr_round_of_body`); the body's fields give its endpoint and time, its bounds the head
relation. -/
private lemma zr_scan_round {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (w : List (ZoneSym k))
    (c : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) x)
    (hc : c.state = some ⟨false, some false⟩) (hw : zr_wordAt w c) (P : (Fin 2 → ℤ) → Prop)
    (hP : ∀ p : Fin 2 → ℤ, c.workTapePos 0 ≤ p 0 → p 0 ≤ c.workTapePos 0 + w.length + 1 →
      c.workTapePos 1 ≤ p 1 → p 1 ≤ c.workTapePos 1 + 1 → P p) :
    Round (zr_scanTM t) ⟨false, some false⟩ {some ⟨false, some true⟩, some ⟨false, none⟩} P c
      (zr_scanMarked c
        ⟨false, if (c.workTapes 0 (c.workTapePos 0)).isNone then some true
          else if zr_slotEmpty t (c.workTapes 0 (c.workTapePos 0)) then some false else none⟩
        (if ¬ (c.workTapes 0 (c.workTapePos 0)).isNone ∧
            zr_slotEmpty t (c.workTapes 0 (c.workTapePos 0)) then
          c.workTapePos 0 + w.length + 1
        else c.workTapePos 0))
      (if (c.workTapes 0 (c.workTapePos 0)).isNone then 6
        else if zr_slotEmpty t (c.workTapes 0 (c.workTapePos 0)) then w.length + 9 else 8) := by
  have hrun1 := zr_host_dispatch_run (zr_machineOf (zr_scanBodyContract t ([] : List (ZoneSym k))))
    (Sum.inl none) zr_scanBack c hc
  set c₁ : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) x :=
    { c with state := some ⟨true, Sum.inl none⟩ } with hc₁
  have hc₁s : c₁.state = some ⟨true, Sum.inl none⟩ := rfl
  set e : Cfg 2 (ZoneSym k) zr_scanSt x := c₁.mapState fun _ => Sum.inl none with he
  have hwt : e.workTapes = c.workTapes :=
    funext fun j => funext fun q => Cfg.mapState_workTapes _ c₁ j q
  have hwp : e.workTapePos = c.workTapePos := funext fun j => Cfg.mapState_workTapePos _ c₁ j
  have hp' : (zr_scanBodyContract t x).pre w e := by
    rw [zr_scanBodyContract, Contract.seq_pre, zr_stepContract, Contract.ofSegment_pre]
    intro p h0 h1
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hwt, hwp]
    exact hw p h0 h1
  obtain ⟨hT, hpost⟩ := zr_scanBody_fields t w e hp'
  rw [hwt, hwp] at hT hpost
  generalize hcell : c.workTapes 0 (c.workTapePos 0) = cell at hT hpost ⊢
  set S : zr_scanSt := if cell.isNone then Sum.inr (Sum.inl (Sum.inr (some false)))
    else if zr_slotEmpty t cell then Sum.inr (Sum.inr (Sum.inl (Sum.inr SeekPhase.done)))
    else Sum.inr (Sum.inr (Sum.inr (some false))) with hS
  set V : Option Bool := if cell.isNone then some true
    else if zr_slotEmpty t cell then some false else none with hV
  set P0 : ℤ := if ¬ cell.isNone ∧ zr_slotEmpty t cell then c.workTapePos 0 + w.length + 1
    else c.workTapePos 0 with hP0
  have hSV : zr_scanBack S = some V := by
    rw [hS, hV]
    split_ifs <;> rfl
  have hB0 : (zr_scanPhaseContract t x).pre w c₁ := by
    rw [zr_scanPhaseContract, zr_hostBodyContract, Contract.inPhase_pre, zr_scanBodyRow,
      zr_exitsContract, Contract.ofSegment_pre]
    exact hp'
  have hBt : (zr_scanPhaseContract t x).time w c₁ = (zr_scanBodyContract t x).time w e + 1 := by
    rw [zr_scanPhaseContract, zr_hostBodyContract, Contract.inPhase_time, zr_scanBodyRow,
      zr_exitsContract, Contract.ofSegment_time]
  have hBpost : (zr_scanPhaseContract t x).post w c₁ = zr_scanMarked c ⟨false, V⟩ P0 := by
    rw [zr_scanPhaseContract, zr_hostBodyContract, Contract.inPhase_post, zr_scanBodyRow,
      zr_exitsContract, Contract.ofSegment_post, hpost]
    refine zr_bindState_eq _ _ _ ?_ (Cfg.mapState_inputPos (fun _ => (Sum.inl none : zr_scanSt)) c₁)
      ?_ ?_ (Cfg.mapState_output (fun _ => (Sum.inl none : zr_scanSt)) c₁)
    · show (zr_scanBack S).map (fun v => (⟨false, v⟩ : Σ b, zr_hostPh zr_scanSt b)) = _
      rw [hSV, Option.map_some]
    · show Function.update e.workTapes 1
          (Function.update (e.workTapes 1) (e.workTapePos 1) (some (Sum.inl false))) =
        Function.update c.workTapes 1
          (Function.update (c.workTapes 1) (c.workTapePos 1) (some (Sum.inl false)))
      rw [hwt, hwp]
    · show (fun j : Fin 2 => if j = 0 then P0 else e.workTapePos 1 + 1) =
        fun j => if j = 0 then P0 else c.workTapePos 1 + 1
      rw [hwp]
  have hmem : ∀ s : zr_scanSt, some s ∈ ({some (.inr (.inl (.inr (some false)))),
      some (.inr (.inr (.inl (.inr .done)))), some (.inr (.inr (.inr (some false))))} :
        Set (Option zr_scanSt)) →
      zr_hostRed (Sum.inl none) zr_scanBack true s ∈
        {q | ∃ s, some s ∈ ({some (.inr (.inl (.inr (some false)))),
          some (.inr (.inr (.inl (.inr .done)))), some (.inr (.inr (.inr (some false))))} :
            Set (Option zr_scanSt)) ∧ q = zr_hostRed (Sum.inl none) zr_scanBack true s} :=
    fun s hs => ⟨s, hs, rfl⟩
  have hend : ((zr_scanPhaseContract t x).post w c₁).state ∈
      (insert (some ⟨false, some false⟩) {some ⟨false, some true⟩, some ⟨false, none⟩} :
        Set (Option (Σ b, zr_hostPh zr_scanSt b))) := by
    rw [hBpost]
    show some (⟨false, V⟩ : Σ b, zr_hostPh zr_scanSt b) ∈ _
    rw [hV]
    split_ifs
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have hPC : ∀ p, HeadBox ((zr_scanPhaseContract t x).lo w c₁)
      ((zr_scanPhaseContract t x).hi w c₁) p → P p := by
    intro p hb
    have hlo : ∀ j, (zr_scanPhaseContract t x).lo w c₁ j = (zr_scanBodyContract t x).lo w e j :=
      fun j => by
        rw [zr_scanPhaseContract, zr_hostBodyContract, Contract.inPhase_lo, zr_scanBodyRow,
          zr_exitsContract, Contract.ofSegment_lo]
    have hhi : ∀ j, (zr_scanPhaseContract t x).hi w c₁ j = (zr_scanBodyContract t x).hi w e j :=
      fun j => by
        rw [zr_scanPhaseContract, zr_hostBodyContract, Contract.inPhase_hi, zr_scanBodyRow,
          zr_exitsContract, Contract.ofSegment_hi]
    obtain ⟨b₁, b₂, b₃, b₄⟩ := zr_scanBody_bounds t w e
    rw [hwp] at b₁ b₂ b₃ b₄
    have h0 := (headBox_iff _ _ _).mp hb 0
    have h1 := (headBox_iff _ _ _).mp hb 1
    rw [hlo, hhi, Finset.mem_Icc] at h0 h1
    exact hP p (b₁.trans h0.1) (h0.2.trans b₂) (b₃.trans h1.1) (h1.2.trans b₄)
  have hR := zr_round_of_body (zr_scanPhaseContract t x) w c c₁ hc hrun1 hc₁s hB0
    (hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (fun q hq => by
      rcases hq with rfl | hq
      · exact hmem _ (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff.mp hq]
        exact hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
    hend (hP _ le_rfl (by omega) le_rfl (by omega)) hPC
  rw [hBt, hT, hBpost] at hR
  rw [show (if cell.isNone = true then 6 else if zr_slotEmpty t cell = true then w.length + 9
      else 8) = 1 + ((if cell.isNone = true then 4 else if zr_slotEmpty t cell = true then
        w.length + 7 else 6) + 1) by split_ifs <;> omega]
  exact hR

/-- The scan's configuration after `n` rounds: `n` marks on scratch from its start, scratch's
head just past them, the zoned head at `p` and the state `s`. -/
private def zr_scanCfg {k : ℕ} {S : Type} {x : List (ZoneSym k)} (d : Cfg 2 (ZoneSym k) S x)
    (s : Option S) (n : ℕ) (p : ℤ) : Cfg 2 (ZoneSym k) S x :=
  { d with
    state := s
    workTapes := Function.update d.workTapes 1 fun q =>
      if d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + n then some (Sum.inl false)
      else d.workTapes 1 q
    workTapePos := fun j => if j = 0 then p else d.workTapePos 1 + n }

/-- One more mark extends the marked block by one cell. -/
private lemma zr_scanCfg_marked {k : ℕ} {S : Type} {x : List (ZoneSym k)}
    (d : Cfg 2 (ZoneSym k) S x) (s : Option S) (n : ℕ) (p : ℤ) (s' : S) (p' : ℤ) :
    zr_scanMarked (zr_scanCfg d s n p) s' p' = zr_scanCfg d (some s') (n + 1) p' := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j q
    by_cases hj : j = 1
    · subst hj
      simp only [zr_scanCfg, Function.update_self, Function.update_apply,
        show (1 : Fin 2) ≠ 0 by decide, if_false, Nat.cast_add, Nat.cast_one]
      split_ifs <;> first | rfl | omega
    · simp only [zr_scanCfg, Function.update_of_ne hj]
  · funext j
    simp only [zr_scanCfg, show (1 : Fin 2) ≠ 0 by decide, if_false,
      Nat.cast_add, Nat.cast_one]
    split_ifs
    · rfl
    · ring
  · rfl

/-- The scan configuration's fields: tape `0` and the start's other fields are kept. -/
private lemma zr_scanCfg_fields {k : ℕ} {S : Type} {x : List (ZoneSym k)}
    (d : Cfg 2 (ZoneSym k) S x) (s : Option S) (n : ℕ) (p : ℤ) :
    (zr_scanCfg d s n p).state = s ∧ (zr_scanCfg d s n p).workTapes 0 = d.workTapes 0 ∧
      (zr_scanCfg d s n p).workTapePos 0 = p ∧
      (zr_scanCfg d s n p).workTapePos 1 = d.workTapePos 1 + n :=
  ⟨rfl, by simp only [zr_scanCfg, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)],
    by simp only [zr_scanCfg, if_true],
    by simp only [zr_scanCfg, show (1 : Fin 2) ≠ 0 by decide, if_false]⟩

/-- The word the scan's round `r` crosses: zone `r`, or the empty word past the layout. -/
private def zr_scanWord {k : ℕ} (D : ZoneData k) (r : ℕ) : List (ZoneSym k) :=
  if h : r < D.1 then zoneCells true D.2 ⟨r, h⟩ else []

/-- Past the layout the scan's cell is blank. -/
private lemma zr_scan_end {k : ℕ} (D : ZoneData k) : zonedTape D.2 (zoneStart D.1) = none :=
  zonedTape_blank_outside D.2 _ (by
    rw [abs_of_nonneg (by omega)]
    omega)

/-- At the start of zone `r`, or at the cell past the layout, the scan's round word lies at the
zoned head. -/
private lemma zr_scanWord_at {k : ℕ} {S : Type} {x : List (ZoneSym k)} (D : ZoneData k)
    (r : ℕ) (hr : r ≤ D.1) (c : Cfg 2 (ZoneSym k) S x) (h0 : c.workTapes 0 = zonedTape D.2)
    (hp : c.workTapePos 0 = zoneStart r) : zr_wordAt (zr_scanWord D r) c := by
  intro p hp0 hp1
  rw [h0, hp, zr_scanWord]
  split_ifs with h
  · rw [zr_scanWord, dif_pos h, zoneCells_length] at hp1
    exact zonedTape_right_word D.2 ⟨r, h⟩ p (by omega) hp1
  · rw [zr_scanWord, dif_neg h, List.length_nil] at hp1
    obtain rfl : r = D.1 := by omega
    obtain rfl : p = 0 := by omega
    rw [FinTM.bufferTape_nil, add_zero]
    exact zr_scan_end D

/-- The scan's tests at the start of zone `r`: the cell is not blank, and its track-`t` slot is
empty exactly when zone `r` is. -/
private lemma zr_scan_test {k : ℕ} (D : ZoneData k) (t : Fin k) (r : ℕ) (hr : r < D.1) :
    (zonedTape D.2 (zoneStart r)).isNone = false ∧
      (zr_slotEmpty t (zonedTape D.2 (zoneStart r)) = true ↔
        (D.2 t).words true ⟨r, hr⟩ = []) := by
  have hcap : 0 < zoneCapacity r := by
    rw [zoneCapacity_eq]
    have := Nat.two_pow_pos r
    omega
  have hcell := zonedTape_right D.2 ⟨r, hr⟩ 0 hcap
  have he := zr_inner_empty_iff true D.2 ⟨r, hr⟩ t
  rw [zr_zonePos, if_pos rfl] at he
  simp only [Nat.add_zero] at hcell he
  rw [hcell, Option.map_some, Option.some.injEq] at he
  rw [hcell, Option.isNone_some, zr_slotEmpty, Option.isNone_iff_eq_none, he]
  exact ⟨rfl, Iff.rfl⟩

/-- At the scanned index, below the level count, the track-`t` slot is occupied. -/
private lemma zr_scan_found {k : ℕ} (D : ZoneData k) (t : Fin k) (j : ℕ)
    (hj : zoneRebalanceIndex true t D = j) (hlt : j < D.1) :
    zr_slotEmpty t (zonedTape D.2 (zoneStart j)) = false := by
  subst hj
  have hne := zoneShiftIndex_nonempty true (D.2 t) hlt
  cases h : zr_slotEmpty t (zonedTape D.2 (zoneStart (zoneRebalanceIndex true t D)))
  · rfl
  · exact absurd ((zr_scan_test D t _ hlt).2.mp h) hne

/-- The scan's round times add up to the crossed extent and nine steps per crossed zone. -/
private lemma zr_scan_time_sum (n : ℕ) :
    ∑ r ∈ Finset.range n, (zoneCapacity r + 9) + zoneStart 0 = zoneStart n + 8 * n := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, mul_zero, add_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, zoneStart_succ]
    omega

/-- The scan's round time from a round's start `c`: by the zoned cell's tests, with the word of
the zone at the scratch head's offset from the start `d`. -/
private def zr_scanTau {k : ℕ} {S : Type} {x : List (ZoneSym k)} (t : Fin k) (D : ZoneData k)
    (d c : Cfg 2 (ZoneSym k) S x) : ℕ :=
  if (c.workTapes 0 (c.workTapePos 0)).isNone then 6
  else if zr_slotEmpty t (c.workTapes 0 (c.workTapePos 0)) then
    (zr_scanWord D (c.workTapePos 1 - d.workTapePos 1).toNat).length + 9
  else 8

/-- The scan's precondition at the loop's start: tape `0` is the zoned tape of `D`, with its
head at the start of zone `0`. -/
private def zr_scanPre {k : ℕ} {S : Type} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) S x) : Prop :=
  d.workTapes 0 = zonedTape D.2 ∧ d.workTapePos 0 = zoneStart 0

/-- The scan's round `r` from the anchor at the start of zone `r`, for `r` up to the scanned
index, as one statement. -/
private lemma zr_scan_round_at {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) x)
    (hd : d.state = some ⟨false, some false⟩) (hp : zr_scanPre D d) (r : ℕ)
    (hr : r ≤ zoneRebalanceIndex true t D) (P : (Fin 2 → ℤ) → Prop)
    (hP : ∀ p : Fin 2 → ℤ, zoneStart r ≤ p 0 → p 0 ≤ zoneStart r + (zr_scanWord D r).length + 1 →
      d.workTapePos 1 + r ≤ p 1 → p 1 ≤ d.workTapePos 1 + r + 1 → P p) :
    Round (zr_scanTM t) ⟨false, some false⟩ {some ⟨false, some true⟩, some ⟨false, none⟩} P
      (zr_scanCfg d d.state r (zoneStart r))
      (zr_scanMarked (zr_scanCfg d d.state r (zoneStart r))
        ⟨false, if (zonedTape D.2 (zoneStart r)).isNone then some true
          else if zr_slotEmpty t (zonedTape D.2 (zoneStart r)) then some false else none⟩
        (if ¬ (zonedTape D.2 (zoneStart r)).isNone ∧ zr_slotEmpty t (zonedTape D.2 (zoneStart r))
          then zoneStart r + (zr_scanWord D r).length + 1
        else zoneStart r))
      (zr_scanTau t D d (zr_scanCfg d d.state r (zoneStart r))) := by
  have hi := zoneShiftIndex_le true (D.2 t)
  rw [zoneRebalanceIndex] at hr
  obtain ⟨e0, e1, e2, e3⟩ := zr_scanCfg_fields d d.state r (zoneStart r)
  have hc : (zr_scanCfg d d.state r (zoneStart r)).workTapes 0
      ((zr_scanCfg d d.state r (zoneStart r)).workTapePos 0) = zonedTape D.2 (zoneStart r) := by
    rw [e1, e2, hp.1]
  have hR := zr_scan_round t (zr_scanWord D r) (zr_scanCfg d d.state r (zoneStart r)) (e0.trans hd)
    (zr_scanWord_at D r (by omega) _ (e1.trans hp.1) e2) P (fun p h₀ h₁ h₂ h₃ => by
      rw [e2] at h₀ h₁
      rw [e3] at h₂ h₃
      exact hP p h₀ h₁ h₂ h₃)
  rw [hc, e2] at hR
  rw [zr_scanTau, hc, e3, show d.workTapePos 1 + (r : ℤ) - d.workTapePos 1 = r by ring,
    Int.toNat_natCast]
  exact hR

/-- The scan's orbit: up to the scanned index, round `r` starts at the anchor with the zoned
head at the start of zone `r` and `r` marks on scratch.

**Proof sketch.** Induct on `r`: below the scanned index, zone `r` is empty
(`zoneShiftIndex_empty`), so its round skips it and ends at the anchor at zone `r + 1`. -/
private lemma zr_scan_orbit {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) x)
    (hd : d.state = some ⟨false, some false⟩) (hp : zr_scanPre D d) :
    ∀ r ≤ zoneRebalanceIndex true t D,
      roundOrbit (zr_scanTM t) (zr_scanTau t D d) d r = zr_scanCfg d d.state r (zoneStart r) := by
  intro r
  induction r with
  | zero =>
    intro _
    rw [roundOrbit_zero]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j q
      by_cases hj : j = 1
      · subst hj
        simp only [zr_scanCfg, Function.update_self, Nat.cast_zero, add_zero]
        split_ifs with h
        · omega
        · rfl
      · simp only [zr_scanCfg, Function.update_of_ne hj]
    · funext j
      simp only [zr_scanCfg, Nat.cast_zero, add_zero]
      split_ifs with h
      · rw [h, hp.2]
      · have hj1 : j = 1 := by omega
        rw [hj1]
    · rfl
  | succ r ih =>
    intro hr
    have hi := zoneShiftIndex_le true (D.2 t)
    rw [zoneRebalanceIndex] at hr
    have hrl : r < D.1 := by omega
    obtain ⟨hn, hs⟩ := zr_scan_test D t r hrl
    have hem := zoneShiftIndex_empty true (D.2 t) ⟨r, hrl⟩ (by simp only; omega)
    have hR := zr_scan_round_at t D d hd hp r (by rw [zoneRebalanceIndex]; omega)
      (fun _ => True) (fun _ _ _ _ _ => trivial)
    rw [roundOrbit_succ, ih (by rw [zoneRebalanceIndex]; omega),
      ((round_iff _ _ _ _ _ _ _).mp hR).2.2.1, hn, hs.mpr hem]
    simp only [Bool.false_eq_true, if_false, if_true, not_false_eq_true, true_and]
    rw [zr_scanCfg_marked, hd, zr_scanWord, dif_pos hrl, zoneCells_length]
    congr 2
    rw [zoneStart_succ]
    push_cast
    ring

/-- The scan loop's endpoint: the escape by the scanned index, `i₀ + 1` marks, the zoned head
at the start of zone `i₀` (the cell past the layout when every zone is empty). -/
private abbrev zr_scanLoopPost {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) x) :
    Cfg 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) x :=
  zr_scanCfg d
    (some ⟨false, if zoneRebalanceIndex true t D < D.1 then none else some true⟩)
    (zoneRebalanceIndex true t D + 1) (zoneStart (zoneRebalanceIndex true t D))

/-- **The scan loop's run**, as a segment against its two escapes inside the box
`[zoneStart 0, zoneStart (i₀ + 1)]` for the zoned head and `[q, q + i₀ + 1]` for scratch.

**Proof sketch.** `Turing.Round.iterate` over the `i₀ + 1` rounds of `zr_scan_round_at`, on the
orbit `zr_scan_orbit`; the last round stops at the found escape on zone `i₀`
(`zoneShiftIndex_nonempty`) or at the short escape past the layout. The times add up by
`zr_scan_time_sum`. -/
private lemma zr_scanLoop_segment {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh zr_scanSt b) x)
    (hd : d.state = some ⟨false, some false⟩) (hp : zr_scanPre D d) :
    Segment (zr_scanTM t) {some ⟨false, some true⟩, some ⟨false, none⟩}
      (HeadBox (fun j => if j = 0 then (zoneStart 0 : ℤ) else d.workTapePos j)
        (fun j => if j = 0 then (zoneStart (zoneRebalanceIndex true t D + 1) : ℤ)
          else d.workTapePos 1 + zoneRebalanceIndex true t D + 1))
      d (zr_scanLoopPost t D d)
      (zoneStart (zoneRebalanceIndex true t D) + 8 * zoneRebalanceIndex true t D +
        if zoneRebalanceIndex true t D < D.1 then 6 else 4) := by
  have hi := zoneShiftIndex_le true (D.2 t)
  have hsi : zoneShiftIndex true (D.2 t) = zoneRebalanceIndex true t D := rfl
  rw [zr_scanLoopPost]
  generalize hi₀ : zoneRebalanceIndex true t D = i₀ at hsi ⊢
  rw [hsi] at hi
  have hbox : ∀ p : Fin 2 → ℤ, (zoneStart 0 : ℤ) ≤ p 0 → p 0 ≤ zoneStart (i₀ + 1) →
      d.workTapePos 1 ≤ p 1 → p 1 ≤ d.workTapePos 1 + i₀ + 1 →
      HeadBox (fun j => if j = 0 then (zoneStart 0 : ℤ) else d.workTapePos j)
        (fun j => if j = 0 then (zoneStart (i₀ + 1) : ℤ) else d.workTapePos 1 + i₀ + 1) p := by
    intro p h0 h1 h2 h3
    rw [headBox_iff]
    intro j
    rw [Finset.mem_Icc]
    match j with
    | 0 => exact ⟨h0, h1⟩
    | 1 =>
      simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
      exact ⟨h2, h3⟩
  have hround : ∀ r < i₀ + 1,
      Round (zr_scanTM t) ⟨false, some false⟩ {some ⟨false, some true⟩, some ⟨false, none⟩}
        (HeadBox (fun j => if j = 0 then (zoneStart 0 : ℤ) else d.workTapePos j)
          (fun j => if j = 0 then (zoneStart (i₀ + 1) : ℤ) else d.workTapePos 1 + i₀ + 1))
        (roundOrbit (zr_scanTM t) (zr_scanTau t D d) d r)
        (roundOrbit (zr_scanTM t) (zr_scanTau t D d) d (r + 1))
        (zr_scanTau t D d (roundOrbit (zr_scanTM t) (zr_scanTau t D d) d r)) := by
    intro r hr
    rw [roundOrbit_succ, zr_scan_orbit t D d hd hp r (by rw [hi₀]; omega)]
    have hR := zr_scan_round_at t D d hd hp r (by rw [hi₀]; omega)
      (HeadBox (fun j => if j = 0 then (zoneStart 0 : ℤ) else d.workTapePos j)
        (fun j => if j = 0 then (zoneStart (i₀ + 1) : ℤ) else d.workTapePos 1 + i₀ + 1))
      (fun p h₀ h₁ h₂ h₃ => by
        have hm := zoneStart_mono (Nat.zero_le r)
        have hw : (zoneStart r : ℤ) + (zr_scanWord D r).length + 1 ≤ zoneStart (i₀ + 1) := by
          rw [zr_scanWord]
          split_ifs with h
          · rw [zoneCells_length, Fin.val_mk]
            have := zoneStart_mono (show r + 1 ≤ i₀ + 1 by omega)
            have := zoneStart_succ r
            omega
          · have := zoneStart_mono (show r ≤ i₀ by omega)
            have := zoneStart_succ i₀
            simp only [List.length_nil, Nat.cast_zero]
            omega
        exact hbox p (by omega) (by omega) (by omega) (by omega))
    rw [((round_iff _ _ _ _ _ _ _).mp hR).2.2.1]
    exact hR
  have hseg := Round.iterate (zr_scanTau t D d) d
    (fun h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq, Sigma.mk.injEq,
        heq_eq_eq, reduceCtorEq, and_false, or_self] at h)
    (hbox _ (by rw [hp.2]) (by
      rw [hp.2]
      exact_mod_cast zoneStart_mono (Nat.zero_le _)) (le_refl _) (by omega)) (i₀ + 1) hround
  have hlast := zr_scan_round_at t D d hd hp i₀ hi₀.ge (fun _ => True)
    (fun _ _ _ _ _ => trivial)
  have hend : roundOrbit (zr_scanTM t) (zr_scanTau t D d) d (i₀ + 1) =
      zr_scanCfg d (some ⟨false, if i₀ < D.1 then none else some true⟩) (i₀ + 1)
        (zoneStart i₀) := by
    rw [roundOrbit_succ, zr_scan_orbit t D d hd hp i₀ hi₀.ge,
      ((round_iff _ _ _ _ _ _ _).mp hlast).2.2.1, zr_scanCfg_marked]
    rcases Nat.lt_or_ge i₀ D.1 with hlt | hge
    · rw [(zr_scan_test D t i₀ hlt).1, zr_scan_found D t i₀ hi₀ hlt]
      simp only [Bool.false_eq_true, if_false, and_false, if_pos hlt]
    · obtain rfl : i₀ = D.1 := by omega
      rw [zr_scan_end]
      simp only [Option.isNone_none, if_true, not_true_eq_false, false_and, if_false,
        lt_irrefl]
  have htime : ∑ r ∈ Finset.range (i₀ + 1),
      zr_scanTau t D d (roundOrbit (zr_scanTM t) (zr_scanTau t D d) d r) =
        zoneStart i₀ + 8 * i₀ + if i₀ < D.1 then 6 else 4 := by
    have hτ : ∀ r < i₀, zr_scanTau t D d (roundOrbit (zr_scanTM t) (zr_scanTau t D d) d r) =
        zoneCapacity r + 9 := by
      intro r hr
      have hrl : r < D.1 := by omega
      obtain ⟨e0, e1, e2, e3⟩ := zr_scanCfg_fields d d.state r (zoneStart r)
      obtain ⟨hn, hs⟩ := zr_scan_test D t r hrl
      have hem := zoneShiftIndex_empty true (D.2 t) ⟨r, hrl⟩ (by simp only; omega)
      rw [zr_scan_orbit t D d hd hp r (by rw [hi₀]; omega), zr_scanTau, e1, e2, e3, hp.1, hn,
        hs.mpr hem, show d.workTapePos 1 + (r : ℤ) - d.workTapePos 1 = r by ring,
        Int.toNat_natCast, zr_scanWord, dif_pos hrl, zoneCells_length]
      simp only [Bool.false_eq_true, if_false, if_true]
    have hlastτ : zr_scanTau t D d (roundOrbit (zr_scanTM t) (zr_scanTau t D d) d i₀) =
        if i₀ < D.1 then 8 else 6 := by
      obtain ⟨e0, e1, e2, e3⟩ := zr_scanCfg_fields d d.state i₀ (zoneStart i₀)
      rw [zr_scan_orbit t D d hd hp i₀ hi₀.ge, zr_scanTau, e1, e2, hp.1]
      rcases Nat.lt_or_ge i₀ D.1 with hlt | hge
      · rw [(zr_scan_test D t i₀ hlt).1, zr_scan_found D t i₀ hi₀ hlt]
        simp only [Bool.false_eq_true, if_false, if_pos hlt]
      · obtain rfl : i₀ = D.1 := by omega
        rw [zr_scan_end]
        simp only [Option.isNone_none, if_true, lt_irrefl, if_false]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl fun r hr => hτ r (Finset.mem_range.mp hr),
      hlastτ]
    have hs := zr_scan_time_sum i₀
    have h0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
    split_ifs <;> omega
  rw [hend, htime] at hseg
  exact hseg

/-- **The scan loop as a contract**: from the anchor at the start of zone `0` of `D`'s zoned
tape, the loop crosses the empty zones of track `t`, marking scratch once per round, and stops at
the found escape on zone `i₀` or at the short escape past the layout. -/
private def zr_scanLoopContract {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    Contract (zr_scanTM t) ⟨false, some false⟩ {some ⟨false, some true⟩, some ⟨false, none⟩}
      (ZoneData k) x :=
  Contract.ofSegment zr_scanPre
    (fun D _ => zoneStart (zoneRebalanceIndex true t D) + 8 * zoneRebalanceIndex true t D +
      if zoneRebalanceIndex true t D < D.1 then 6 else 4)
    (fun D d => zr_scanLoopPost t D d)
    (fun _ d j => if j = 0 then (zoneStart 0 : ℤ) else d.workTapePos j)
    (fun D d j => if j = 0 then (zoneStart (zoneRebalanceIndex true t D + 1) : ℤ)
      else d.workTapePos 1 + zoneRebalanceIndex true t D + 1)
    (fun D d hd hp => zr_scanLoop_segment t D d hd hp)
    (fun D d _ _ => by
      show some (⟨false, if zoneRebalanceIndex true t D < D.1 then none else some true⟩ :
        Σ b, zr_hostPh zr_scanSt b) ∈ _
      split_ifs
      · exact Set.mem_insert_of_mem _ rfl
      · exact Set.mem_insert _ _)

/-- The scan's lead-in: from home, skip the home field to the start of zone `0`. Its
precondition is the zoned tape of `D` at home. -/
private def zr_homeSkipContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (skipTM_contract 0 x)
    (fun D : ZoneData k => [Sum.inr fun t => some (D.2 t).home])
    (fun (D : ZoneData k) (d : Cfg 2 (ZoneSym k) SeekPhase x) =>
      d.workTapes 0 = zonedTape D.2 ∧ d.workTapePos 0 = 0)
    fun D d hp => by
      rw [skipTM_contract_pre]
      intro p h0 h1
      rw [hp.1, hp.2, zero_add]
      exact zr_home_word D.2 p (by omega) h1

/-- **The rebalance scan** (rightward): skip the home field, then run the scan loop. It stops at
the found escape on the first zone `i₀` whose track-`t` slot is occupied, or at the short
escape past the layout, with `i₀ + 1` ruler cells on scratch. -/
private def zr_scanContract {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  (zr_homeSkipContract x).seq (zr_scanLoopContract t x) (fun D => D) fun D d _ hp => by
    rw [zr_homeSkipContract, zr_reindexContract, Contract.ofSegment_pre] at hp
    rw [zr_scanLoopContract, Contract.ofSegment_pre, zr_scanPre, zr_homeSkipContract,
      zr_reindexContract, Contract.ofSegment_post, skipTM_contract_post]
    have h0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
    refine ⟨funext fun q => ?_, ?_⟩
    · rw [Cfg.mapState_workTapes, seekPost_workTapes, hp.1]
    · rw [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self, hp.2,
        List.length_singleton, h0]
      norm_num

/-- **The scan's fields**: it stops at the escape by the scanned index `i₀`, with the zoned head
at the start of zone `i₀` (past the layout when every zone is empty) and `i₀ + 1` ruler cells on
scratch from its start, its head just past them, after `zoneStart i₀ + 8 i₀ + 9` steps on a
found zone and two fewer on a short scan; the zoned head stays in `[0, zoneStart (i₀ + 1)]`,
scratch in `[q, q + i₀ + 1]`. -/
private lemma zr_scan_fields {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ Σ b, zr_hostPh zr_scanSt b) x) :
    (zr_scanContract t x).time D d = zoneStart (zoneRebalanceIndex true t D) +
        8 * zoneRebalanceIndex true t D + (if zoneRebalanceIndex true t D < D.1 then 9 else 7) ∧
      (zr_scanContract t x).post D d =
        zr_scanCfg d (some (Sum.inr
          ⟨false, if zoneRebalanceIndex true t D < D.1 then none else some true⟩))
          (zoneRebalanceIndex true t D + 1) (zoneStart (zoneRebalanceIndex true t D)) ∧
      (zr_scanContract t x).lo D d 0 = min (d.workTapePos 0) (zoneStart 0) ∧
      (zr_scanContract t x).hi D d 0 =
        max (d.workTapePos 0 + 2) (zoneStart (zoneRebalanceIndex true t D + 1)) ∧
      (zr_scanContract t x).lo D d 1 = d.workTapePos 1 ∧
      (zr_scanContract t x).hi D d 1 = d.workTapePos 1 + zoneRebalanceIndex true t D + 1 := by
  have hm := zoneStart_mono (Nat.zero_le (zoneRebalanceIndex true t D + 1))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zr_scanContract, Contract.seq_time, zr_scanLoopContract, Contract.ofSegment_time,
      zr_homeSkipContract, zr_reindexContract, Contract.ofSegment_time, skipTM_contract_time,
      List.length_singleton]
    split_ifs <;> omega
  · rw [zr_scanContract, Contract.seq_post, zr_scanLoopContract, Contract.ofSegment_post,
      zr_scanLoopPost, zr_homeSkipContract, zr_reindexContract, Contract.ofSegment_post,
      skipTM_contract_post]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some, zr_scanCfg]
    · simp only [Cfg.mapState_inputPos, zr_scanCfg, seekPost_inputPos]
    · funext j q
      by_cases hj : j = 1
      · subst hj
        simp only [Cfg.mapState_workTapes, zr_scanCfg, Function.update_self,
          Cfg.mapState_workTapePos, seekPost_workTapes, seekPost_workTapePos,
          Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      · simp only [Cfg.mapState_workTapes, zr_scanCfg, Function.update_of_ne hj,
          seekPost_workTapes]
    · funext j
      simp only [Cfg.mapState_workTapePos, zr_scanCfg, seekPost_workTapePos,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    · simp only [Cfg.mapState_output, zr_scanCfg, seekPost_output]
  all_goals
    simp only [zr_scanContract, Contract.seq_lo, Contract.seq_hi, zr_scanLoopContract,
      Contract.ofSegment_lo, Contract.ofSegment_hi, Contract.ofSegment_post,
      zr_homeSkipContract, zr_reindexContract,
      skipTM_contract_lo, skipTM_contract_hi, skipTM_contract_post, Cfg.mapState_workTapePos,
      seekPost_workTapePos, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
      List.length_singleton, if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, Nat.cast_one]
  all_goals omega

/-- Skip back over the scratch ruler of `n` cells from two cells past its last one to its first
cell. -/
private def zr_scratchBackContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (skipBackTM_contract 1 x) (fun n => List.replicate n (Sum.inl false))
    (fun n d => zr_scratchAt ((n : ℤ) + 1) n d) fun n d hp => by
      rw [skipBackTM_contract_pre]
      intro p _ _
      rw [hp.2, (zr_rulerTape_word n (d.workTapePos 1 - ((n : ℤ) + 1)) p).1,
        List.length_replicate]
      congr 1
      ring

/-- **The count's clear**: from just past the scratch ruler of `n` cells, step right, skip back
to its first cell and clear it. -/
private def zr_countClearContract {k : ℕ} (x : List (ZoneSym k)) :=
  (zr_stepContract 1 1 x fun (n : ℕ) d => zr_scratchAt (n : ℤ) n d).seq
    ((zr_scratchBackContract x).seq (zr_rulerClearContract (fun n : ℕ => n) x) (fun n => n)
      fun n d _ hp => by
        rw [zr_scratchBackContract, zr_reindexContract, Contract.ofSegment_pre] at hp
        rw [zr_rulerClearContract, zr_reindexContract, Contract.ofSegment_pre,
          zr_scratchBackContract, zr_reindexContract, Contract.ofSegment_post,
          skipBackTM_contract_post]
        refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_
        · rw [Cfg.mapState_workTapes, seekPost_workTapes]
        · rw [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
            List.length_replicate]
          ring)
    (fun n => n) fun n d _ hp => by
      rw [zr_stepContract, Contract.ofSegment_pre] at hp
      rw [Contract.seq_pre, zr_scratchBackContract, zr_reindexContract, Contract.ofSegment_pre,
        zr_stepContract, Contract.ofSegment_post]
      refine zr_scratchAt_move _ _ hp (fun r => ?_) ?_
      · simp only [Cfg.mapState_workTapes, zr_cellContract, zr_cellPost]
      · simp only [Cfg.mapState_workTapePos, zr_cellContract, zr_cellPost, Function.update_self,
          SignType.coe_one]
        ring

/-- **The count clear's fields**: from just past a scratch ruler of `n` cells that is all of
scratch, it blanks scratch and returns its head to the ruler's first cell in `3n + 8` steps;
the zoned head is fixed and scratch stays in `[q - n - 1, q + 1]`. -/
private lemma zr_countClear_fields {k : ℕ} {x : List (ZoneSym k)} (n : ℕ)
    (d : Cfg 2 (ZoneSym k) (Option Bool ⊕ SeekPhase ⊕ SweepPhase) x)
    (hp : zr_scratchAt (n : ℤ) n d) :
    (zr_countClearContract x).time n d = 3 * n + 8 ∧
      (zr_countClearContract x).post n d =
        { d with
          state := some (Sum.inr (Sum.inr SweepPhase.done))
          workTapes := Function.update d.workTapes 1 fun _ => none
          workTapePos := Function.update d.workTapePos 1 (d.workTapePos 1 - n) } ∧
      (zr_countClearContract x).lo n d 0 = d.workTapePos 0 ∧
      (zr_countClearContract x).hi n d 0 = d.workTapePos 0 ∧
      (zr_countClearContract x).lo n d 1 = d.workTapePos 1 - n - 1 ∧
      (zr_countClearContract x).hi n d 1 = d.workTapePos 1 + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zr_countClearContract, Contract.seq_time, zr_stepContract,
      Contract.ofSegment_time, zr_cellContract, zr_scratchBackContract, zr_reindexContract,
      skipBackTM_contract_time, zr_rulerClearContract, clearTM_contract_time,
      List.length_replicate]
    omega
  · simp only [zr_countClearContract, Contract.seq_post, zr_stepContract,
      Contract.ofSegment_post, zr_cellContract, zr_cellPost, zr_scratchBackContract,
      zr_reindexContract, skipBackTM_contract_post, zr_rulerClearContract,
      clearTM_contract_post]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, sweepPost_state, Option.map_some]
    · simp only [Cfg.mapState_inputPos, sweepPost_inputPos, seekPost_inputPos]
    · funext j q
      by_cases hj : j = 1
      · subst hj
        simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, sweepPost_workTapes,
          seekPost_workTapes, seekPost_workTapePos, Function.update_self,
          List.length_replicate, true_and, SignType.coe_one, hp.2, zr_rulerTape]
        split_ifs <;> first | rfl | omega
      · simp only [Cfg.mapState_workTapes, sweepPost_workTapes, seekPost_workTapes, hj,
          false_and, if_false, Function.update_of_ne hj]
    · funext j
      by_cases hj : j = 1
      · subst hj
        simp only [Cfg.mapState_workTapePos, sweepPost_workTapePos, seekPost_workTapePos,
          Function.update_self, List.length_replicate, SignType.coe_one]
        ring
      · simp only [Cfg.mapState_workTapePos, sweepPost_workTapePos, seekPost_workTapePos,
          Function.update_of_ne hj]
    · simp only [Cfg.mapState_output, sweepPost_output, seekPost_output]
  all_goals
    simp only [zr_countClearContract, Contract.seq_lo, Contract.seq_hi, zr_stepContract,
      Contract.ofSegment_lo, Contract.ofSegment_hi, Contract.ofSegment_post, zr_cellContract,
      zr_cellPost, zr_scratchBackContract, zr_reindexContract, skipBackTM_contract_lo,
      skipBackTM_contract_hi, skipBackTM_contract_post,
      zr_rulerClearContract, clearTM_contract_lo, clearTM_contract_hi,
      Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), List.length_replicate,
      SignType.coe_one, if_true, show (0 : Fin 2) ≠ 1 by decide, if_false]
  all_goals omega

/-- The short path's return home: the return loop at the scanned data, carrying the count on
scratch. -/
private def zr_shortLoopContract {k : ℕ} (x : List (ZoneSym k)) :=
  zr_reindexContract (zr_loopContract x) (fun D => D)
    (fun (D : ZoneData k) d => zr_loopPre D d ∧ zr_scratchAt ((D.1 + 1 : ℕ) : ℤ) (D.1 + 1) d)
    fun _ _ hp => by
      rw [zr_loopContract, Contract.ofSegment_pre]
      exact hp.1

/-- **The short path**: after a short scan, return the zoned head home and clear the count. -/
private def zr_shortContract {k : ℕ} (x : List (ZoneSym k)) :=
  letI := zr_decEqLoopPh
  (zr_shortLoopContract x).seq (zr_countClearContract x) (fun D => D.1 + 1) fun D d _ hp => by
    rw [zr_shortLoopContract, zr_reindexContract, Contract.ofSegment_pre] at hp
    rw [zr_countClearContract, Contract.seq_pre, zr_stepContract, Contract.ofSegment_pre,
      zr_shortLoopContract, zr_reindexContract, Contract.ofSegment_post, zr_loopContract,
      Contract.ofSegment_post]
    refine zr_scratchAt_move _ _ hp.2 (fun r => ?_) ?_ <;>
    simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- **The short path's fields**: from one past the last zone of `D` with the count of
`ℓ + 1` cells on scratch, it returns the zoned head home, blanks scratch and returns its head to
the count's first cell, in `zoneStart ℓ + 11 ℓ + 20` steps; the zoned head stays in
`[-1, zoneStart ℓ]`, scratch in `[q - ℓ - 2, q + 1]`. -/
private lemma zr_short_fields {k : ℕ} {x : List (ZoneSym k)} (D : ZoneData k)
    (d : Cfg 2 (ZoneSym k) ((Σ b, zr_loopPh b) ⊕ Option Bool ⊕ SeekPhase ⊕ SweepPhase) x)
    (hp : (zr_shortContract x).pre D d) :
    (zr_shortContract x).time D d = zoneStart D.1 + 11 * D.1 + 20 ∧
      (zr_shortContract x).post D d =
        { d with
          state := some (Sum.inr (Sum.inr (Sum.inr SweepPhase.done)))
          workTapes := Function.update d.workTapes 1 fun _ => none
          workTapePos := fun j => if j = 0 then 0 else d.workTapePos 1 - (D.1 + 1) } ∧
      (zr_shortContract x).lo D d 0 = -1 ∧ (zr_shortContract x).hi D d 0 = zoneStart D.1 ∧
      (zr_shortContract x).lo D d 1 = d.workTapePos 1 - D.1 - 2 ∧
      (zr_shortContract x).hi D d 1 = d.workTapePos 1 + 1 := by
  letI := zr_decEqLoopPh
  rw [zr_shortContract, Contract.seq_pre, zr_shortLoopContract, zr_reindexContract,
    Contract.ofSegment_pre] at hp
  set e := ((zr_shortLoopContract x).post D (d.mapState fun _ => ⟨false, some false⟩)).mapState
    fun _ => (Sum.inl none : Option Bool ⊕ SeekPhase ⊕ SweepPhase) with he
  have he0 : e.workTapePos 0 = 0 := by
    rw [he, Cfg.mapState_workTapePos, zr_shortLoopContract, zr_reindexContract,
      Contract.ofSegment_post, zr_loopContract, Contract.ofSegment_post]
    simp only [Function.update_self]
  have he1 : e.workTapePos 1 = d.workTapePos 1 := by
    rw [he, Cfg.mapState_workTapePos, zr_shortLoopContract, zr_reindexContract,
      Contract.ofSegment_post, zr_loopContract, Contract.ofSegment_post]
    simp only [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), Cfg.mapState_workTapePos]
  have het : e.workTapes = d.workTapes := by
    funext j q
    rw [he, Cfg.mapState_workTapes, zr_shortLoopContract, zr_reindexContract,
      Contract.ofSegment_post, zr_loopContract, Contract.ofSegment_post]
    simp only [Cfg.mapState_workTapes]
  have hc : zr_scratchAt ((D.1 + 1 : ℕ) : ℤ) (D.1 + 1) e :=
    zr_scratchAt_move _ e hp.2 (fun r => by rw [het, Cfg.mapState_workTapes])
      (by rw [he1, Cfg.mapState_workTapePos])
  obtain ⟨ht, hpost, hlo0, hhi0, hlo1, hhi1⟩ := zr_countClear_fields (D.1 + 1) e hc
  have hL := two_le_zoneStart D.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zr_shortContract, Contract.seq_time, ← he, ht, zr_shortLoopContract, zr_reindexContract,
      Contract.ofSegment_time, zr_loopContract, Contract.ofSegment_time]
    ring
  · rw [zr_shortContract, Contract.seq_post, ← he, hpost]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
    · rw [Cfg.mapState_inputPos, he, Cfg.mapState_inputPos, zr_shortLoopContract,
        zr_reindexContract, Contract.ofSegment_post, zr_loopContract, Contract.ofSegment_post,
        Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes]
      simp only [het]
    · funext j
      rw [Cfg.mapState_workTapePos]
      by_cases hj : j = 1
      · subst hj
        simp only [Function.update_self, he1, show (1 : Fin 2) ≠ 0 by decide, if_false]
        push_cast
        ring
      · have hj0 : j = 0 := by omega
        subst hj0
        simp only [Function.update_of_ne hj, he0, if_true]
    · rw [Cfg.mapState_output, he, Cfg.mapState_output, zr_shortLoopContract,
        zr_reindexContract, Contract.ofSegment_post, zr_loopContract, Contract.ofSegment_post,
        Cfg.mapState_output]
  · rw [zr_shortContract, Contract.seq_lo, ← he, hlo0, zr_shortLoopContract,
      zr_reindexContract, Contract.ofSegment_lo, zr_loopContract, Contract.ofSegment_lo, he0]
    simp only [if_true]
    omega
  · rw [zr_shortContract, Contract.seq_hi, ← he, hhi0, zr_shortLoopContract,
      zr_reindexContract, Contract.ofSegment_hi, zr_loopContract, Contract.ofSegment_hi, he0]
    simp only [if_true]
    omega
  · rw [zr_shortContract, Contract.seq_lo, ← he, hlo1, zr_shortLoopContract,
      zr_reindexContract, Contract.ofSegment_lo, zr_loopContract, Contract.ofSegment_lo, he1]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, Cfg.mapState_workTapePos]
    omega
  · rw [zr_shortContract, Contract.seq_hi, ← he, hhi1, zr_shortLoopContract,
      zr_reindexContract, Contract.ofSegment_hi, zr_loopContract, Contract.ofSegment_hi, he1]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, Cfg.mapState_workTapePos]
    omega

/-- **A short scan leads into the short path**: when every feeding zone of track `t` is empty,
the scan's endpoint from a zone-row start satisfies the short path's precondition (its count is
all of scratch). -/
private lemma zr_scanShort_pre {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (D : ZoneData k)
    (s : Σ b, zr_loopPh b)
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ Σ b, zr_hostPh zr_scanSt b) x) (hp : zoneRowPre D d)
    (hs : zoneRebalanceIndex true t D = D.1) :
    zr_loopPre D (((zr_scanContract t x).post D d).mapState fun _ => s) ∧
      zr_scratchAt ((D.1 + 1 : ℕ) : ℤ) (D.1 + 1)
        (((zr_scanContract t x).post D d).mapState fun _ => s) := by
  rw [(zr_scan_fields t D d).2.1, hs]
  obtain ⟨-, e1, e2, e3⟩ := zr_scanCfg_fields d
    (some (Sum.inr ⟨false, if D.1 < D.1 then none else some true⟩)) (D.1 + 1) (zoneStart D.1)
  refine ⟨⟨by rw [Cfg.mapState_workTapePos, e2], fun q _ _ => ?_⟩, Nat.succ_pos _, fun r => ?_⟩
  · rw [Cfg.mapState_workTapes, e1, hp.1]
  · rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, e3, zr_rulerTape]
    simp only [zr_scanCfg, Function.update_self, hp.2.2 r]
    split_ifs <;> first | rfl | omega

/-- A track's slots on the zoned tape depend on that track's contents only. -/
private lemma zr_slot_track {k ℓ : ℕ} {z z' : Fin k → ZoneContents ℓ} {t : Fin k}
    (h : z t = z' t) (q : ℤ) :
    (zonedTape z q).map (zoneSlotOf t) = (zonedTape z' q).map (zoneSlotOf t) := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · rw [zonedTape_of_neg z hq, zonedTape_of_neg z' hq, zoneCellAt_eq, zoneCellAt_eq]
    cases zoneOwner ℓ (-q).toNat <;> simp only [Option.map_none, Option.map_some, zoneSlotOf_inr, h]
  · simp only [zonedTape_zero, Option.map_some, zoneSlotOf_inr, h]
  · rw [zonedTape_of_pos z hq, zonedTape_of_pos z' hq, zoneCellAt_eq, zoneCellAt_eq]
    cases zoneOwner ℓ q.toNat <;> simp only [Option.map_none, Option.map_some, zoneSlotOf_inr, h]

/-- **Rewriting one track of a zoned cell**: where the zoned tape of `z` has a cell, the zoned
tape with track `t` replaced by `u` holds that cell with track `t`'s slot set to the new one. -/
private lemma zr_zonedTape_update {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k)
    (u : ZoneContents ℓ) (q : ℤ) (v : Option (Option Bool))
    (hv : (zonedTape (fun _ => u) q).map (zoneSlotOf t) = some v) :
    zonedTape (Function.update z t u) q = some (zoneSlotSet t (zonedTape z q) v) := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · rw [zonedTape_of_neg _ hq, zoneCellAt_eq] at hv
    rw [zonedTape_of_neg _ hq, zonedTape_of_neg _ hq, zoneCellAt_eq, zoneCellAt_eq]
    cases ho : zoneOwner ℓ (-q).toNat with
    | none => rw [ho, Option.map_none] at hv; cases hv
    | some i =>
      rw [ho, Option.map_some, Option.map_some, zoneSlotOf_inr, Option.some.injEq] at hv
      simp only [Option.map_some, zoneSlotSet_eq, zoneCellOfCell_inr, Option.some.injEq,
        Sum.inr.injEq]
      funext s
      by_cases hs : s = t
      · subst hs
        rw [Function.update_self, Function.update_self, hv]
      · rw [Function.update_of_ne hs, Function.update_of_ne hs]
  · rw [zonedTape_zero, Option.map_some, zoneSlotOf_inr, Option.some.injEq] at hv
    simp only [zonedTape_zero, zoneSlotSet_eq, zoneCellOfCell_inr, Option.some.injEq,
      Sum.inr.injEq]
    funext s
    by_cases hs : s = t
    · subst hs
      rw [Function.update_self, Function.update_self, hv]
    · rw [Function.update_of_ne hs, Function.update_of_ne hs]
  · rw [zonedTape_of_pos _ hq, zoneCellAt_eq] at hv
    rw [zonedTape_of_pos _ hq, zonedTape_of_pos _ hq, zoneCellAt_eq, zoneCellAt_eq]
    cases ho : zoneOwner ℓ q.toNat with
    | none => rw [ho, Option.map_none] at hv; cases hv
    | some i =>
      rw [ho, Option.map_some, Option.map_some, zoneSlotOf_inr, Option.some.injEq] at hv
      simp only [Option.map_some, zoneSlotSet_eq, zoneCellOfCell_inr, Option.some.injEq,
        Sum.inr.injEq]
      funext s
      by_cases hs : s = t
      · subst hs
        rw [Function.update_self, Function.update_self, hv]
      · rw [Function.update_of_ne hs, Function.update_of_ne hs]

/-- Every nonblank cell of the zoned tape is a zone cell. -/
private lemma zr_zonedTape_inr {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (q : ℤ)
    (γ : ZoneSym k) (h : zonedTape z q = some γ) : ∃ c, γ = .inr c := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · rw [zonedTape_of_neg z hq, zoneCellAt_eq] at h
    cases ho : zoneOwner ℓ (-q).toNat with
    | none => rw [ho, Option.map_none] at h; cases h
    | some i =>
      rw [ho, Option.map_some, Option.some.injEq] at h
      exact ⟨_, h.symm⟩
  · rw [zonedTape_zero, Option.some.injEq] at h
    exact ⟨_, h.symm⟩
  · rw [zonedTape_of_pos z hq, zoneCellAt_eq] at h
    cases ho : zoneOwner ℓ q.toNat with
    | none => rw [ho, Option.map_none] at h; cases h
    | some i =>
      rw [ho, Option.map_some, Option.some.injEq] at h
      exact ⟨_, h.symm⟩

/-- Where track `t`'s new slot equals the old one, the rewritten zoned tape keeps the cell. -/
private lemma zr_zonedTape_update_same {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k)
    (u : ZoneContents ℓ) (q : ℤ)
    (h : (zonedTape (fun _ => u) q).map (zoneSlotOf t) = (zonedTape z q).map (zoneSlotOf t)) :
    zonedTape (Function.update z t u) q = zonedTape z q := by
  cases hz : zonedTape z q with
  | none =>
    have hs := zonedTape_isSome (Function.update z t u) z q
    rw [hz, Option.isSome_none] at hs
    exact Option.not_isSome_iff_eq_none.mp (by rw [hs]; decide)
  | some γ =>
    obtain ⟨c, rfl⟩ := zr_zonedTape_inr z q γ hz
    rw [hz, Option.map_some, zoneSlotOf_inr] at h
    rw [zr_zonedTape_update z t u q (c t) h, hz, zoneSlotSet_eq, zoneCellOfCell_inr,
      Function.update_eq_self]

/-- **The right inward shift on the zoned tape**, its guard enabled: when track `t`'s right zone
`i - 1` is empty, the shift at level `i` sets track `t`'s slots of zone `i - 1`'s first
`2^(i-1)` cells to zone `i`'s first `2^(i-1)` slots, and zone `i`'s slots to its slots
`2^(i-1)` further on (`⊠` past its word); every other cell keeps its contents. -/
private lemma zr_shiftIn_tape {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : ℕ)
    (hi : 1 ≤ i) (hiℓ : i < ℓ) (he : (z t).right ⟨i - 1, by omega⟩ = []) (q : ℤ) :
    zonedTape (Function.update z t (zoneShiftIn true i (z t))) q =
      if (zoneStart (i - 1) : ℤ) ≤ q ∧ q < zoneStart (i - 1) + ((2 ^ (i - 1) : ℕ) : ℤ) then
        some (zoneSlotSet t (zonedTape z q)
          ((z t).right ⟨i, hiℓ⟩)[(q - zoneStart (i - 1)).toNat]?)
      else if (zoneStart i : ℤ) ≤ q ∧ q < zoneStart i + zoneCapacity i then
        some (zoneSlotSet t (zonedTape z q)
          ((z t).right ⟨i, hiℓ⟩)[2 ^ (i - 1) + (q - zoneStart i).toNat]?)
      else zonedTape z q := by
  have hur : ∀ j : Fin ℓ, (zoneShiftIn true i (z t)).right j =
      if j.val = i - 1 then ((z t).right ⟨i, hiℓ⟩).take (2 ^ (i - 1))
      else if j.val = i then ((z t).right ⟨i, hiℓ⟩).drop (2 ^ (i - 1))
      else (z t).right j := by
    intro j
    rw [zoneShiftIn_right, if_pos rfl, zoneShiftInW_eq, dif_pos ⟨hi, hiℓ⟩, if_pos he]
  have hul : (zoneShiftIn true i (z t)).left = (z t).left := by
    funext j
    rw [zoneShiftIn_left, if_pos rfl]
  have huh : (zoneShiftIn true i (z t)).home = (z t).home := zoneShiftIn_home true i (z t)
  have hcap : zoneCapacity (i - 1) = 2 * 2 ^ (i - 1) := zoneCapacity_eq (i - 1)
  have hcapi : zoneCapacity i = 4 * 2 ^ (i - 1) := by
    rw [zoneCapacity_eq, show i = (i - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hlen : ((z t).right ⟨i, hiℓ⟩).length ≤ zoneCapacity i := (z t).right_le ⟨i, hiℓ⟩
  have hpos : 0 < 2 ^ (i - 1) := Nat.two_pow_pos _
  split_ifs with h1 h2
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = (zoneStart (i - 1) : ℤ) + p :=
      ⟨(q - zoneStart (i - 1)).toNat, by omega⟩
    apply zr_zonedTape_update
    have hs := zr_read_slot true (fun _ => zoneShiftIn true i (z t)) ⟨i - 1, by omega⟩ t p
      (by simp only; omega)
    rw [zr_zonePos, if_pos rfl] at hs
    rw [show (zoneStart (i - 1) : ℤ) + p = ((zoneStart (i - 1) + p : ℕ) : ℤ) by push_cast; ring,
      hs, ZoneContents.words_true, hur, if_pos rfl, List.getElem?_take, if_pos (by omega)]
    simp only [Nat.cast_add, add_sub_cancel_left, Int.toNat_natCast]
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = (zoneStart i : ℤ) + p := ⟨(q - zoneStart i).toNat, by omega⟩
    apply zr_zonedTape_update
    have hs := zr_read_slot true (fun _ => zoneShiftIn true i (z t)) ⟨i, hiℓ⟩ t p
      (by simp only; omega)
    rw [zr_zonePos, if_pos rfl] at hs
    rw [show (zoneStart i : ℤ) + p = ((zoneStart i + p : ℕ) : ℤ) by push_cast; ring, hs,
      ZoneContents.words_true, hur, if_neg (by simp only; omega), if_pos rfl,
      List.getElem?_drop]
    simp only [Nat.cast_add, add_sub_cancel_left, Int.toNat_natCast]
  · apply zr_zonedTape_update_same
    rw [zr_slot_track (z := z) (z' := fun _ => z t) rfl q]
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · rw [zonedTape_of_neg _ hq, zonedTape_of_neg _ hq, zoneCellAt_eq, zoneCellAt_eq]
      simp only [ZoneContents.words_false, hul]
    · simp only [zonedTape_zero, Option.map_some, zoneSlotOf_inr, huh]
    · rw [zonedTape_of_pos _ hq, zonedTape_of_pos _ hq, zoneCellAt_eq, zoneCellAt_eq]
      cases ho : zoneOwner ℓ q.toNat with
      | none => rfl
      | some o =>
        have hm := (Fin.find_eq_some_iff.mp ((zoneOwner_eq ℓ q.toNat).symm.trans ho)).1
        simp only [Option.map_some, zoneSlotOf_inr, ZoneContents.words_true, hur]
        split_ifs with ho1 ho2
        · have hoe : (z t).right o = [] := by
            rw [show o = ⟨i - 1, by omega⟩ from Fin.ext ho1]
            exact he
          rw [List.getElem?_take, if_neg (by rw [ho1] at hm ⊢; omega), hoe, List.getElem?_nil]
        · exfalso
          rw [ho2] at hm
          omega
        · rfl

/-- Two nonempty layouts side by side are one layout, with one separator between them. -/
private lemma zr_joinFields_append {Γ : Type} (ws vs : List (List Γ)) (hw : ws ≠ [])
    (hv : vs ≠ []) : joinFields (ws ++ vs) = joinFields ws ++ none :: joinFields vs := by
  induction ws with
  | nil => exact absurd rfl hw
  | cons u ws ih =>
    cases ws with
    | nil =>
      obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil hv
      rw [List.singleton_append, joinFields_cons_cons, joinFields_singleton]
    | cons u' ws =>
      rw [List.cons_append, List.cons_append, joinFields_cons_cons, ← List.cons_append,
        ih (List.cons_ne_nil _ _), joinFields_cons_cons, List.append_assoc, List.cons_append]

/-- **One more field**: the tape of a nonempty layout with a field appended is the layout's
tape before the new field's offset, and the new field's delimited word from there. -/
private lemma zr_fieldsTape_snoc {Γ : Type} (ws : List (List Γ)) (hw : ws ≠ []) (u : List Γ)
    (z : ℤ) :
    fieldsTape (ws ++ [u]) z =
      if z < fieldOffset ws ws.length then fieldsTape ws z
      else FinTM.bufferTape u (z - fieldOffset ws ws.length) := by
  have hlen := length_joinFields_add_one ws hw
  rcases lt_or_ge z 0 with hz | hz
  · rw [fieldsTape_of_neg _ hz, if_pos (by omega), fieldsTape_of_neg _ hz]
  rw [fieldsTape_of_nonneg _ hz, zr_joinFields_append ws [u] hw (List.cons_ne_nil _ _),
    joinFields_singleton]
  split_ifs with h
  · rw [fieldsTape_of_nonneg _ hz]
    by_cases hl : z.toNat < (joinFields ws).length
    · rw [List.getElem?_append_left hl]
    · rw [List.getElem?_append_right (by omega),
        show z.toNat - (joinFields ws).length = 0 by omega, List.getElem?_cons_zero,
        Option.join_some, List.getElem?_eq_none (by omega)]
      rfl
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, z - fieldOffset ws ws.length = n :=
      ⟨(z - fieldOffset ws ws.length).toNat, by omega⟩
    rw [hn, FinTM.bufferTape_nat, List.getElem?_append_right (by omega),
      show z.toNat - (joinFields ws).length = n + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_map]
    cases u[n]? <;> rfl

/-- A layout with a marked field: the earlier fields and a separator, the field's cells, then a
separator and the later fields. -/
private lemma zr_joinFields_mid {Γ : Type} (pre post : List (List Γ)) (w : List Γ) :
    joinFields (pre ++ [w] ++ post) =
      (if pre.isEmpty then [] else joinFields pre ++ [none]) ++ w.map some ++
        (if post.isEmpty then [] else none :: joinFields post) := by
  by_cases hpre : pre = [] <;> by_cases hpost : post = []
  · subst hpre hpost
    simp only [List.nil_append, List.append_nil, joinFields_singleton, List.isEmpty_nil,
      if_true]
  · subst hpre
    rw [List.isEmpty_nil, if_pos rfl, if_neg (by simpa using hpost), List.nil_append,
      List.nil_append, zr_joinFields_append [w] post (List.cons_ne_nil _ _) hpost,
      joinFields_singleton]
  · subst hpost
    rw [if_neg (by simpa using hpre), List.isEmpty_nil, if_pos rfl, List.append_nil,
      List.append_nil, zr_joinFields_append pre [w] hpre (List.cons_ne_nil _ _),
      joinFields_singleton, List.append_assoc, List.singleton_append]
  · rw [if_neg (by simpa using hpre), if_neg (by simpa using hpost), List.append_assoc,
      zr_joinFields_append pre ([w] ++ post) hpre (by simp),
      zr_joinFields_append [w] post (List.cons_ne_nil _ _) hpost, joinFields_singleton]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The marked field starts where the earlier fields end. -/
private lemma zr_joinFields_mid_offset {Γ : Type} (pre : List (List Γ)) :
    ((if pre.isEmpty then [] else joinFields pre ++ [none]) : List (Option Γ)).length =
      fieldOffset pre pre.length := by
  split_ifs with h
  · rw [List.isEmpty_iff.mp h, List.length_nil, List.length_nil, fieldOffset_zero]
  · rw [List.length_append, List.length_singleton,
      length_joinFields_add_one pre (by simpa using h)]

/-- One list entry replaced, read at every index. -/
private lemma zr_getElem?_mid {α : Type} (P Q : List α) (x y : α) (n : ℕ) :
    (P ++ x :: Q)[n]? = if n = P.length then some x else (P ++ y :: Q)[n]? := by
  rcases lt_trichotomy n P.length with h | rfl | h
  · rw [if_neg (by omega), List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [if_pos rfl, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero]
  · obtain ⟨m, hm⟩ : ∃ m, n - P.length = m + 1 := ⟨n - P.length - 1, by omega⟩
    rw [if_neg (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), hm, List.getElem?_cons_succ,
      List.getElem?_cons_succ]

/-- **Cutting a field**: blanking the cell after `u` in a field `u ++ a :: v` splits it into the
two fields `u` and `v`. -/
private lemma zr_fieldsTape_cut {Γ : Type} (pre post : List (List Γ)) (u v : List Γ) (a : Γ) :
    Function.update (fieldsTape (pre ++ [u ++ a :: v] ++ post))
        ((fieldOffset pre pre.length + u.length : ℕ) : ℤ) none =
      fieldsTape (pre ++ [u, v] ++ post) := by
  have h1 := zr_joinFields_mid pre post (u ++ a :: v)
  have h2 := zr_joinFields_mid pre ([v] ++ post) u
  have h3 := zr_joinFields_mid [] post v
  have hoff := zr_joinFields_mid_offset pre
  rw [List.isEmpty_nil, if_pos rfl, List.nil_append, List.nil_append] at h3
  rw [show ([v] ++ post).isEmpty = false from rfl, if_neg Bool.false_ne_true, h3] at h2
  rw [show pre ++ [u, v] ++ post = pre ++ [u] ++ ([v] ++ post) by simp]
  funext z
  rcases lt_or_ge z 0 with hz | hz
  · rw [Function.update_of_ne (by omega), fieldsTape_of_neg _ hz, fieldsTape_of_neg _ hz]
  rw [fieldsTape_of_nonneg _ hz, h2]
  by_cases hz0 : z = ((fieldOffset pre pre.length + u.length : ℕ) : ℤ)
  · rw [hz0, Function.update_self, Int.toNat_natCast, ← hoff,
      zr_getElem?_mid _ _ none (some a), if_pos (by simp)]
    rfl
  · have hne : z.toNat ≠ ((if pre.isEmpty then [] else joinFields pre ++ [none]) ++
        u.map some).length := by
      rw [List.length_append, List.length_map, hoff]
      omega
    rw [Function.update_of_ne hz0, fieldsTape_of_nonneg _ hz, h1, List.append_assoc,
      zr_getElem?_mid _ _ none (some a), if_neg hne, List.map_append, List.map_cons,
      List.append_assoc, List.append_assoc, List.cons_append]

/-- A configuration's tapes and heads are the pinned ones. -/
private def zr_pinned {k : ℕ} {S : Type} {x : List (ZoneSym k)}
    (T : Fin 2 → ℤ → Option (ZoneSym k)) (p : Fin 2 → ℤ) (d : Cfg 2 (ZoneSym k) S x) : Prop :=
  d.workTapes = T ∧ d.workTapePos = p

/-- Renaming the state neither makes nor breaks a pin. -/
private lemma zr_pinned_mapState_iff {k : ℕ} {S S' : Type} {x : List (ZoneSym k)}
    {T : Fin 2 → ℤ → Option (ZoneSym k)} {p : Fin 2 → ℤ} {d : Cfg 2 (ZoneSym k) S x}
    (f : S → S') : zr_pinned T p (d.mapState f) ↔ zr_pinned T p d := by
  simp only [zr_pinned]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨funext fun j => funext fun q => ?_,
    funext fun j => ?_⟩
  · rw [← Cfg.mapState_workTapes f d j q, h1]
  · rw [← Cfg.mapState_workTapePos f d j, h2]
  · rw [Cfg.mapState_workTapes f d j q, h1]
  · rw [Cfg.mapState_workTapePos f d j, h2]

/-- Renaming the state keeps a pin. -/
private lemma zr_pinned_mapState {k : ℕ} {S S' : Type} {x : List (ZoneSym k)}
    {T : Fin 2 → ℤ → Option (ZoneSym k)} {p : Fin 2 → ℤ} {d : Cfg 2 (ZoneSym k) S x}
    (f : S → S') (h : zr_pinned T p d) : zr_pinned T p (d.mapState f) :=
  (zr_pinned_mapState_iff f).mpr h

/-- **A pinned step**: the contract's precondition is a valid index and the start pin
`(T₁ j, p₁ j)`; from every such start its endpoint is pinned at `(T₂ j, p₂ j)`, with the input
head and the output kept, after `τ j` steps, its heads within `[L j, U j]`. -/
private def zr_PinStep {k : ℕ} {S J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X : Set (Option S)} (C : Contract M e X J x)
    (V : J → Prop) (T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)) (p₁ p₂ : J → Fin 2 → ℤ)
    (τ : J → ℕ) (L U : J → Fin 2 → ℤ) : Prop :=
  (∀ j (d : Cfg 2 (ZoneSym k) S x), C.pre j d → V j ∧ zr_pinned (T₁ j) (p₁ j) d) ∧
    ∀ j (d : Cfg 2 (ZoneSym k) S x), V j → zr_pinned (T₁ j) (p₁ j) d →
      C.pre j d ∧ zr_pinned (T₂ j) (p₂ j) (C.post j d) ∧
        (C.post j d).inputPos = d.inputPos ∧ (C.post j d).output = d.output ∧
        C.time j d = τ j ∧ ∀ i, L j i ≤ C.lo j d i ∧ C.hi j d i ≤ U j i

/-- **Pinned steps compose**: a sequence of two pinned steps, the second's start pin the
first's endpoint pin, is a pinned step; the times add with the seam's step, the boxes join. -/
private lemma zr_PinStep_seq {k : ℕ} {S₁ S₂ J : Type} [DecidableEq S₁] {x : List (ZoneSym k)}
    {M₁ : MultiTapeTM 2 (ZoneSym k) S₁} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₁ d₁ : S₁}
    {e₂ : S₂} {X₂ : Set (Option S₂)} {C₁ : Contract M₁ e₁ {some d₁} J x}
    {C₂ : Contract M₂ e₂ X₂ J x}
    {T₁ T₂ T₃ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ p₃ : J → Fin 2 → ℤ}
    {τ₁ τ₂ : J → ℕ} {L₁ U₁ L₂ U₂ : J → Fin 2 → ℤ} {V : J → Prop}
    (h₁ : zr_PinStep C₁ V T₁ T₂ p₁ p₂ τ₁ L₁ U₁) (h₂ : zr_PinStep C₂ V T₂ T₃ p₂ p₃ τ₂ L₂ U₂)
    (hl : ∀ j d, d.state = some e₁ → C₁.pre j d →
      C₂.pre j ((C₁.post j d).mapState fun _ => e₂)) :
    zr_PinStep (C₁.seq C₂ (fun j => j) hl) V T₁ T₃ p₁ p₃ (fun j => τ₁ j + 1 + τ₂ j)
      (fun j i => min (L₁ j i) (L₂ j i)) (fun j i => max (U₁ j i) (U₂ j i)) := by
  refine ⟨fun j d hp => ?_, fun j d hV hd => ?_⟩
  · rw [Contract.seq_pre] at hp
    obtain ⟨hV, hd⟩ := h₁.1 j _ hp
    exact ⟨hV, (zr_pinned_mapState_iff _).mp hd⟩
  obtain ⟨hp₁, hq₁, hi₁, ho₁, ht₁, hb₁⟩ :=
    h₁.2 j (d.mapState fun _ => e₁) hV (zr_pinned_mapState _ hd)
  obtain ⟨hp₂, hq₂, hi₂, ho₂, ht₂, hb₂⟩ :=
    h₂.2 j ((C₁.post j (d.mapState fun _ => e₁)).mapState fun _ => e₂) hV
      (zr_pinned_mapState _ hq₁)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · rw [Contract.seq_pre]
    exact hp₁
  · rw [Contract.seq_post]
    exact zr_pinned_mapState _ hq₂
  · rw [Contract.seq_post, Cfg.mapState_inputPos, hi₂, Cfg.mapState_inputPos, hi₁,
      Cfg.mapState_inputPos]
  · rw [Contract.seq_post, Cfg.mapState_output, ho₂, Cfg.mapState_output, ho₁,
      Cfg.mapState_output]
  · rw [Contract.seq_time, ht₁, ht₂]
  · rw [Contract.seq_lo, Contract.seq_hi]
    exact ⟨min_le_min (hb₁ i).1 (hb₂ i).1, max_le_max (hb₁ i).2 (hb₂ i).2⟩

/-- **A pinned re-indexed row is a pinned step** once its endpoint, its time and its envelope
from the pin are known. -/
private lemma zr_pinRe_step {k : ℕ} {S I J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X : Set (Option S)} (C : Contract M e X I x)
    (f : J → I) (V : J → Prop) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hP : ∀ j d, V j ∧ zr_pinned (T j) (p j) d → C.pre (f j) d)
    {T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₂ : J → Fin 2 → ℤ} {τ : J → ℕ}
    {L U : J → Fin 2 → ℤ}
    (h : ∀ j d, V j → zr_pinned (T j) (p j) d →
      zr_pinned (T₂ j) (p₂ j) (C.post (f j) d) ∧ (C.post (f j) d).inputPos = d.inputPos ∧
        (C.post (f j) d).output = d.output ∧ C.time (f j) d = τ j ∧
        ∀ i, L j i ≤ C.lo (f j) d i ∧ C.hi (f j) d i ≤ U j i) :
    zr_PinStep (zr_reindexContract C f (fun j d => V j ∧ zr_pinned (T j) (p j) d) hP) V T T₂ p
      p₂ τ L U := by
  refine ⟨fun j d hd => by rwa [zr_reindexContract, Contract.ofSegment_pre] at hd,
    fun j d hV hd => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h j d hV hd
  rw [zr_reindexContract, Contract.ofSegment_pre, Contract.ofSegment_post,
    Contract.ofSegment_time]
  refine ⟨⟨hV, hd⟩, h1, h2, h3, h4, fun i => ?_⟩
  rw [Contract.ofSegment_lo, Contract.ofSegment_hi]
  exact h5 i

/-- A re-indexed pinned step of a segment-built contract, from its fields at the pin. -/
private lemma zr_pinRe_ofSeg {k : ℕ} {S I J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X : Set (Option S)}
    {pre : I → Cfg 2 (ZoneSym k) S x → Prop} {time : I → Cfg 2 (ZoneSym k) S x → ℕ}
    {post : I → Cfg 2 (ZoneSym k) S x → Cfg 2 (ZoneSym k) S x}
    {lo hi : I → Cfg 2 (ZoneSym k) S x → Fin 2 → ℤ}
    {seg : ∀ i d, d.state = some e → pre i d →
      Segment M X (HeadBox (lo i d) (hi i d)) d (post i d) (time i d)}
    {em : ∀ i d, d.state = some e → pre i d → (post i d).state ∈ X}
    (f : J → I) (V : J → Prop) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hP : ∀ j d, V j ∧ zr_pinned (T j) (p j) d → pre (f j) d)
    {T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₂ : J → Fin 2 → ℤ} {τ : J → ℕ}
    {L U : J → Fin 2 → ℤ}
    (h : ∀ j d, V j → zr_pinned (T j) (p j) d →
      zr_pinned (T₂ j) (p₂ j) (post (f j) d) ∧ (post (f j) d).inputPos = d.inputPos ∧
        (post (f j) d).output = d.output ∧ time (f j) d = τ j ∧
        ∀ i, L j i ≤ lo (f j) d i ∧ hi (f j) d i ≤ U j i) :
    zr_PinStep (zr_reindexContract (Contract.ofSegment pre time post lo hi seg em) f
      (fun j d => V j ∧ zr_pinned (T j) (p j) d) fun j d hd => by
        rw [Contract.ofSegment_pre]
        exact hP j d hd) V T T₂ p p₂ τ L U :=
  zr_pinRe_step _ f V T p _ fun j d hV hd => by
    simp only [Contract.ofSegment_post, Contract.ofSegment_time, Contract.ofSegment_lo,
      Contract.ofSegment_hi]
    exact h j d hV hd

/-- A seek-family endpoint from a pin: the tapes, the input head and the output kept, head `i`
moved to `v`. -/
private lemma zr_seekPost_pin {k : ℕ} {S : Type} {x : List (ZoneSym k)}
    {T : Fin 2 → ℤ → Option (ZoneSym k)} {p : Fin 2 → ℤ} {d : Cfg 2 (ZoneSym k) S x} {s : S}
    {i : Fin 2} {v : ℤ} (hd : zr_pinned T p d) :
    zr_pinned T (Function.update p i v) (seekPost s i v d) ∧
      (seekPost s i v d).inputPos = d.inputPos ∧ (seekPost s i v d).output = d.output := by
  refine ⟨⟨funext fun i' => funext fun q => ?_, funext fun i' => ?_⟩, ?_, ?_⟩
  · rw [seekPost_workTapes, hd.1]
  · rw [seekPost_workTapePos, hd.2]
  · rw [seekPost_inputPos]
  · rw [seekPost_output]

/-- A skip on tape `i`, its precondition the pin, the skipped word `w j` at the head. -/
private def zr_pinSkipContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop) (i : Fin 2)
    (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℤ, 0 ≤ q → q ≤ ((w j).length : ℤ) →
      T j i (p j i + q) = FinTM.bufferTape (w j) q) :=
  zr_reindexContract (skipTM_contract i x) w (fun j d => V j ∧ zr_pinned (T j) (p j) d)
    fun j d hd => by
      rw [skipTM_contract_pre, hd.2.1, hd.2.2]
      exact hw j hd.1

/-- The pinned skip moves only its head, past the word's right delimiter. -/
private lemma zr_pinSkip_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop) (i : Fin 2)
    (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℤ, 0 ≤ q → q ≤ ((w j).length : ℤ) →
      T j i (p j i + q) = FinTM.bufferTape (w j) q) :
    zr_PinStep (zr_pinSkipContract x V i w T p hw) V T T p
      (fun j => Function.update (p j) i (p j i + (w j).length + 1)) (fun j => (w j).length + 1)
      p (fun j => Function.update (p j) i (p j i + (w j).length + 1)) := by
  unfold zr_pinSkipContract
  refine zr_pinRe_step _ _ _ _ _ _ fun j d _ hd => ?_
  rw [skipTM_contract_post, skipTM_contract_time, hd.2]
  refine ⟨(zr_seekPost_pin hd).1, (zr_seekPost_pin hd).2.1, (zr_seekPost_pin hd).2.2, rfl,
    fun i' => ?_⟩
  rw [skipTM_contract_lo, skipTM_contract_hi, hd.2]
  by_cases hi : i' = i
  · subst hi
    simp only [if_true, Function.update_self]
    omega
  · simp only [hi, if_false, Function.update_of_ne hi, le_refl, and_self]

/-- A backward skip on tape `i`, its precondition the pin, the word `u j` ending one blank
before the head. -/
private def zr_pinBackContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop) (i : Fin 2)
    (u : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hu : ∀ j, V j → ∀ q : ℤ, -1 ≤ q → q ≤ ((u j).length : ℤ) →
      T j i (p j i - (u j).length - 1 + q) = FinTM.bufferTape (u j) q) :=
  zr_reindexContract (skipBackTM_contract i x) u (fun j d => V j ∧ zr_pinned (T j) (p j) d)
    fun j d hd => by
      rw [skipBackTM_contract_pre, hd.2.1, hd.2.2]
      exact hu j hd.1

/-- The pinned backward skip moves only its head, to the word's first cell. -/
private lemma zr_pinBack_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop) (i : Fin 2)
    (u : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hu : ∀ j, V j → ∀ q : ℤ, -1 ≤ q → q ≤ ((u j).length : ℤ) →
      T j i (p j i - (u j).length - 1 + q) = FinTM.bufferTape (u j) q) :
    zr_PinStep (zr_pinBackContract x V i u T p hu) V T T p
      (fun j => Function.update (p j) i (p j i - (u j).length - 1))
      (fun j => (u j).length + 3)
      (fun j => Function.update (p j) i (p j i - (u j).length - 2)) p := by
  unfold zr_pinBackContract
  refine zr_pinRe_step _ _ _ _ _ _ fun j d _ hd => ?_
  rw [skipBackTM_contract_post, skipBackTM_contract_time, hd.2]
  refine ⟨(zr_seekPost_pin hd).1, (zr_seekPost_pin hd).2.1, (zr_seekPost_pin hd).2.2, rfl,
    fun i' => ?_⟩
  rw [skipBackTM_contract_lo, skipBackTM_contract_hi, hd.2]
  by_cases hi : i' = i
  · subst hi
    simp only [if_true, Function.update_self]
    omega
  · simp only [hi, if_false, Function.update_of_ne hi, le_refl, and_self]

/-- The one-cell leaf as a pinned step: write `wr` if any, then move tape `i` by `dir`. -/
private def zr_pinCellContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop) (i : Fin 2)
    (dir : SignType) (wr : Option (Option (ZoneSym k)))
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :=
  zr_stepContract i dir x (fun j d => V j ∧ zr_pinned (T j) (p j) d) wr

/-- The one-cell leaf's pinned endpoint: tape `i` written at its head if asked, the head moved
by `dir`. -/
private lemma zr_pinCell_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop) (i : Fin 2)
    (dir : SignType) (wr : Option (Option (ZoneSym k)))
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :
    zr_PinStep (zr_pinCellContract x V i dir wr T p) V T
      (fun j => match wr with
        | none => T j
        | some a => Function.update (T j) i (Function.update (T j i) (p j i) a))
      p (fun j => Function.update (p j) i (p j i + dir)) (fun _ => 1)
      (fun j i' => min (p j i') (Function.update (p j) i (p j i + dir) i'))
      (fun j i' => max (p j i') (Function.update (p j) i (p j i + dir) i')) := by
  refine ⟨fun j d hd => ?_, fun j d hV hd => ?_⟩
  · rwa [zr_pinCellContract, zr_stepContract, Contract.ofSegment_pre] at hd
  have hp : (zr_pinCellContract x V i dir wr T p).pre j d := by
    rw [zr_pinCellContract, zr_stepContract, Contract.ofSegment_pre]
    exact ⟨hV, hd⟩
  have hpost : (zr_pinCellContract x V i dir wr T p).post j d =
      zr_cellPost i (fun _ => false) wr dir d := by
    rw [zr_pinCellContract, zr_stepContract, Contract.ofSegment_post, zr_cellContract]
  refine ⟨hp, ⟨?_, ?_⟩, ?_, ?_, ?_, fun i' => ?_⟩
  · rw [hpost]
    cases wr <;> simp only [zr_cellPost, hd.1, hd.2]
  · rw [hpost]
    simp only [zr_cellPost, hd.2]
  · rw [hpost]
    cases wr <;> rfl
  · rw [hpost]
    cases wr <;> rfl
  · rw [zr_pinCellContract, zr_stepContract, Contract.ofSegment_time, zr_cellContract]
  · rw [zr_pinCellContract, zr_stepContract, Contract.ofSegment_lo, Contract.ofSegment_hi,
      zr_cellContract]
    simp only [zr_cellPost, hd.2]
    exact ⟨le_rfl, le_rfl⟩

/-- A rightward lockstep walk over the word `w j` at tape `src`'s head, both heads moved, as a
pinned step. -/
private def zr_pinWalkContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop)
    (src : Fin 2) (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k))
    (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℕ, q ≤ (w j).length →
      T j src (p j src + q) = FinTM.bufferTape (w j) q) :=
  zr_reindexContract (walkTM_contract src (fun _ : Fin 2 => True) trivial 1 x) w
    (fun j d => V j ∧ zr_pinned (T j) (p j) d) fun j d hd => by
      rw [walkTM_contract_pre, hd.2.1, hd.2.2]
      intro q hq
      rw [SignType.coe_one, one_mul]
      exact (hw j hd.1 q hq).trans (FinTM.bufferTape_nat (w j) q)

/-- The pinned walk moves both heads `|w j| + 1` cells right. -/
private lemma zr_pinWalk_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop)
    (src : Fin 2) (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k))
    (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℕ, q ≤ (w j).length →
      T j src (p j src + q) = FinTM.bufferTape (w j) q) :
    zr_PinStep (zr_pinWalkContract x V src w T p hw) V T T p
      (fun j i => p j i + ((w j).length + 1 : ℕ)) (fun j => (w j).length + 1) p
      (fun j i => p j i + ((w j).length + 1 : ℕ)) := by
  unfold zr_pinWalkContract
  refine zr_pinRe_step _ _ _ _ _ _ fun j d _ hd => ?_
  rw [walkTM_contract_post, walkTM_contract_time, hd.2]
  refine ⟨⟨hd.1, funext fun i => ?_⟩, rfl, rfl, rfl, fun i => ?_⟩
  · simp only [if_true, SignType.coe_one, one_mul, Nat.cast_add, Nat.cast_one]
  · rw [walkTM_contract_lo, walkTM_contract_hi, hd.2]
    simp only [if_true, SignType.coe_one, one_mul, Nat.cast_add, Nat.cast_one]
    omega

/-- The tapes after a mapped copy from `src` onto `dst` of the word `w` at the pinned heads. -/
private abbrev zr_copyTapes {k : ℕ} {Δ : Type} (dst : Fin 2) (extract : ZoneSym k → Δ)
    (merge : Option (ZoneSym k) → Δ → ZoneSym k) (w : List (ZoneSym k))
    (T : Fin 2 → ℤ → Option (ZoneSym k)) (p : Fin 2 → ℤ) : Fin 2 → ℤ → Option (ZoneSym k) :=
  fun j q => if j = dst ∧ p dst ≤ q ∧ q < p dst + w.length then
    (FinTM.bufferTape w (q - p dst)).map fun γ => merge (T j q) (extract γ)
  else T j q

/-- A mapped copy from `src` onto `dst` as a pinned step, the copied word `w j` at `src`. -/
private def zr_pinCopyContract {k : ℕ} {J Δ : Type} (x : List (ZoneSym k)) (V : J → Prop)
    (src dst : Fin 2) (hne : src ≠ dst) (extract : ZoneSym k → Δ)
    (merge : Option (ZoneSym k) → Δ → ZoneSym k)
    (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℤ, -1 ≤ q → q ≤ ((w j).length : ℤ) →
      T j src (p j src + q) = FinTM.bufferTape (w j) q) :=
  zr_reindexContract (copyMapTM_contract src dst hne extract merge x) w
    (fun j d => V j ∧ zr_pinned (T j) (p j) d) fun j d hd => by
      rw [copyMapTM_contract_pre, hd.2.1, hd.2.2]
      exact hw j hd.1

/-- The pinned mapped copy writes `dst`'s interval and keeps the heads. -/
private lemma zr_pinCopy_step {k : ℕ} {J Δ : Type} {x : List (ZoneSym k)} (V : J → Prop)
    (src dst : Fin 2) (hne : src ≠ dst) (extract : ZoneSym k → Δ)
    (merge : Option (ZoneSym k) → Δ → ZoneSym k)
    (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℤ, -1 ≤ q → q ≤ ((w j).length : ℤ) →
      T j src (p j src + q) = FinTM.bufferTape (w j) q) :
    zr_PinStep (zr_pinCopyContract x V src dst hne extract merge w T p hw) V T
      (fun j => zr_copyTapes dst extract merge (w j) (T j) (p j)) p p
      (fun j => 2 * (w j).length + 2) (fun j i => p j i - 1)
      (fun j i => p j i + (w j).length) := by
  unfold zr_pinCopyContract
  refine zr_pinRe_step _ _ _ _ _ _ fun j d _ hd => ?_
  refine ⟨⟨funext fun i => funext fun q => ?_, funext fun i => ?_⟩, ?_, ?_, ?_, fun i => ?_⟩
  · rw [copyMapTM_contract_post_workTapes, hd.1, hd.2]
    by_cases hi : i = dst
    · subst hi
      rfl
    · simp only [zr_copyTapes, hi, false_and, if_false]
  · rw [copyMapTM_contract_post, sweepPost_workTapePos, hd.2]
  · rw [copyMapTM_contract_post, sweepPost_inputPos]
  · rw [copyMapTM_contract_post, sweepPost_output]
  · rw [copyMapTM_contract_time]
  · rw [copyMapTM_contract_lo, copyMapTM_contract_hi, hd.2]
    split_ifs <;> omega

/-- A clear of the word `w j` at tape `i`'s head as a pinned step. -/
private def zr_pinClearContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop) (i : Fin 2)
    (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℤ, -1 ≤ q → q ≤ ((w j).length : ℤ) →
      T j i (p j i + q) = FinTM.bufferTape (w j) q) :=
  zr_reindexContract (clearTM_contract i x) w (fun j d => V j ∧ zr_pinned (T j) (p j) d)
    fun j d hd => by
      rw [clearTM_contract_pre, hd.2.1, hd.2.2]
      exact hw j hd.1

/-- The pinned clear blanks the word's interval and keeps the heads. -/
private lemma zr_pinClear_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop) (i : Fin 2)
    (w : J → List (ZoneSym k)) (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ)
    (hw : ∀ j, V j → ∀ q : ℤ, -1 ≤ q → q ≤ ((w j).length : ℤ) →
      T j i (p j i + q) = FinTM.bufferTape (w j) q) :
    zr_PinStep (zr_pinClearContract x V i w T p hw) V T
      (fun j i' q => if i' = i ∧ p j i ≤ q ∧ q < p j i + (w j).length then none else T j i' q)
      p p (fun j => 2 * (w j).length + 2) (fun j i => p j i - 1)
      (fun j i => p j i + (w j).length) := by
  unfold zr_pinClearContract
  refine zr_pinRe_step _ _ _ _ _ _ fun j d _ hd => ?_
  rw [clearTM_contract_post, clearTM_contract_time, sweepPost_inputPos, sweepPost_output]
  refine ⟨⟨funext fun i' => funext fun q => ?_, funext fun i' => ?_⟩, rfl, rfl, rfl, fun i' => ?_⟩
  · rw [sweepPost_workTapes, hd.1, hd.2]
    by_cases hi : i' = i
    · subst hi
      rfl
    · simp only [hi, false_and, if_false]
  · rw [sweepPost_workTapePos, hd.2]
  · rw [clearTM_contract_lo, clearTM_contract_hi, hd.2]
    split_ifs <;> omega

/-- The right layout's field `m`: the home at `m = 0`, zone `m - 1` after it (empty past the
layout). -/
private def zr_rfield {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) : List (ZoneSym k) :=
  if m = 0 then [.inr fun t => some (z t).home]
  else if h : m - 1 < ℓ then zoneCells true z ⟨m - 1, h⟩ else []

/-- The right layout's field `m` starts at home for `m = 0` and at zone `m - 1`'s start after. -/
private def zr_rstart (m : ℕ) : ℤ := if m = 0 then 0 else zoneStart (m - 1)

/-- Field `m` has `2^m` cells. -/
private lemma zr_rfield_length {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) (hm : m ≤ ℓ) :
    (zr_rfield z m).length = 2 ^ m := by
  rw [zr_rfield]
  split_ifs with h0 h1
  · subst h0
    rfl
  · rw [zoneCells_length, zoneCapacity_eq]
    simp only
    rw [← pow_succ']
    congr 1
    omega
  · omega

/-- The next field starts one separator after field `m` ends. -/
private lemma zr_rstart_succ (m : ℕ) :
    zr_rstart (m + 1) = zr_rstart m + ((2 ^ m : ℕ) : ℤ) + 1 := by
  rw [zr_rstart, zr_rstart, if_neg (by omega), Nat.add_sub_cancel]
  split_ifs with h
  · subst h
    norm_num [zoneStart_eq]
  · have hs := zoneStart_succ (m - 1)
    rw [show m - 1 + 1 = m by omega, zoneCapacity_eq,
      show 2 * 2 ^ (m - 1) = 2 ^ m by rw [← pow_succ']; congr 1; omega] at hs
    rw [hs]
    push_cast
    ring

/-- **Each field of the right layout is a delimited word** on the zoned tape. -/
private lemma zr_rfield_word {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) (hm : m ≤ ℓ) :
    ∀ q : ℤ, -1 ≤ q → q ≤ ((zr_rfield z m).length : ℤ) →
      zonedTape z (zr_rstart m + q) = FinTM.bufferTape (zr_rfield z m) q := by
  intro q h1 h2
  rw [zr_rfield, zr_rstart] at *
  split_ifs at h2 ⊢ with h0 h1'
  · rw [zero_add]
    exact zr_home_word z q h1 (by simpa using h2)
  · rw [zoneCells_length] at h2
    exact zonedTape_right_word z ⟨m - 1, h1'⟩ q h1 h2
  · omega

/-- The scratch tape with the fields `ws` laid out from one cell past the head `s`: the start's
scratch `σ` up to `s`. -/
private abbrev zr_scr {k : ℕ} (σ : ℤ → Option (ZoneSym k)) (s : ℤ) (ws : List (List (ZoneSym k)))
    (r : ℤ) : Option (ZoneSym k) :=
  if r ≤ s then σ r else fieldsTape ws (r - (s + 1))

/-- The two work tapes as one family. -/
private abbrev zr_tapes {k : ℕ} (A B : ℤ → Option (ZoneSym k)) : Fin 2 → ℤ → Option (ZoneSym k) :=
  fun j => if j = 0 then A else B

/-- The two heads as one family. -/
private abbrev zr_heads (a b : ℤ) : Fin 2 → ℤ := fun j => if j = 0 then a else b

/-- A slot value as a scratch cell. -/
private abbrev zr_enc {k : ℕ} (v : Option (Option Bool)) : ZoneSym k := .inr fun _ => v

/-- Track `t`'s column of a word, as scratch cells. -/
private abbrev zr_col {k : ℕ} (t : Fin k) (w : List (ZoneSym k)) : List (ZoneSym k) :=
  w.map fun γ => zr_enc (zoneSlotOf t γ)

/-- A mapped word's buffer is the mapped buffer. -/
private lemma zr_bufferTape_map {α β : Type} (w : List α) (f : α → β) (q : ℤ) :
    FinTM.bufferTape (w.map f) q = (FinTM.bufferTape w q).map f := by
  rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq]
  split_ifs
  · rw [List.getElem?_map]
  · rfl

/-- Past its last field a layout is blank. -/
private lemma zr_fieldsTape_end {Γ : Type} (ws : List (List Γ)) (z : ℤ)
    (hz : (fieldOffset ws ws.length : ℤ) ≤ z + 1) : fieldsTape ws z = none := by
  by_cases hw : ws = []
  · subst hw
    exact fieldsTape_nil z
  · have h := length_joinFields_add_one ws hw
    exact fieldsTape_of_length_le ws (by omega)

/-- **One more field**, for every layout (the empty one included). -/
private lemma zr_fieldsTape_snoc' {Γ : Type} (ws : List (List Γ)) (u : List Γ) (z : ℤ) :
    fieldsTape (ws ++ [u]) z =
      if z < fieldOffset ws ws.length then fieldsTape ws z
      else FinTM.bufferTape u (z - fieldOffset ws ws.length) := by
  by_cases hw : ws = []
  · subst hw
    rw [List.nil_append, List.length_nil, fieldOffset_zero, Nat.cast_zero, sub_zero]
    split_ifs with hz
    · rw [fieldsTape_of_neg _ hz, fieldsTape_nil]
    · rw [fieldsTape_of_nonneg _ (by omega), joinFields_singleton, FinTM.bufferTape_eq,
        if_pos (by omega), List.getElem?_map]
      cases u[z.toNat]? <;> rfl
  · exact zr_fieldsTape_snoc ws hw u z

/-- **A copy onto blank scratch appends a field**: a mapped copy from tape `0` onto scratch at
the next field's offset lays the mapped word out as a new last field. -/
private lemma zr_scr_copy {k : ℕ} {Δ : Type} (A σ : ℤ → Option (ZoneSym k)) (s a : ℤ)
    (ws : List (List (ZoneSym k))) (extract : ZoneSym k → Δ)
    (merge : Option (ZoneSym k) → Δ → ZoneSym k) (w : List (ZoneSym k)) (b : ℤ)
    (hb : b = s + 1 + fieldOffset ws ws.length) :
    zr_copyTapes 1 extract merge w (zr_tapes A (zr_scr σ s ws)) (zr_heads a b) =
      zr_tapes A (zr_scr σ s (ws ++ [w.map fun γ => merge none (extract γ)])) := by
  subst hb
  funext j q
  by_cases hj : j = 0
  · subst hj
    simp only [zr_copyTapes, zr_tapes, zr_heads, show (0 : Fin 2) ≠ 1 by decide, false_and,
      if_false, if_true]
  · have hj1 : j = 1 := by omega
    subst hj1
    simp only [zr_copyTapes, zr_tapes, zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false,
      true_and, zr_scr]
    rw [zr_fieldsTape_snoc']
    set o := fieldOffset ws ws.length
    by_cases hq : q ≤ s
    · rw [if_neg (by omega), if_pos hq, if_pos hq]
    rw [if_neg hq, if_neg hq]
    by_cases hin : s + 1 + (o : ℤ) ≤ q ∧ q < s + 1 + o + w.length
    · rw [if_pos hin, if_neg (by omega), zr_fieldsTape_end ws _ (by omega), zr_bufferTape_map,
        show q - (s + 1 + (o : ℤ)) = q - (s + 1) - o by ring]
    · rw [if_neg hin]
      by_cases hlt : q - (s + 1) < o
      · rw [if_pos hlt]
      · rw [if_neg hlt, zr_fieldsTape_end ws _ (by omega), FinTM.bufferTape_eq,
          if_pos (by omega), List.getElem?_eq_none (by simp only [List.length_map]; omega)]

/-- **A blank written inside a field cuts it**: blanking scratch at the cell after `u` in a field
`u ++ a :: v` lays out `u` and `v` as two fields. -/
private lemma zr_scr_cut {k : ℕ} (A σ : ℤ → Option (ZoneSym k)) (s : ℤ)
    (pre post : List (List (ZoneSym k))) (u v : List (ZoneSym k)) (a : ZoneSym k) :
    Function.update (zr_tapes A (zr_scr σ s (pre ++ [u ++ a :: v] ++ post))) 1
        (Function.update (zr_tapes A (zr_scr σ s (pre ++ [u ++ a :: v] ++ post)) 1)
          (s + 1 + fieldOffset pre pre.length + u.length) none) =
      zr_tapes A (zr_scr σ s (pre ++ [u, v] ++ post)) := by
  have hcut := zr_fieldsTape_cut pre post u v a
  funext j q
  by_cases hj : j = 1
  · subst hj
    simp only [Function.update_self, zr_tapes, show (1 : Fin 2) ≠ 0 by decide, if_false, zr_scr]
    by_cases hq : q = s + 1 + fieldOffset pre pre.length + u.length
    · rw [hq, Function.update_self, if_neg (by omega), ← hcut,
        show s + 1 + (fieldOffset pre pre.length : ℤ) + u.length - (s + 1) =
          ((fieldOffset pre pre.length + u.length : ℕ) : ℤ) by push_cast; ring,
        Function.update_self]
    · rw [Function.update_of_ne hq]
      split_ifs with h
      · rfl
      · rw [← hcut, Function.update_of_ne (by push_cast; omega)]
  · have hj0 : j = 0 := by omega
    subst hj0
    simp only [Function.update_of_ne hj, zr_tapes, if_true]

/-- **A blank written inside a field splits it** at the `n`-th cell, which it removes. -/
private lemma zr_scr_split {k : ℕ} (A σ : ℤ → Option (ZoneSym k)) (s b : ℤ)
    (pre post : List (List (ZoneSym k))) (w : List (ZoneSym k)) (n m : ℕ) (hn : n < w.length)
    (hm : n + 1 = m) (hb : b = s + 1 + fieldOffset pre pre.length + n) :
    Function.update (zr_tapes A (zr_scr σ s (pre ++ [w] ++ post))) 1
        (Function.update (zr_tapes A (zr_scr σ s (pre ++ [w] ++ post)) 1) b none) =
      zr_tapes A (zr_scr σ s (pre ++ [w.take n, w.drop m] ++ post)) := by
  subst hb hm
  have h := zr_scr_cut A σ s pre post (w.take n) (w.drop (n + 1)) w[n]
  rwa [← List.drop_eq_getElem_cons hn, List.take_append_drop, List.length_take,
    min_eq_left hn.le] at h

/-- **Clearing the last field removes it**: blanking the last field's interval leaves the
earlier layout. -/
private lemma zr_scr_clear {k : ℕ} (A σ : ℤ → Option (ZoneSym k)) (s : ℤ)
    (pre : List (List (ZoneSym k))) (u : List (ZoneSym k)) (b : ℤ)
    (hb : b = s + 1 + fieldOffset pre pre.length) :
    (fun (i' : Fin 2) q => if i' = 1 ∧ b ≤ q ∧ q < b + u.length then none
      else zr_tapes A (zr_scr σ s (pre ++ [u])) i' q) =
      zr_tapes A (zr_scr σ s pre) := by
  subst hb
  funext j q
  by_cases hj : j = 0
  · subst hj
    simp only [show (0 : Fin 2) ≠ 1 by decide, false_and, if_false, zr_tapes, if_true]
  · have hj1 : j = 1 := by omega
    subst hj1
    simp only [true_and, zr_tapes, show (1 : Fin 2) ≠ 0 by decide, if_false, zr_scr]
    rw [zr_fieldsTape_snoc']
    set o := fieldOffset pre pre.length
    by_cases hin : s + 1 + (o : ℤ) ≤ q ∧ q < s + 1 + o + u.length
    · rw [if_pos hin, if_neg (by omega), zr_fieldsTape_end pre _ (by omega)]
    · rw [if_neg hin]
      by_cases hq : q ≤ s
      · rw [if_pos hq, if_pos hq]
      · rw [if_neg hq, if_neg hq]
        by_cases hlt : q - (s + 1) < o
        · rw [if_pos hlt]
        · rw [if_neg hlt, zr_fieldsTape_end pre _ (by omega), FinTM.bufferTape_eq,
            if_pos (by omega), List.getElem?_eq_none (by omega)]

/-- **Each field of the scratch layout is a delimited word**, the cell before the layout blank. -/
private lemma zr_scr_word {k : ℕ} (σ : ℤ → Option (ZoneSym k)) (s : ℤ) (hσ : σ s = none)
    (ws : List (List (ZoneSym k))) (m : ℕ) (hm : m < ws.length) :
    ∀ q : ℤ, -1 ≤ q → q ≤ (ws[m].length : ℤ) →
      zr_scr σ s ws (s + 1 + fieldOffset ws m + q) = FinTM.bufferTape ws[m] q := by
  intro q h1 h2
  simp only [zr_scr]
  split_ifs with h
  · have hq : q = -1 := by omega
    rw [show s + 1 + (fieldOffset ws m : ℤ) + q = s by omega, hσ, hq, FinTM.bufferTape_left]
  · rw [show s + 1 + (fieldOffset ws m : ℤ) + q - (s + 1) = fieldOffset ws m + q by ring]
    exact fieldsTape_field ws m hm q h1 h2

/-- **A scratch field read at its offset.** -/
private lemma zr_scr_at {k : ℕ} {σ : ℤ → Option (ZoneSym k)} {s : ℤ} (hσ : σ s = none)
    (ws : List (List (ZoneSym k))) (m : ℕ) (hm : m < ws.length) (b : ℤ)
    (hb : b = s + 1 + fieldOffset ws m) (q : ℤ) (h1 : -1 ≤ q) (h2 : q ≤ (ws[m].length : ℤ)) :
    zr_scr σ s ws (b + q) = FinTM.bufferTape ws[m] q := by
  subst hb
  exact zr_scr_word σ s hσ ws m hm q h1 h2

/-- The donor's column: zone `i`'s track-`t` slots, as scratch cells. -/
private lemma zr_col_zone {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : ℕ)
    (hi : i < ℓ) (p : ℕ) :
    (zr_col t (zr_rfield z (i + 1)))[p]? =
      if p < zoneCapacity i then some (zr_enc ((z t).right ⟨i, hi⟩)[p]?) else none := by
  have hf : zr_rfield z (i + 1) = zoneCells true z ⟨i, hi⟩ := by
    rw [zr_rfield, if_neg (by omega), dif_pos (by simpa using hi)]
    rfl
  rw [hf, zr_col, zoneCells_eq, List.getElem?_map, List.getElem?_map]
  by_cases hp : p < zoneCapacity i
  · rw [List.getElem?_range hp, if_pos hp, Option.map_some, Option.map_some, zoneSlotOf_inr,
      ZoneContents.words_true]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hp), if_neg hp]
    rfl

/-- A pinned step's endpoint pin, time and box restated by equalities and box inclusions. -/
private lemma zr_PinStep_congr {k : ℕ} {S J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X : Set (Option S)} {C : Contract M e X J x}
    {V : J → Prop} {T₁ T₂ T₂' : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ p₂' : J → Fin 2 → ℤ}
    {τ τ' : J → ℕ} {L U L' U' : J → Fin 2 → ℤ} (h : zr_PinStep C V T₁ T₂ p₁ p₂ τ L U)
    (hT : ∀ j, V j → T₂ j = T₂' j) (hp : ∀ j, V j → p₂ j = p₂' j) (hτ : ∀ j, V j → τ j = τ' j)
    (hL : ∀ j, V j → ∀ i, L' j i ≤ L j i) (hU : ∀ j, V j → ∀ i, U j i ≤ U' j i) :
    zr_PinStep C V T₁ T₂' p₁ p₂' τ' L' U' := by
  refine ⟨h.1, fun j d hV hd => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.2 j d hV hd
  refine ⟨h1, ⟨(h2.1).trans (hT j hV), (h2.2).trans (hp j hV)⟩, h3, h4, h5.trans (hτ j hV),
    fun i => ⟨(hL j hV i).trans (h6 i).1, (h6 i).2.trans (hU j hV i)⟩⟩

/-- **The seam of a pinned chain**: the next part's precondition holds at the renamed endpoint
of a pinned step whose endpoint pin is the next part's start pin. -/
private lemma zr_pin_hlink {k : ℕ} {S₁ S₂ J : Type} {x : List (ZoneSym k)}
    {M₁ : MultiTapeTM 2 (ZoneSym k) S₁} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₁ : S₁}
    {X₁ : Set (Option S₁)} {e₂ : S₂} {X₂ : Set (Option S₂)} {C₁ : Contract M₁ e₁ X₁ J x}
    {C₂ : Contract M₂ e₂ X₂ J x} {V : J → Prop}
    {T₁ T₂ T₃ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ p₃ : J → Fin 2 → ℤ}
    {τ₁ τ₂ : J → ℕ} {L₁ U₁ L₂ U₂ : J → Fin 2 → ℤ} (h₁ : zr_PinStep C₁ V T₁ T₂ p₁ p₂ τ₁ L₁ U₁)
    (h₂ : zr_PinStep C₂ V T₂ T₃ p₂ p₃ τ₂ L₂ U₂) :
    ∀ j d, d.state = some e₁ → C₁.pre j d → C₂.pre j ((C₁.post j d).mapState fun _ => e₂) := by
  intro j d _ hp
  obtain ⟨hV, hd⟩ := h₁.1 j d hp
  exact (h₂.2 j _ hV (zr_pinned_mapState _ (h₁.2 j d hV hd).2.1)).1

/-- Pinned steps in one box compose in that box. -/
private lemma zr_PinStep_seq' {k : ℕ} {S₁ S₂ J : Type} [DecidableEq S₁] {x : List (ZoneSym k)}
    {M₁ : MultiTapeTM 2 (ZoneSym k) S₁} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₁ d₁ : S₁}
    {e₂ : S₂} {X₂ : Set (Option S₂)} {C₁ : Contract M₁ e₁ {some d₁} J x}
    {C₂ : Contract M₂ e₂ X₂ J x}
    {T₁ T₂ T₃ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ p₃ : J → Fin 2 → ℤ}
    {τ₁ τ₂ : J → ℕ} {L U : J → Fin 2 → ℤ} {V : J → Prop}
    (h₁ : zr_PinStep C₁ V T₁ T₂ p₁ p₂ τ₁ L U) (h₂ : zr_PinStep C₂ V T₂ T₃ p₂ p₃ τ₂ L U)
    (hl : ∀ j d, d.state = some e₁ → C₁.pre j d →
      C₂.pre j ((C₁.post j d).mapState fun _ => e₂)) :
    zr_PinStep (C₁.seq C₂ (fun j => j) hl) V T₁ T₃ p₁ p₃ (fun j => τ₁ j + 1 + τ₂ j) L U :=
  zr_PinStep_congr (zr_PinStep_seq h₁ h₂ hl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => le_min le_rfl le_rfl) (fun _ _ _ => max_le le_rfl le_rfl)

/-- A pinned step survives an exit-set re-wrap. -/
private lemma zr_PinStep_exits {k : ℕ} {S J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X X' : Set (Option S)} {R : Contract M e X J x}
    {hX : X = X'} {V : J → Prop} {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₁ p₂ : J → Fin 2 → ℤ} {τ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (h : zr_PinStep R V T₁ T₂ p₁ p₂ τ L U) :
    zr_PinStep (zr_exitsContract R X' hX) V T₁ T₂ p₁ p₂ τ L U := by
  refine ⟨fun j d hd => h.1 j d (by rwa [zr_exitsContract, Contract.ofSegment_pre] at hd),
    fun j d hV hd => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.2 j d hV hd
  simp only [zr_exitsContract, Contract.ofSegment_pre, Contract.ofSegment_post,
    Contract.ofSegment_time, Contract.ofSegment_lo, Contract.ofSegment_hi]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **A pinned segment**: a contract with one live exit, and its pinned step. -/
private structure zr_PinSeg {k : ℕ} {S J : Type} (x : List (ZoneSym k))
    (M : MultiTapeTM 2 (ZoneSym k) S) (e d : S) (V : J → Prop)
    (T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)) (p₁ p₂ : J → Fin 2 → ℤ) (τ : J → ℕ)
    (L U : J → Fin 2 → ℤ) where
  /-- the contract -/
  C : Contract M e {some d} J x
  /-- its pinned step -/
  step : zr_PinStep C V T₁ T₂ p₁ p₂ τ L U

/-- A pinned segment from a pinned step: its endpoint pin restated, its box widened. -/
private def zr_seg {k : ℕ} {S J : Type} {x : List (ZoneSym k)} {M : MultiTapeTM 2 (ZoneSym k) S}
    {e d : S} {C : Contract M e {some d} J x} {V : J → Prop}
    {T₁ T₂ T₂' : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ p₂' : J → Fin 2 → ℤ} {τ : J → ℕ}
    {L U L' U' : J → Fin 2 → ℤ} (h : zr_PinStep C V T₁ T₂ p₁ p₂ τ L U)
    (hT : ∀ j, V j → T₂ j = T₂' j)
    (hx : ∀ j, V j → p₂ j = p₂' j ∧ (∀ i, L' j i ≤ L j i) ∧ ∀ i, U j i ≤ U' j i) :
    zr_PinSeg x M e d V T₁ T₂' p₁ p₂' τ L' U' :=
  ⟨C, zr_PinStep_congr h hT (fun j hj => (hx j hj).1) (fun _ _ => rfl) (fun j hj => (hx j hj).2.1)
    (fun j hj => (hx j hj).2.2)⟩

/-- **Pinned segments compose** in one box, re-wrapped to the second one's live exit. -/
private def zr_segSeq {k : ℕ} {S₁ S₂ J : Type} [DecidableEq S₁] {x : List (ZoneSym k)}
    {M₁ : MultiTapeTM 2 (ZoneSym k) S₁} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₁ d₁ : S₁}
    {e₂ d₂ : S₂} {V : J → Prop} {T₁ T₂ T₃ : J → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₁ p₂ p₃ : J → Fin 2 → ℤ} {τ₁ τ₂ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (A : zr_PinSeg x M₁ e₁ d₁ V T₁ T₂ p₁ p₂ τ₁ L U)
    (B : zr_PinSeg x M₂ e₂ d₂ V T₂ T₃ p₂ p₃ τ₂ L U) :
    zr_PinSeg x (seamCompTM M₁ d₁ M₂ e₂) (Sum.inl e₁) (Sum.inr d₂) V T₁ T₃ p₁ p₃
      (fun j => τ₁ j + 1 + τ₂ j) L U :=
  ⟨zr_singletonContract (A.C.seq B.C (fun j => j) (zr_pin_hlink A.step B.step)) (Sum.inr d₂),
    zr_PinStep_exits (zr_PinStep_seq' A.step B.step _)⟩

/-- The index of one level's column move: the data, the level, and scratch's tape and head at
the start. -/
private structure zr_Ix (k : ℕ) where
  /-- the data -/
  D : ZoneData k
  /-- the level -/
  i : ℕ
  /-- the start's scratch tape -/
  σ : ℤ → Option (ZoneSym k)
  /-- the start's scratch head -/
  s : ℤ

/-- A valid index for the right inward shift: `1 ≤ i < ℓ`, track `t`'s right zone `i - 1`
empty (its innermost slot `⊠`), and scratch blank from its head on. -/
private def zr_inV {k : ℕ} (t : Fin k) (J : zr_Ix k) : Prop :=
  1 ≤ J.i ∧ J.i < J.D.1 ∧
    (zonedTape J.D.2 (zoneStart (J.i - 1))).map (zoneSlotOf t) = some none ∧
    ∀ r, J.s ≤ r → J.σ r = none

/-- At a valid index the receiving zone is empty on track `t`. -/
private lemma zr_inV_empty {k : ℕ} {t : Fin k} {J : zr_Ix k} (hV : zr_inV t J) :
    (J.D.2 t).right ⟨J.i - 1, by have := hV.2.1; omega⟩ = [] := by
  have h := (zr_inner_empty_iff true J.D.2 ⟨J.i - 1, by have := hV.2.1; omega⟩ t).mp
  rw [zr_zonePos, if_pos rfl, Nat.add_zero, ZoneContents.words_true] at h
  exact h hV.2.2.1

/-- The half-capacity `2^(i-1)` of the receiving zone. -/
private abbrev zr_hh {k : ℕ} (J : zr_Ix k) : ℕ := 2 ^ (J.i - 1)

/-- The donor's track-`t` column, as scratch cells. -/
private abbrev zr_cD {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  zr_col t (zr_rfield J.D.2 (J.i + 1))

/-- The receiver's new slots: the donor column's first `2^(i-1)` cells. -/
private abbrev zr_W1 {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cD t J).take (zr_hh J)

/-- The donor's new slots up to its last `2^(i-1)`: its column from offset `2^(i-1)` on. -/
private abbrev zr_V {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cD t J).drop (zr_hh J)

/-- The scratch pieces the two cuts leave behind. -/
private abbrev zr_J1 {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cD t J).drop (zr_hh J + 1)

/-- The scratch pieces the two cuts leave behind. -/
private abbrev zr_J2 {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cD t J).take (zr_hh J - 1)

/-- The lengths at a valid index. -/
private lemma zr_inV_lengths {k : ℕ} {t : Fin k} {J : zr_Ix k} (hV : zr_inV t J) :
    (zr_rfield J.D.2 J.i).length = 2 * zr_hh J ∧
      (zr_rfield J.D.2 (J.i - 1)).length = zr_hh J ∧
      (zr_rfield J.D.2 (J.i + 1)).length = 4 * zr_hh J ∧ (zr_cD t J).length = 4 * zr_hh J ∧
      (zr_W1 t J).length = zr_hh J ∧ (zr_V t J).length = 3 * zr_hh J ∧
      (zr_J1 t J).length = 3 * zr_hh J - 1 ∧ (zr_J2 t J).length = zr_hh J - 1 ∧
      0 < zr_hh J := by
  obtain ⟨h1, h2, -, -⟩ := hV
  have e1 := zr_rfield_length J.D.2 J.i (by omega)
  have e2 := zr_rfield_length J.D.2 (J.i - 1) (by omega)
  have e3 := zr_rfield_length J.D.2 (J.i + 1) (by omega)
  have p1 : (2 : ℕ) ^ J.i = 2 * 2 ^ (J.i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have p2 : (2 : ℕ) ^ (J.i + 1) = 4 * 2 ^ (J.i - 1) := by
    rw [show J.i + 1 = (J.i - 1) + 2 by omega, pow_add]
    ring
  have hpos : 0 < 2 ^ (J.i - 1) := Nat.two_pow_pos _
  simp only [zr_hh, zr_cD, zr_W1, zr_V, zr_J1, zr_J2, zr_col, List.length_map,
    List.length_take, List.length_drop, e1, e2, e3, p1, p2, true_and]
  omega

/-- The field starts at a valid index: the field two inward, the receiver, the donor. -/
private lemma zr_inV_starts {k : ℕ} {t : Fin k} {J : zr_Ix k} (hV : zr_inV t J) :
    zr_rstart J.i = zr_rstart (J.i - 1) + zr_hh J + 1 ∧
      zr_rstart (J.i + 1) = zr_rstart J.i + 2 * zr_hh J + 1 ∧
      zr_rstart J.i = zoneStart (J.i - 1) ∧ zr_rstart (J.i + 1) = zoneStart J.i ∧
      0 ≤ zr_rstart (J.i - 1) := by
  obtain ⟨h1, -, -, -⟩ := hV
  have s1 := zr_rstart_succ (J.i - 1)
  have s2 := zr_rstart_succ J.i
  rw [show J.i - 1 + 1 = J.i by omega] at s1
  have p1 : (2 : ℕ) ^ J.i = 2 * 2 ^ (J.i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨s1, ?_, ?_, ?_, ?_⟩
  · rw [s2, p1]
    push_cast
    ring
  · rw [zr_rstart, if_neg (by omega)]
  · rw [zr_rstart, if_neg (by omega), Nat.add_sub_cancel]
  · rw [zr_rstart]
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _

/-- Tape `0` after a mapped copy onto it at `a` of the word `w`. -/
private abbrev zr_wr0 {k : ℕ} {Δ : Type} (extract : ZoneSym k → Δ)
    (merge : Option (ZoneSym k) → Δ → ZoneSym k) (w : List (ZoneSym k))
    (A : ℤ → Option (ZoneSym k)) (a : ℤ) : ℤ → Option (ZoneSym k) := fun q =>
  if a ≤ q ∧ q < a + w.length then
    (FinTM.bufferTape w (q - a)).map fun γ => merge (A q) (extract γ)
  else A q

/-- A mapped copy onto tape `0` rewrites tape `0` only. -/
private lemma zr_copy0 {k : ℕ} {Δ : Type} (extract : ZoneSym k → Δ)
    (merge : Option (ZoneSym k) → Δ → ZoneSym k) (w : List (ZoneSym k))
    (A B : ℤ → Option (ZoneSym k)) (a b : ℤ) :
    zr_copyTapes 0 extract merge w (zr_tapes A B) (zr_heads a b) =
      zr_tapes (zr_wr0 extract merge w A a) B := by
  funext j q
  by_cases hj : j = 0
  · subst hj
    simp only [zr_copyTapes, zr_tapes, zr_heads, true_and, if_true, zr_wr0]
  · simp only [zr_copyTapes, zr_tapes, zr_heads, hj, false_and, if_false]

/-- Left of the copy's start, tape `0` is kept. -/
private lemma zr_wr0_lt {k : ℕ} {Δ : Type} (extract : ZoneSym k → Δ)
    (merge : Option (ZoneSym k) → Δ → ZoneSym k) (w : List (ZoneSym k))
    (A : ℤ → Option (ZoneSym k)) {a q : ℤ} (hq : q < a) :
    zr_wr0 extract merge w A a q = A q := by
  simp only [zr_wr0]
  rw [if_neg (by omega)]

/-- Tape `0` after the donor's track-`t` slots are cleared. -/
private abbrev zr_inA1 {k : ℕ} (t : Fin k) (J : zr_Ix k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (fun c _ => zoneSlotSet t c none) (zr_cD t J) (zonedTape J.D.2)
    (zr_rstart (J.i + 1))

/-- Tape `0` after the donor's write from offset `2^(i-1)` on. -/
private abbrev zr_inA2 {k : ℕ} (t : Fin k) (J : zr_Ix k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (zoneSlotSet t) (zr_V t J) (zr_inA1 t J) (zr_rstart (J.i + 1))

/-- Left of the donor, the cleared tape is the zoned tape. -/
private lemma zr_inA1_lt {k : ℕ} {t : Fin k} {J : zr_Ix k} {q : ℤ}
    (hq : q < zr_rstart (J.i + 1)) : zr_inA1 t J q = zonedTape J.D.2 q :=
  zr_wr0_lt _ _ _ _ hq

/-- Left of the donor, the donor-written tape is the zoned tape. -/
private lemma zr_inA2_lt {k : ℕ} {t : Fin k} {J : zr_Ix k} {q : ℤ}
    (hq : q < zr_rstart (J.i + 1)) : zr_inA2 t J q = zonedTape J.D.2 q := by
  rw [zr_inA2, zr_wr0_lt _ _ _ _ hq, zr_inA1_lt hq]

/-- Setting a track's slot twice keeps the second. -/
private lemma zr_slotSet_slotSet {k : ℕ} (t : Fin k) (c : Option (ZoneSym k))
    (v w : Option (Option Bool)) :
    zoneSlotSet t (some (zoneSlotSet t c v)) w = zoneSlotSet t c w := by
  simp only [zoneSlotSet_eq, zoneCellOfCell_inr, Function.update_idem]

/-- **The shift's tape-`0` writes**: clearing the donor's track-`t` slots, writing them from
the donor column's offset `2^(i-1)` on, and writing the receiver's first `2^(i-1)` slots from the
column's first cells gives the zoned tape of the shifted track. -/
private lemma zr_inA3 {k : ℕ} {t : Fin k} {J : zr_Ix k} (hV : zr_inV t J) :
    zr_wr0 (zoneSlotOf t) (zoneSlotSet t) (zr_W1 t J) (zr_inA2 t J) (zr_rstart J.i) =
      zonedTape (Function.update J.D.2 t (zoneShiftIn true J.i (J.D.2 t))) := by
  have hl := zr_inV_lengths hV
  have hs := zr_inV_starts hV
  have h1 := hV.1
  have h2 := hV.2.1
  have hcap : zoneCapacity J.i = 4 * zr_hh J := by
    rw [zoneCapacity_eq, show (2 : ℕ) ^ J.i = 2 * zr_hh J by
      rw [zr_hh, ← pow_succ']
      congr 1
      omega]
    ring
  have hle : ((J.D.2 t).right ⟨J.i, h2⟩).length ≤ zoneCapacity J.i := (J.D.2 t).right_le _
  have hh : (2 : ℕ) ^ (J.i - 1) = zr_hh J := rfl
  funext q
  rw [zr_shiftIn_tape J.D.2 t J.i h1 h2 (zr_inV_empty hV) q]
  obtain ⟨l1, l2, l0, l3, l4, l5, l6, l7, l8⟩ := hl
  obtain ⟨s1, s2, s3, s4, s5⟩ := hs
  simp only [zr_wr0, zr_inA2, zr_inA1]
  by_cases hR : zr_rstart J.i ≤ q ∧ q < zr_rstart J.i + zr_hh J
  · obtain ⟨p, hp⟩ : ∃ p : ℕ, q - zr_rstart J.i = p :=
      ⟨(q - zr_rstart J.i).toNat, by omega⟩
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), ← s3, hp,
      FinTM.bufferTape_nat, List.getElem?_take, if_pos (by omega), zr_col_zone J.D.2 t J.i h2 p,
      if_pos (by omega), Option.map_some, zoneSlotOf_inr, Int.toNat_natCast]
  by_cases hD : zr_rstart (J.i + 1) ≤ q ∧ q < zr_rstart (J.i + 1) + 4 * zr_hh J
  swap
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  obtain ⟨p, hp⟩ : ∃ p : ℕ, q - zr_rstart (J.i + 1) = p :=
    ⟨(q - zr_rstart (J.i + 1)).toNat, by omega⟩
  by_cases hD1 : p < 3 * zr_hh J
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_pos (by omega), ← s4, hp, FinTM.bufferTape_nat, FinTM.bufferTape_nat, List.getElem?_drop,
      zr_col_zone J.D.2 t J.i h2 (zr_hh J + p), zr_col_zone J.D.2 t J.i h2 p, if_pos (by omega),
      if_pos (by omega), Option.map_some, Option.map_some, zoneSlotOf_inr, zr_slotSet_slotSet,
      Int.toNat_natCast]
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_pos (by omega), ← s4, hp, FinTM.bufferTape_nat, zr_col_zone J.D.2 t J.i h2 p,
      if_pos (by omega), Option.map_some, Int.toNat_natCast, List.getElem?_eq_none (by omega)]

/-- Tape `0` after the shift: the zoned tape of the shifted track. -/
private abbrev zr_inZ {k : ℕ} (t : Fin k) (J : zr_Ix k) : ℤ → Option (ZoneSym k) :=
  zonedTape (Function.update J.D.2 t (zoneShiftIn true J.i (J.D.2 t)))

/-- Head vectors compare by their two entries. -/
private lemma zr_heads_le {f g : Fin 2 → ℤ} (h0 : f 0 ≤ g 0) (h1 : f 1 ≤ g 1) :
    ∀ j, f j ≤ g j := by
  intro j
  by_cases hj : j = 0
  · subst hj
    exact h0
  · have hj1 : j = 1 := by omega
    subst hj1
    exact h1

/-- The second of two heads. -/
private lemma zr_heads_one (a b : ℤ) : zr_heads a b 1 = b := rfl

/-- A head vector is the pair of its two entries. -/
private lemma zr_heads_ext {f : Fin 2 → ℤ} {a b : ℤ} (h0 : f 0 = a) (h1 : f 1 = b) :
    f = zr_heads a b := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simpa only [zr_heads, if_true] using h0
  · have hj1 : j = 1 := by omega
    subst hj1
    simpa only [zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false] using h1

/-- **A right-layout field read at its start.** -/
private lemma zr_rfield_at {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) (hm : m ≤ ℓ) (b : ℤ)
    (hb : b = zr_rstart m) (q : ℤ) (h1 : -1 ≤ q) (h2 : q ≤ ((zr_rfield z m).length : ℤ)) :
    zonedTape z (b + q) = FinTM.bufferTape (zr_rfield z m) q := by
  subst hb
  exact zr_rfield_word z m hm q h1 h2

/-- The right inward shift's head box: the zoned head from one cell left of the field two
inward to the donor's end, scratch over its work area. -/
private abbrev zr_inL {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_rstart (J.i - 1) - 1) J.s

/-- The right inward shift's head box, its upper corner. -/
private abbrev zr_inU {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_rstart (J.i + 1) + 4 * zr_hh J) (J.s + 8 * zr_hh J + 2)

/-- The right inward shift's tape stages: tape `0`, and the scratch layout `L`. -/
private abbrev zr_inT {k : ℕ} (J : zr_Ix k) (A : ℤ → Option (ZoneSym k))
    (L : List (List (ZoneSym k))) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes A (zr_scr J.σ J.s L)

/-- **The right inward shift at level `i`**, as one pinned segment: the thirty steps of the
column move in sequence. -/
private def zr_inSeg {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ (zr_inV t) (fun J => zr_inT J (zonedTape J.D.2) [])
      (fun J => zr_inT J (zr_inZ t J) []) (fun J => zr_heads (zr_rstart J.i) J.s)
      (fun J => zr_heads (zr_rstart J.i) J.s) _ zr_inL zr_inU from
  -- step 1: skip the receiver, to the donor
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_rfield J.D.2 J.i)
        (fun J => zr_inT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_rstart J.i) J.s)
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zonedTape J.D.2) (zr_rstart J.i + q) = _
          exact zr_rfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 2: scratch one cell right, to the work area
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_inT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_rstart (J.i + 1)) J.s))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 3: copy the donor's column onto scratch
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_rfield J.D.2 (J.i + 1))
        (fun J => zr_inT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zonedTape J.D.2) (zr_rstart (J.i + 1) + q) = _
          exact zr_rfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_copy _ _ _ _ [] _ _ _ _
          (by rw [List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 4: skip the column
  zr_segSeq (zr_seg (zr_pinSkip_step _ 1 (fun J => zr_cD t J)
        (fun J => zr_inT J (zonedTape J.D.2) [zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_cD t J]
            (J.s + 1 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_cD t J] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 5: copy the donor's column again
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_rfield J.D.2 (J.i + 1))
        (fun J => zr_inT J (zonedTape J.D.2) [zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 4 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zonedTape J.D.2) (zr_rstart (J.i + 1) + q) = _
          exact zr_rfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_copy _ _ _ _ [zr_cD t J] _ _ _ _
          (by rw [List.length_singleton, fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 6: clear the donor's track-`t` slots by the second column
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (fun c _ => zoneSlotSet t c none)
        (fun J => zr_cD t J)
        (fun J => zr_inT J (zonedTape J.D.2) [zr_cD t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 4 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_cD t J, zr_cD t J]
            (J.s + 4 * zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_cD t J, zr_cD t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 7: back over the first column
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_cD t J)
        (fun J => zr_inT J (zr_inA1 t J) [zr_cD t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 4 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_cD t J, zr_cD t J]
            (J.s + 4 * zr_hh J + 2 - ((zr_cD t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_cD t J, zr_cD t J] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 8: scratch one cell left, to its start
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_inT J (zr_inA1 t J) [zr_cD t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 9: back over the receiver
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_rfield J.D.2 J.i)
        (fun J => zr_inT J (zr_inA1 t J) [zr_cD t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) J.s)
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zr_inA1 t J) (zr_rstart (J.i + 1) - ((zr_rfield J.D.2 J.i).length : ℤ) - 1 + q) = _
          have hq' : q ≤ ((zr_rfield J.D.2 J.i).length : ℤ) := h1
          rw [zr_inA1_lt (by omega)]
          exact zr_rfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 10: back over the field two inward
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_rfield J.D.2 (J.i - 1))
        (fun J => zr_inT J (zr_inA1 t J) [zr_cD t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart J.i) J.s)
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zr_inA1 t J) (zr_rstart J.i - ((zr_rfield J.D.2 (J.i - 1)).length : ℤ) - 1 + q) = _
          have hq' : q ≤ ((zr_rfield J.D.2 (J.i - 1)).length : ℤ) := h1
          rw [zr_inA1_lt (by omega)]
          exact zr_rfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 11: walk over the field two inward, scratch to the first column's cut
  zr_segSeq (zr_seg (zr_pinWalk_step _ 0 (fun J => zr_rfield J.D.2 (J.i - 1))
        (fun J => zr_inT J (zr_inA1 t J) [zr_cD t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i - 1)) J.s)
        fun J hV q hq => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zr_inA1 t J) (zr_rstart (J.i - 1) + q) = _
          have hq' : q ≤ (zr_rfield J.D.2 (J.i - 1)).length := hq
          rw [zr_inA1_lt (by omega)]
          exact zr_rfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) (by exact_mod_cast hq))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 12: cut the first column after its first `2^(i-1)` cells
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (some none)
        (fun J => zr_inT J (zr_inA1 t J) [zr_cD t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + zr_hh J + 1)))
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_split _ _ _ _ [] [zr_cD t J] (zr_cD t J) (zr_hh J) (zr_hh J + 1)
          (by omega) (by omega)
          (by rw [zr_heads_one, List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 13: skip the first column's rest
  zr_segSeq (zr_seg (zr_pinSkip_step _ 1 (fun J => zr_J1 t J)
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J, zr_J1 t J, zr_cD t J]
            (J.s + zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J, zr_J1 t J, zr_cD t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 14: scratch one cell left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 4 * zr_hh J + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 15: scratch one cell left, `2^(i-1)` cells before the second cut
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 4 * zr_hh J + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 16: back over the field two inward
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_rfield J.D.2 (J.i - 1))
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 4 * zr_hh J))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zr_inA1 t J) (zr_rstart J.i - ((zr_rfield J.D.2 (J.i - 1)).length : ℤ) - 1 + q) = _
          have hq' : q ≤ ((zr_rfield J.D.2 (J.i - 1)).length : ℤ) := h1
          rw [zr_inA1_lt (by omega)]
          exact zr_rfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 17: walk over the field two inward, scratch to the second column's cut
  zr_segSeq (zr_seg (zr_pinWalk_step _ 0 (fun J => zr_rfield J.D.2 (J.i - 1))
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart (J.i - 1)) (J.s + 4 * zr_hh J))
        fun J hV q hq => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zr_inA1 t J) (zr_rstart (J.i - 1) + q) = _
          have hq' : q ≤ (zr_rfield J.D.2 (J.i - 1)).length := hq
          rw [zr_inA1_lt (by omega)]
          exact zr_rfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) (by exact_mod_cast hq))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 18: cut the second column before its cell `2^(i-1)`
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (some none)
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_cD t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 5 * zr_hh J + 1)))
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_split _ _ _ _ [zr_W1 t J, zr_J1 t J] [] (zr_cD t J) (zr_hh J - 1) (zr_hh J)
          (by omega) (by omega)
          (by rw [zr_heads_one, List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 19: skip the receiver, to the donor
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_rfield J.D.2 J.i)
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_J2 t J, zr_V t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 5 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zr_inA1 t J) (zr_rstart J.i + q) = _
          have hq' : q ≤ ((zr_rfield J.D.2 J.i).length : ℤ) := h1
          rw [zr_inA1_lt (by omega)]
          exact zr_rfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 20: write the donor's track-`t` slots from the second column's rest
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (zoneSlotSet t)
        (fun J => zr_V t J)
        (fun J => zr_inT J (zr_inA1 t J) [zr_W1 t J, zr_J1 t J, zr_J2 t J, zr_V t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 5 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J, zr_J1 t J, zr_J2 t J, zr_V t J]
            (J.s + 5 * zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J, zr_J1 t J, zr_J2 t J, zr_V t J] 3 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 21: clear the second column's rest
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_V t J)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J, zr_J1 t J, zr_J2 t J, zr_V t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 5 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J, zr_J1 t J, zr_J2 t J, zr_V t J]
            (J.s + 5 * zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J, zr_J1 t J, zr_J2 t J, zr_V t J] 3 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_clear _ _ _ [zr_W1 t J, zr_J1 t J, zr_J2 t J] _ _
          (by rw [zr_heads_one, List.length_cons, List.length_cons, List.length_singleton,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 22: back over the second column's head
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_J2 t J)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J, zr_J1 t J, zr_J2 t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 5 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J, zr_J1 t J, zr_J2 t J]
            (J.s + 5 * zr_hh J + 2 - ((zr_J2 t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J, zr_J1 t J, zr_J2 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 23: clear the second column's head
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_J2 t J)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J, zr_J1 t J, zr_J2 t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 4 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J, zr_J1 t J, zr_J2 t J]
            (J.s + 4 * zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J, zr_J1 t J, zr_J2 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_clear _ _ _ [zr_W1 t J, zr_J1 t J] _ _
          (by rw [zr_heads_one, List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 24: back over the first column's rest
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_J1 t J)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J, zr_J1 t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 4 * zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J, zr_J1 t J]
            (J.s + 4 * zr_hh J + 2 - ((zr_J1 t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J, zr_J1 t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 25: clear the first column's rest
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_J1 t J)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J, zr_J1 t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J, zr_J1 t J]
            (J.s + zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J, zr_J1 t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_clear _ _ _ [zr_W1 t J] _ _
          (by rw [zr_heads_one, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 26: back over the receiver's new slots
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_W1 t J)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J]
            (J.s + zr_hh J + 2 - ((zr_W1 t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 27: back over the receiver, to its start
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_rfield J.D.2 J.i)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J])
        (fun J => zr_heads (zr_rstart (J.i + 1)) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          have := zr_inV_starts hV
          show (zr_inA2 t J) (zr_rstart (J.i + 1) - ((zr_rfield J.D.2 J.i).length : ℤ) - 1 + q) = _
          have hq' : q ≤ ((zr_rfield J.D.2 J.i).length : ℤ) := h1
          rw [zr_inA2_lt (by omega)]
          exact zr_rfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _ (by omega) _
            (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 28: write the receiver's track-`t` slots
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (zoneSlotSet t)
        (fun J => zr_W1 t J)
        (fun J => zr_inT J (zr_inA2 t J) [zr_W1 t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J]
            (J.s + 1 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => (zr_copy0 _ _ _ _ _ _ _).trans
        (congrArg (fun A => zr_tapes A _) (zr_inA3 hV)))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 29: clear the receiver's new slots
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_W1 t J)
        (fun J => zr_inT J (zr_inZ t J) [zr_W1 t J])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_inV_lengths hV
          show zr_scr J.σ J.s [zr_W1 t J]
            (J.s + 1 + q) = _
          exact zr_scr_at (hV.2.2.2 _ le_rfl)
            [zr_W1 t J] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_inV_lengths hV
        exact zr_scr_clear _ _ _ [] _ _
          (by rw [zr_heads_one, List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_inL, zr_inU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 30: scratch one cell left, to its start
  (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_inT J (zr_inZ t J) [])
        (fun J => zr_heads (zr_rstart J.i) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        have := zr_inV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_inL, zr_inU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega))

/-- The left layout's field `m`, read left to right: the swapped contents' right field `m`,
reversed (the home at `m = 0`, left zone `m - 1` after it). -/
private def zr_lfield {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) : List (ZoneSym k) :=
  (zr_rfield (fun t => (z t).swap) m).reverse

/-- The left layout's field `m` starts at the mirror of the right field `m`'s last cell. -/
private def zr_lstart (m : ℕ) : ℤ := -(zr_rstart m + ((2 ^ m : ℕ) : ℤ) - 1)

/-- Left field `m` has `2^m` cells. -/
private lemma zr_lfield_length {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) (hm : m ≤ ℓ) :
    (zr_lfield z m).length = 2 ^ m := by
  rw [zr_lfield, List.length_reverse, zr_rfield_length _ m hm]

/-- Left field `m` ends one separator before left field `m - 1`'s start: the next field inward
starts `2^(m+1) + 1` cells after field `m + 1`'s. -/
private lemma zr_lstart_succ (m : ℕ) :
    zr_lstart m = zr_lstart (m + 1) + ((2 ^ (m + 1) : ℕ) : ℤ) + 1 := by
  rw [zr_lstart, zr_lstart, zr_rstart_succ, pow_succ]
  push_cast
  ring

/-- A reversed word, read at `q`, is the word read at the mirrored position. -/
private lemma zr_bufferTape_reverse {α : Type} (w : List α) (q : ℤ) (h1 : -1 ≤ q)
    (h2 : q ≤ w.length) : FinTM.bufferTape w.reverse q = FinTM.bufferTape w (w.length - 1 - q) := by
  rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq]
  split_ifs with ha hb hb
  · rw [List.getElem?_reverse (by omega)]
    congr 1
    omega
  · exact List.getElem?_eq_none (by rw [List.length_reverse]; omega)
  · exact (List.getElem?_eq_none (by omega)).symm
  · omega

/-- **Each field of the left layout is a delimited word** on the zoned tape: the mirror of the
swapped contents' right field. -/
private lemma zr_lfield_at {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) (hm : m ≤ ℓ) (b : ℤ)
    (hb : b = zr_lstart m) (q : ℤ) (h1 : -1 ≤ q) (h2 : q ≤ ((zr_lfield z m).length : ℤ)) :
    zonedTape z (b + q) = FinTM.bufferTape (zr_lfield z m) q := by
  subst hb
  have hl := zr_rfield_length (fun t => (z t).swap) m hm
  rw [zr_lfield, List.length_reverse] at h2
  have hmir := zr_mirror_tape z (-(zr_lstart m + q))
  rw [neg_neg] at hmir
  rw [← hmir, zr_lfield, zr_bufferTape_reverse _ q h1 h2,
    show -(zr_lstart m + q) = zr_rstart m +
      (((zr_rfield (fun t => (z t).swap) m).length : ℤ) - 1 - q) by rw [zr_lstart, hl]; ring]
  exact zr_rfield_at _ m hm _ rfl _ (by omega) (by omega)

/-- **The left outward shift on the zoned tape**, its guard enabled: when track `t`'s left zone
`i - 1` is full and left zone `i` has room for `2^(i-1)` more slots, the shift at level `i`
keeps track `t`'s first `2^(i-1)` slots of zone `i - 1` and clears the rest, and sets zone `i`'s
slots to zone `i - 1`'s last `2^(i-1)` slots followed by zone `i`'s own; every other cell keeps
its contents. Offsets are measured from each zone's inner end. -/
private lemma zr_shiftOut_tape {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : ℕ)
    (hi : 1 ≤ i) (hiℓ : i < ℓ)
    (hf : ((z t).left ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1))
    (hr : ((z t).left ⟨i, hiℓ⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i) (q : ℤ) :
    zonedTape (Function.update z t (zoneShiftOut false i (z t))) q =
      if -((zoneStart (i - 1) : ℤ) + zoneCapacity (i - 1)) < q ∧ q ≤ -(zoneStart (i - 1) : ℤ)
      then
        some (zoneSlotSet t (zonedTape z q)
          (((z t).left ⟨i - 1, by omega⟩).take (2 ^ (i - 1)))[(-q - zoneStart (i - 1)).toNat]?)
      else if -((zoneStart i : ℤ) + zoneCapacity i) < q ∧ q ≤ -(zoneStart i : ℤ) then
        some (zoneSlotSet t (zonedTape z q)
          (((z t).left ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++
            (z t).left ⟨i, hiℓ⟩)[(-q - zoneStart i).toNat]?)
      else zonedTape z q := by
  have hul : ∀ j : Fin ℓ, (zoneShiftOut false i (z t)).left j =
      if j.val = i - 1 then ((z t).left ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
      else if j.val = i then ((z t).left ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++
        (z t).left ⟨i, hiℓ⟩
      else (z t).left j := by
    intro j
    rw [zoneShiftOut_left, if_neg Bool.false_ne_true, zoneShiftOutW_eq, dif_pos ⟨hi, hiℓ⟩,
      if_pos ⟨hf, hr⟩]
  split_ifs with h1 h2
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = -(((zoneStart (i - 1) + p : ℕ) : ℤ)) :=
      ⟨(-q - zoneStart (i - 1)).toNat, by omega⟩
    apply zr_zonedTape_update
    have hs := zr_read_slot false (fun _ => zoneShiftOut false i (z t)) ⟨i - 1, by omega⟩ t p
      (by simp only; omega)
    rw [zr_zonePos, if_neg Bool.false_ne_true] at hs
    rw [hs, ZoneContents.words_false, hul, if_pos rfl]
    congr 2
    push_cast
    omega
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = -(((zoneStart i + p : ℕ) : ℤ)) :=
      ⟨(-q - zoneStart i).toNat, by omega⟩
    apply zr_zonedTape_update
    have hs := zr_read_slot false (fun _ => zoneShiftOut false i (z t)) ⟨i, hiℓ⟩ t p
      (by simp only; omega)
    rw [zr_zonePos, if_neg Bool.false_ne_true] at hs
    rw [hs, ZoneContents.words_false, hul, if_neg (by simp only; omega), if_pos rfl]
    congr 2
    push_cast
    omega
  · apply zr_zonedTape_update_same
    rw [zr_slot_track (z := z) (z' := fun _ => z t) rfl q]
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · rw [zonedTape_of_neg _ hq, zonedTape_of_neg _ hq, zoneCellAt_eq, zoneCellAt_eq]
      cases ho : zoneOwner ℓ (-q).toNat with
      | none => rfl
      | some o =>
        have hm := (Fin.find_eq_some_iff.mp ((zoneOwner_eq ℓ (-q).toNat).symm.trans ho)).1
        simp only [Option.map_some, zoneSlotOf_inr, ZoneContents.words_false, hul]
        split_ifs with ho1 ho2
        · exfalso
          rw [ho1] at hm
          omega
        · exfalso
          rw [ho2] at hm
          omega
        · rfl
    · simp only [zonedTape_zero, Option.map_some, zoneSlotOf_inr, zoneShiftOut_home]
    · rw [zonedTape_of_pos _ hq, zonedTape_of_pos _ hq, zoneCellAt_eq, zoneCellAt_eq]
      simp only [ZoneContents.words_true, zoneShiftOut_right, if_neg Bool.false_ne_true]

/-- Zone contents are determined by their home and their two sides' words. -/
private lemma zr_contents_ext {ℓ : ℕ} {u v : ZoneContents ℓ} (h1 : u.home = v.home)
    (h2 : u.left = v.left) (h3 : u.right = v.right) : u = v := by
  cases u
  cases v
  cases h1
  cases h2
  cases h3
  rfl

/-- **The right inward shift's guard disabled**: a nonempty receiver leaves the track unchanged. -/
private lemma zr_shiftIn_off {ℓ : ℕ} (w : ZoneContents ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i < ℓ)
    (hne : w.right ⟨i - 1, by omega⟩ ≠ []) : zoneShiftIn true i w = w :=
  zr_contents_ext (zoneShiftIn_home true i w) (by
    funext j
    rw [zoneShiftIn_left, if_pos rfl]) (by
    funext j
    rw [zoneShiftIn_right, if_pos rfl, zoneShiftInW_eq, dif_pos ⟨hi, hiℓ⟩, if_neg hne])

/-- **The left outward shift's guard disabled**: without a full zone `i - 1` and room in zone
`i`, the track is unchanged. -/
private lemma zr_shiftOut_off {ℓ : ℕ} (w : ZoneContents ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i < ℓ)
    (hne : ¬ ((w.left ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) ∧
      (w.left ⟨i, hiℓ⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i)) :
    zoneShiftOut false i w = w :=
  zr_contents_ext (zoneShiftOut_home false i w) (by
    funext j
    rw [zoneShiftOut_left, if_neg Bool.false_ne_true, zoneShiftOutW_eq, dif_pos ⟨hi, hiℓ⟩,
      if_neg hne]) (by
    funext j
    rw [zoneShiftOut_right, if_neg Bool.false_ne_true])

/-- Track `t`'s left word at level `m`, empty past the layout. -/
private def zr_lword {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (m : ℕ) :
    List (Option Bool) :=
  if h : m < ℓ then (z t).left ⟨m, h⟩ else []

/-- A valid index for the left outward shift: `1 ≤ i < ℓ`, track `t`'s left zone `i - 1` full,
left zone `i` with room for `2^(i-1)` more slots, and scratch blank from its head on. -/
private def zr_outV {k : ℕ} (t : Fin k) (J : zr_Ix k) : Prop :=
  1 ≤ J.i ∧ J.i < J.D.1 ∧ (zr_lword J.D.2 t (J.i - 1)).length = zoneCapacity (J.i - 1) ∧
    (zr_lword J.D.2 t J.i).length + 2 ^ (J.i - 1) ≤ zoneCapacity J.i ∧
    ∀ r, J.s ≤ r → J.σ r = none

/-- The outer zone's track-`t` column, read left to right, as scratch cells. -/
private abbrev zr_cA {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  zr_col t (zr_lfield J.D.2 (J.i + 1))

/-- The inner zone's track-`t` column, read left to right, as scratch cells. -/
private abbrev zr_cB {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  zr_col t (zr_lfield J.D.2 J.i)

/-- The outer zone's new left part: its column from offset `2^(i-1)` on. -/
private abbrev zr_oV {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cA t J).drop (zr_hh J)

/-- The outer zone's new right part: the inner zone's first `2^(i-1)` column cells. -/
private abbrev zr_oW {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cB t J).take (zr_hh J)

/-- The pieces the two cuts leave behind. -/
private abbrev zr_oJ1 {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cB t J).drop (zr_hh J + 1)

/-- The pieces the two cuts leave behind. -/
private abbrev zr_oJ2 {k : ℕ} (t : Fin k) (J : zr_Ix k) : List (ZoneSym k) :=
  (zr_cA t J).take (zr_hh J - 1)

/-- **The left fields around level `i`**, for `1 ≤ i < ℓ`: the outer zone, the inner zone and
the field one inward have `4`, `2` and `1` times `2^(i-1)` cells, and start one separator apart. -/
private lemma zr_lfields {k : ℕ} {J : zr_Ix k} (h1 : 1 ≤ J.i) (h2 : J.i < J.D.1) :
    (zr_lfield J.D.2 (J.i + 1)).length = 4 * zr_hh J ∧
      (zr_lfield J.D.2 J.i).length = 2 * zr_hh J ∧
      (zr_lfield J.D.2 (J.i - 1)).length = zr_hh J ∧ 0 < zr_hh J ∧
      zr_lstart J.i = zr_lstart (J.i + 1) + 4 * zr_hh J + 1 ∧
      zr_lstart (J.i - 1) = zr_lstart J.i + 2 * zr_hh J + 1 := by
  have e1 := zr_lfield_length J.D.2 (J.i + 1) (by omega)
  have e2 := zr_lfield_length J.D.2 J.i (by omega)
  have e3 := zr_lfield_length J.D.2 (J.i - 1) (by omega)
  have s1 := zr_lstart_succ J.i
  have s2 := zr_lstart_succ (J.i - 1)
  rw [show J.i - 1 + 1 = J.i by omega] at s2
  have p1 : (2 : ℕ) ^ J.i = 2 * 2 ^ (J.i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have p2 : (2 : ℕ) ^ (J.i + 1) = 4 * 2 ^ (J.i - 1) := by
    rw [show J.i + 1 = (J.i - 1) + 2 by omega, pow_add]
    ring
  refine ⟨by rw [e1, p2], by rw [e2, p1], by rw [e3], Nat.two_pow_pos _, ?_, ?_⟩
  · rw [s1, p2]
    push_cast
    ring
  · rw [s2, p1]
    push_cast
    ring

/-- The lengths at a valid index. -/
private lemma zr_outV_lengths {k : ℕ} {t : Fin k} {J : zr_Ix k} (hV : zr_outV t J) :
    (zr_lfield J.D.2 (J.i + 1)).length = 4 * zr_hh J ∧
      (zr_lfield J.D.2 J.i).length = 2 * zr_hh J ∧
      (zr_lfield J.D.2 (J.i - 1)).length = zr_hh J ∧ (zr_cA t J).length = 4 * zr_hh J ∧
      (zr_cB t J).length = 2 * zr_hh J ∧ (zr_oV t J).length = 3 * zr_hh J ∧
      (zr_oW t J).length = zr_hh J ∧ (zr_oJ1 t J).length = zr_hh J - 1 ∧
      (zr_oJ2 t J).length = zr_hh J - 1 ∧ 0 < zr_hh J := by
  obtain ⟨e1, e2, e3, hpos, -, -⟩ := zr_lfields hV.1 hV.2.1
  refine ⟨e1, e2, e3, ?_⟩
  simp only [zr_cA, zr_cB, zr_oV, zr_oW, zr_oJ1, zr_oJ2, zr_col, List.length_map,
    List.length_take, List.length_drop, e1, e2, true_and]
  omega

/-- The field starts at a valid index: the outer zone, the inner zone, the field one inward. -/
private lemma zr_outV_starts {k : ℕ} {t : Fin k} {J : zr_Ix k} (hV : zr_outV t J) :
    zr_lstart J.i = zr_lstart (J.i + 1) + 4 * zr_hh J + 1 ∧
      zr_lstart (J.i - 1) = zr_lstart J.i + 2 * zr_hh J + 1 ∧
      zr_lstart (J.i + 1) = -((zoneStart J.i : ℤ) + zoneCapacity J.i - 1) ∧
      zr_lstart J.i = -((zoneStart (J.i - 1) : ℤ) + zoneCapacity (J.i - 1) - 1) ∧
      zoneCapacity J.i = 4 * zr_hh J ∧ zoneCapacity (J.i - 1) = 2 * zr_hh J := by
  obtain ⟨h1, h2, -, -, -⟩ := hV
  obtain ⟨-, -, -, -, s1, s2⟩ := zr_lfields h1 h2
  have p1 : (2 : ℕ) ^ J.i = 2 * 2 ^ (J.i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨s1, s2, ?_, ?_, ?_, ?_⟩
  · rw [zr_lstart, zr_rstart, if_neg (by omega), Nat.add_sub_cancel, zoneCapacity_eq, pow_succ]
    push_cast
    ring
  · rw [zr_lstart, zr_rstart, if_neg (by omega), zoneCapacity_eq, p1]
  · rw [zoneCapacity_eq, p1]
    ring
  · rw [zoneCapacity_eq]

/-- A left zone's column, read left to right: zone `i`'s track-`t` slots from its outer end. -/
private lemma zr_lcol {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : ℕ) (hi : i < ℓ)
    (p : ℕ) :
    (zr_col t (zr_lfield z (i + 1)))[p]? =
      if p < zoneCapacity i then
        some (zr_enc ((z t).left ⟨i, hi⟩)[zoneCapacity i - 1 - p]?)
      else none := by
  have hf : zr_lfield z (i + 1) = (zoneCells true (fun t => (z t).swap) ⟨i, hi⟩).reverse := by
    rw [zr_lfield, zr_rfield, if_neg (by omega), dif_pos (by simpa using hi)]
    rfl
  rw [hf, zr_col, List.getElem?_map]
  by_cases hp : p < zoneCapacity i
  · have hlt : zoneCapacity i - 1 - p < zoneCapacity i := by omega
    rw [List.getElem?_reverse (by rw [zoneCells_length]; exact hp), zoneCells_length,
      zoneCells_eq, List.getElem?_map, List.getElem?_range hlt, if_pos hp, Option.map_some,
      Option.map_some, zoneSlotOf_inr, ZoneContents.words_true, ZoneContents.swap_right]
  · rw [List.getElem?_eq_none (by
      rw [List.length_reverse, zoneCells_length]
      exact Nat.le_of_not_lt hp), if_neg hp]
    rfl

/-- Tape `0` after the outer zone's left part is written. -/
private abbrev zr_outO1 {k : ℕ} (t : Fin k) (J : zr_Ix k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (zoneSlotSet t) (zr_oV t J) (zonedTape J.D.2) (zr_lstart (J.i + 1))

/-- Tape `0` after the outer zone's right part is written. -/
private abbrev zr_outO2 {k : ℕ} (t : Fin k) (J : zr_Ix k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (zoneSlotSet t) (zr_oW t J) (zr_outO1 t J)
    (zr_lstart (J.i + 1) + 3 * zr_hh J)

/-- Tape `0` after the shift: the zoned tape of the shifted track. -/
private abbrev zr_outZ {k : ℕ} (t : Fin k) (J : zr_Ix k) : ℤ → Option (ZoneSym k) :=
  zonedTape (Function.update J.D.2 t (zoneShiftOut false J.i (J.D.2 t)))

/-- A zoned cell with track `t`'s slot set to its own is unchanged. -/
private lemma zr_slotSet_self {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : Fin ℓ)
    (o : ℕ) (ho : o < zoneCapacity i) :
    some (zoneSlotSet t (zonedTape z (-((zoneStart i + o : ℕ) : ℤ)))
        ((z t).left i)[o]?) = zonedTape z (-((zoneStart i + o : ℕ) : ℤ)) := by
  rw [zonedTape_left z i o ho, zoneSlotSet_eq, zoneCellOfCell_inr]
  simp only [ZoneContents.words_false]
  congr 2
  exact Function.update_eq_self t _

/-- **The left outward shift's tape-`0` writes**: the outer zone's left part written from its
own column from offset `2^(i-1)` on, its right part from the inner zone's first column cells,
and the inner zone's first `2^(i-1)` cells cleared give the zoned tape of the shifted track. -/
private lemma zr_outA3 {k : ℕ} {t : Fin k} {J : zr_Ix k} (hV : zr_outV t J) :
    zr_wr0 (zoneSlotOf t) (fun c _ => zoneSlotSet t c none) (zr_oW t J) (zr_outO2 t J)
      (zr_lstart J.i) = zr_outZ t J := by
  have hl := zr_outV_lengths hV
  have hs := zr_outV_starts hV
  obtain ⟨h1, h2, hf, hr, -⟩ := hV
  have hf' : ((J.D.2 t).left ⟨J.i - 1, by omega⟩).length = zoneCapacity (J.i - 1) := by
    rw [zr_lword, dif_pos (by omega)] at hf
    exact hf
  have hr' : ((J.D.2 t).left ⟨J.i, h2⟩).length + 2 ^ (J.i - 1) ≤ zoneCapacity J.i := by
    rw [zr_lword, dif_pos h2] at hr
    exact hr
  have hh : (2 : ℕ) ^ (J.i - 1) = zr_hh J := rfl
  have hzs := zoneStart_succ (J.i - 1)
  rw [show J.i - 1 + 1 = J.i by omega] at hzs
  have hB : zr_cB t J = zr_col t (zr_lfield J.D.2 (J.i - 1 + 1)) := by
    simp only [zr_cB, Nat.sub_add_cancel h1]
  funext q
  rw [zr_outZ, zr_shiftOut_tape J.D.2 t J.i h1 h2 hf' hr' q]
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := hl
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hs
  simp only [zr_wr0, zr_outO2, zr_outO1]
  by_cases hR : zr_lstart (J.i + 1) ≤ q ∧ q < zr_lstart (J.i + 1) + 4 * zr_hh J
  · obtain ⟨p, hp⟩ : ∃ p : ℕ, q - zr_lstart (J.i + 1) = p :=
      ⟨(q - zr_lstart (J.i + 1)).toNat, by omega⟩
    by_cases h3 : p < 3 * zr_hh J
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
        if_pos (by omega), hp, FinTM.bufferTape_nat, List.getElem?_drop,
        zr_lcol J.D.2 t J.i h2 (zr_hh J + p), if_pos (by omega), Option.map_some, zoneSlotOf_inr,
        List.getElem?_append_right (by rw [List.length_drop]; omega), List.length_drop]
      congr 3
      omega
    · obtain ⟨r, hr0⟩ : ∃ r : ℕ, q - (zr_lstart (J.i + 1) + 3 * zr_hh J) = r :=
        ⟨p - 3 * zr_hh J, by omega⟩
      rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), hr0, FinTM.bufferTape_nat, List.getElem?_take, if_pos (by omega), hB,
        zr_lcol J.D.2 t (J.i - 1) (by omega) r, if_pos (by omega), Option.map_some,
        zoneSlotOf_inr, List.getElem?_append_left (by rw [List.length_drop]; omega),
        List.getElem?_drop]
      congr 3
      omega
  by_cases hC : zr_lstart J.i ≤ q ∧ q < zr_lstart J.i + 2 * zr_hh J
  · obtain ⟨r, hr0⟩ : ∃ r : ℕ, q - zr_lstart J.i = r := ⟨(q - zr_lstart J.i).toNat, by omega⟩
    by_cases h3 : r < zr_hh J
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), hr0,
        FinTM.bufferTape_nat, List.getElem?_take, if_pos h3, hB,
        zr_lcol J.D.2 t (J.i - 1) (by omega) r, if_pos (by omega), Option.map_some,
        List.getElem?_take, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        List.getElem?_take, if_pos (by omega)]
      obtain ⟨o, ho⟩ : ∃ o : ℕ, q = -((zoneStart (J.i - 1) + o : ℕ) : ℤ) :=
        ⟨2 * zr_hh J - 1 - r, by push_cast; omega⟩
      subst ho
      rw [show (-(-((zoneStart (J.i - 1) + o : ℕ) : ℤ)) - zoneStart (J.i - 1)).toNat = o by
        push_cast
        omega]
      exact (zr_slotSet_self J.D.2 t ⟨J.i - 1, by omega⟩ o
        (by show o < zoneCapacity (J.i - 1); omega)).symm
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

/-- The left outward shift's head box: the zoned head from one cell left of the outer zone to
one past the field one inward, scratch over its work area. -/
private abbrev zr_outL {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (J.i + 1) - 1) J.s

/-- The left outward shift's head box, its upper corner. -/
private abbrev zr_outU {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + 6 * zr_hh J + 3)

/-- The left outward shift's tape stages: tape `0`, and the scratch layout `L` laid out from two
cells past the scratch head. -/
private abbrev zr_outT {k : ℕ} (J : zr_Ix k) (A : ℤ → Option (ZoneSym k))
    (L : List (List (ZoneSym k))) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes A (zr_scr J.σ (J.s + 1) L)

/-- **The left outward shift at level `i`**, as one pinned segment: the forty steps of the
column move in sequence. -/
private def zr_outSeg {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ (zr_outV t) (fun J => zr_outT J (zonedTape J.D.2) [])
      (fun J => zr_outT J (zr_outZ t J) [])
      (fun J => zr_heads (zr_lstart J.i) J.s)
      (fun J => zr_heads (zr_lstart J.i) J.s) _ zr_outL zr_outU from
  -- step 1: back over the outer zone
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 (J.i + 1))
        (fun J => zr_outT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart J.i) J.s)
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart J.i - (zr_lfield J.D.2 (J.i + 1)).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 2: scratch right
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_outT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart (J.i + 1)) J.s))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 3: scratch right, to the work area
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_outT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart (J.i + 1)) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 4: copy the outer zone's column
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_lfield J.D.2 (J.i + 1))
        (fun J => zr_outT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart (J.i + 1)) (J.s + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i + 1) + q) = _
          exact zr_lfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_copy _ _ _ _ [] _ _ _ _
          (by rw [List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 5: skip the outer zone
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_lfield J.D.2 (J.i + 1))
        (fun J => zr_outT J (zonedTape J.D.2) [zr_cA t J])
        (fun J => zr_heads (zr_lstart (J.i + 1)) (J.s + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i + 1) + q) = _
          exact zr_lfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _
            (by omega) _ (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 6: skip the inner zone
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_lfield J.D.2 J.i)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_cA t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart J.i + q) = _
          exact zr_lfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _
            (by omega) _ (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 7: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_cA t J])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 8: scratch left, to its start
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_cA t J])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 9: walk over the field one inward
  zr_segSeq (zr_seg (zr_pinWalk_step _ 0 (fun J => zr_lfield J.D.2 (J.i - 1))
        (fun J => zr_outT J (zonedTape J.D.2) [zr_cA t J])
        (fun J => zr_heads (zr_lstart (J.i - 1)) J.s)
        fun J hV q hq => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) + ↑q) = _
          exact zr_lfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _
            (by omega) _ (by omega) (by exact_mod_cast hq))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 10: cut the outer column before its cell `2^(i-1)`
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (some none)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_cA t J])
        (fun J => zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + zr_hh J + 1)))
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_split _ _ _ _ [] [] (zr_cA t J) (zr_hh J - 1) (zr_hh J)
          (by omega) (by omega)
          (by rw [zr_heads_one, List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 11: skip the outer column's rest
  zr_segSeq (zr_seg (zr_pinSkip_step _ 1 (fun J => zr_oV t J)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J])
        (fun J => zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J]
            (J.s + zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 12: back over the field one inward
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 (J.i - 1))
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J])
        (fun J => zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) + zr_hh J + 1 - (zr_lfield J.D.2 (J.i - 1)).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 13: back over the inner zone
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 J.i)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) - (zr_lfield J.D.2 J.i).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 14: copy the inner zone's column
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_lfield J.D.2 J.i)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart J.i + q) = _
          exact zr_lfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_copy _ _ _ _ [zr_oJ2 t J, zr_oV t J] _ _ _ _
          (by rw [List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 15: skip the inner zone
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_lfield J.D.2 J.i)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_cB t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart J.i + q) = _
          exact zr_lfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _
            (by omega) _ (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 16: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_cB t J])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + 4 * zr_hh J + 3)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 17: walk over the field one inward
  zr_segSeq (zr_seg (zr_pinWalk_step _ 0 (fun J => zr_lfield J.D.2 (J.i - 1))
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_cB t J])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + 4 * zr_hh J + 2))
        fun J hV q hq => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) + ↑q) = _
          exact zr_lfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _
            (by omega) _ (by omega) (by exact_mod_cast hq))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 18: cut the inner column after its first `2^(i-1)` cells
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (some none)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_cB t J])
        (fun J => zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + 5 * zr_hh J + 3)))
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_split _ _ _ _ [zr_oJ2 t J, zr_oV t J] [] (zr_cB t J) (zr_hh J) (zr_hh J + 1)
          (by omega) (by omega)
          (by rw [zr_heads_one, List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 19: back over the inner column's head
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_oW t J)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + 5 * zr_hh J + 4))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 5 * zr_hh J + 4 - ((zr_oW t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 20: back over the outer column's rest
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_oV t J)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 4 * zr_hh J + 3 - ((zr_oV t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 21: back over the field one inward
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 (J.i - 1))
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) + zr_hh J + 1 - (zr_lfield J.D.2 (J.i - 1)).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 22: back over the inner zone
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 J.i)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) - (zr_lfield J.D.2 J.i).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 23: back over the outer zone
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 (J.i + 1))
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          have := zr_outV_starts hV
          show (zonedTape J.D.2)
            (zr_lstart J.i - (zr_lfield J.D.2 (J.i + 1)).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 24: write the outer zone's left part
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (zoneSlotSet t)
        (fun J => zr_oV t J)
        (fun J => zr_outT J (zonedTape J.D.2) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i + 1)) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 25: walk over the outer column's rest
  zr_segSeq (zr_seg (zr_pinWalk_step _ 1 (fun J => zr_oV t J)
        (fun J => zr_outT J (zr_outO1 t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i + 1)) (J.s + zr_hh J + 2))
        fun J hV q hq => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + zr_hh J + 2 + ↑q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ,
                fieldOffset_zero]; omega) ↑q (by omega) (by exact_mod_cast hq))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 26: zoned head left, to the outer zone's right part
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_outT J (zr_outO1 t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i + 1) + 3 * zr_hh J + 1) (J.s + 4 * zr_hh J + 3)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 27: write the outer zone's right part
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (zoneSlotSet t)
        (fun J => zr_oW t J)
        (fun J => zr_outT J (zr_outO1 t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i + 1) + 3 * zr_hh J) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 4 * zr_hh J + 3 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 28: walk over the inner column's head, to the inner zone
  zr_segSeq (zr_seg (zr_pinWalk_step _ 1 (fun J => zr_oW t J)
        (fun J => zr_outT J (zr_outO2 t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart (J.i + 1) + 3 * zr_hh J) (J.s + 4 * zr_hh J + 3))
        fun J hV q hq => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 4 * zr_hh J + 3 + ↑q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_zero]; omega) ↑q (by omega) (by exact_mod_cast hq))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 29: back over the inner column's head
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_oW t J)
        (fun J => zr_outT J (zr_outO2 t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 5 * zr_hh J + 4))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 5 * zr_hh J + 4 - ((zr_oW t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 30: clear the inner zone's first `2^(i-1)` cells
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (fun c _ => zoneSlotSet t c none)
        (fun J => zr_oW t J)
        (fun J => zr_outT J (zr_outO2 t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 4 * zr_hh J + 3 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => (zr_copy0 _ _ _ _ _ _ _).trans
        (congrArg (fun A => zr_tapes A _) (zr_outA3 hV)))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 31: skip the inner column's head
  zr_segSeq (zr_seg (zr_pinSkip_step _ 1 (fun J => zr_oW t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 4 * zr_hh J + 3 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_zero]; omega) q (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 32: clear the inner column's rest
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_oJ1 t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 5 * zr_hh J + 4))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J]
            (J.s + 5 * zr_hh J + 4 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J, zr_oJ1 t J] 3 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_clear _ _ _ [zr_oJ2 t J, zr_oV t J, zr_oW t J] _ _
          (by rw [zr_heads_one, List.length_cons, List.length_cons, List.length_singleton,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 33: back over the inner column's head
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_oW t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 5 * zr_hh J + 4))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J]
            (J.s + 5 * zr_hh J + 4 - ((zr_oW t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 34: clear it
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_oW t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J, zr_oV t J, zr_oW t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J, zr_oW t J]
            (J.s + 4 * zr_hh J + 3 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J, zr_oW t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_clear _ _ _ [zr_oJ2 t J, zr_oV t J] _ _
          (by rw [zr_heads_one, List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 35: back over the outer column's rest
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_oV t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J, zr_oV t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 4 * zr_hh J + 3))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J]
            (J.s + 4 * zr_hh J + 3 - ((zr_oV t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 36: clear it
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_oV t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J, zr_oV t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J, zr_oV t J]
            (J.s + zr_hh J + 2 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J, zr_oV t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_clear _ _ _ [zr_oJ2 t J] _ _
          (by rw [zr_heads_one, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 37: back over the outer column's head
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_oJ2 t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J]
            (J.s + zr_hh J + 2 - ((zr_oJ2 t J).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 38: clear it
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_oJ2 t J)
        (fun J => zr_outT J (zr_outZ t J) [zr_oJ2 t J])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 2))
        fun J hV q h0 h1 => by
          have := zr_outV_lengths hV
          show zr_scr J.σ (J.s + 1) [zr_oJ2 t J]
            (J.s + 2 + q) = _
          exact zr_scr_at (hV.2.2.2.2 _ (by omega))
            [zr_oJ2 t J] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_outV_lengths hV
        exact zr_scr_clear _ _ _ [] _ _
          (by rw [zr_heads_one, List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_outL, zr_outU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 39: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_outT J (zr_outZ t J) [])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 40: scratch left, to its start
  (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_outT J (zr_outZ t J) [])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        have := zr_outV_starts hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_outL, zr_outU,
          if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega))

/-- A pinned step's start tapes restated by an equality at every valid index. -/
private lemma zr_PinStep_start {k : ℕ} {S J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X : Set (Option S)} {C : Contract M e X J x}
    {V : J → Prop} {T₁ T₁' T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ}
    {τ : J → ℕ} {L U : J → Fin 2 → ℤ} (h : zr_PinStep C V T₁ T₂ p₁ p₂ τ L U)
    (hT : ∀ j, V j → T₁ j = T₁' j) : zr_PinStep C V T₁' T₂ p₁ p₂ τ L U := by
  refine ⟨fun j d hd => ?_, fun j d hV hd => h.2 j d hV ⟨hd.1.trans (hT j hV).symm, hd.2⟩⟩
  obtain ⟨hV, hd'⟩ := h.1 j d hd
  exact ⟨hV, hd'.1.trans (hT j hV), hd'.2⟩

/-- The empty scratch layout over a tape blank from its head on is that tape. -/
private lemma zr_scr_nil {k : ℕ} {σ : ℤ → Option (ZoneSym k)} {s : ℤ}
    (hσ : ∀ r, s ≤ r → σ r = none) : zr_scr σ s [] = σ := by
  funext r
  simp only [zr_scr]
  split_ifs with h
  · rfl
  · rw [fieldsTape_nil, hσ r (by omega)]

/-- **The right inward shift at level `i`, its guard enabled**: from the zoned tape with the
zoned head at the receiver's start and scratch blank from its head on, the shift's segment ends
at the zoned tape of the shifted track with both heads and the scratch restored, after
`76 · 2^(i-1) + 77` steps, its heads within `zr_inL`/`zr_inU`. -/
private lemma zr_inSeg_spec {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_inSeg t x).C (zr_inV t) (fun J => zr_tapes (zonedTape J.D.2) J.σ)
      (fun J => zr_tapes (zr_inZ t J) J.σ) (fun J => zr_heads (zr_rstart J.i) J.s)
      (fun J => zr_heads (zr_rstart J.i) J.s) (fun J => 76 * zr_hh J + 77) zr_inL zr_inU :=
  zr_PinStep_start (zr_PinStep_congr (zr_inSeg t x).step
      (fun J hV => by rw [zr_inT, zr_scr_nil hV.2.2.2]) (fun _ _ => rfl)
      (fun J hV => by
        have := zr_inV_lengths hV
        omega)
      (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl))
    (fun J hV => by rw [zr_inT, zr_scr_nil hV.2.2.2])

/-- **The left outward shift at level `i`, its guards enabled**: from the zoned tape with the
zoned head at the inner zone's outermost cell and scratch blank from its head on, the shift's
segment ends at the zoned tape of the shifted track with both heads and the scratch restored,
after `76 · 2^(i-1) + 107` steps, its heads within `zr_outL`/`zr_outU`. -/
private lemma zr_outSeg_spec {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_outSeg t x).C (zr_outV t) (fun J => zr_tapes (zonedTape J.D.2) J.σ)
      (fun J => zr_tapes (zr_outZ t J) J.σ) (fun J => zr_heads (zr_lstart J.i) J.s)
      (fun J => zr_heads (zr_lstart J.i) J.s) (fun J => 76 * zr_hh J + 107) zr_outL zr_outU :=
  zr_PinStep_start (zr_PinStep_congr (zr_outSeg t x).step
      (fun J hV => by rw [zr_outT, zr_scr_nil fun r hr => hV.2.2.2.2 r (by omega)])
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_outV_lengths hV
        omega)
      (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl))
    (fun J hV => by rw [zr_outT, zr_scr_nil fun r hr => hV.2.2.2.2 r (by omega)])

/-- **The right inward guard**: at the receiver's start, track `t`'s slot is `⊠` exactly when
the receiver is empty. -/
private lemma zr_inGuard_iff {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : ℕ)
    (hi : 1 ≤ i) (hiℓ : i < ℓ) :
    (zonedTape z (zr_rstart i)).map (zoneSlotOf t) = some none ↔
      (z t).right ⟨i - 1, by omega⟩ = [] := by
  have h := zr_inner_empty_iff true z ⟨i - 1, by omega⟩ t
  rw [zr_zonePos, if_pos rfl, Nat.add_zero, ZoneContents.words_true] at h
  rw [zr_rstart, if_neg (by omega)]
  exact h

/-- **The left outward guard's first test**: at the inner zone's outermost cell, track `t`'s
slot is occupied exactly when the inner zone is full. -/
private lemma zr_outFull_iff {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : ℕ)
    (hi : 1 ≤ i) (hiℓ : i < ℓ) :
    (zonedTape z (zr_lstart i)).map (zoneSlotOf t) ≠ some none ↔
      ((z t).left ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) := by
  have h := zr_outer_full_iff false z ⟨i - 1, by omega⟩ t
  have hc := zr_capacity_pos (i - 1)
  rw [zr_zonePos, if_neg Bool.false_ne_true, ZoneContents.words_false] at h
  rw [zr_lstart, zr_rstart, if_neg (by omega),
    show -((zoneStart (i - 1) : ℤ) + ((2 ^ i : ℕ) : ℤ) - 1) =
      -((zoneStart (i - 1) + (zoneCapacity (i - 1) - 1) : ℕ) : ℤ) by
      rw [zoneCapacity_eq, show 2 * 2 ^ (i - 1) = 2 ^ i by rw [← pow_succ']; congr 1; omega]
      have hpos := Nat.two_pow_pos i
      generalize 2 ^ i = P at hpos ⊢
      omega]
  exact h

/-- **The left outward guard's second test**: `2^(i-1) - 1` cells right of the outer zone's
outermost cell, track `t`'s slot is `⊠` exactly when the outer zone has room for `2^(i-1)` more
slots. -/
private lemma zr_outRoom_iff {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (t : Fin k) (i : ℕ)
    (hi : 1 ≤ i) (hiℓ : i < ℓ) :
    (zonedTape z (zr_lstart (i + 1) + ((2 ^ (i - 1) : ℕ) : ℤ) - 1)).map (zoneSlotOf t) =
        some none ↔
      ((z t).left ⟨i, hiℓ⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i := by
  have hp : (0 : ℕ) < 2 ^ (i - 1) := Nat.two_pow_pos _
  have hcap : zoneCapacity i = 4 * 2 ^ (i - 1) := by
    rw [zoneCapacity_eq, show i = (i - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have h := zr_room_iff false z ⟨i, hiℓ⟩ t (2 ^ (i - 1)) hp (by simp only; omega)
  rw [zr_zonePos, if_neg Bool.false_ne_true, ZoneContents.words_false] at h
  rw [zr_lstart, zr_rstart, if_neg (by omega), Nat.add_sub_cancel,
    show -((zoneStart i : ℤ) + ((2 ^ (i + 1) : ℕ) : ℤ) - 1) + ((2 ^ (i - 1) : ℕ) : ℤ) - 1 =
      -((zoneStart i + (zoneCapacity i - 2 ^ (i - 1)) : ℕ) : ℤ) by
      rw [show (2 : ℕ) ^ (i + 1) = zoneCapacity i by rw [zoneCapacity_eq, pow_succ']]
      omega]
  exact h

/-- With the right inward guard disabled, the shifted tape is the zoned tape. -/
private lemma zr_inZ_off {k : ℕ} (t : Fin k) (J : zr_Ix k) (hi : 1 ≤ J.i) (hiℓ : J.i < J.D.1)
    (hne : (J.D.2 t).right ⟨J.i - 1, by omega⟩ ≠ []) : zr_inZ t J = zonedTape J.D.2 := by
  rw [zr_inZ, zr_shiftIn_off _ _ hi hiℓ hne, Function.update_eq_self]

/-- With the left outward guard disabled, the shifted tape is the zoned tape. -/
private lemma zr_outZ_off {k : ℕ} (t : Fin k) (J : zr_Ix k) (hi : 1 ≤ J.i) (hiℓ : J.i < J.D.1)
    (hne : ¬ (((J.D.2 t).left ⟨J.i - 1, by omega⟩).length = zoneCapacity (J.i - 1) ∧
      ((J.D.2 t).left ⟨J.i, hiℓ⟩).length + 2 ^ (J.i - 1) ≤ zoneCapacity J.i)) :
    zr_outZ t J = zonedTape J.D.2 := by
  rw [zr_outZ, zr_shiftOut_off _ _ hi hiℓ hne, Function.update_eq_self]

/-- **The seam of a pinned branch arm**: a pinned test whose verdict at `j` is `a₁` exactly
when `v j`, followed by an arm pinned from the test's endpoint pin at the indices it selects. -/
private lemma zr_pin_blink {k : ℕ} {S₀ S₁ J : Type} {x : List (ZoneSym k)}
    {M₀ : MultiTapeTM 2 (ZoneSym k) S₀} {M₁ : MultiTapeTM 2 (ZoneSym k) S₁} {e₀ a₁ a₂ a : S₀}
    {e₁ : S₁} {X₀ : Set (Option S₀)} {X₁ : Set (Option S₁)} {C₀ : Contract M₀ e₀ X₀ J x}
    {C₁ : Contract M₁ e₁ X₁ J x} {V : J → Prop} {v : J → Bool} (b : Bool) (he : a₁ ≠ a₂)
    {T₀ T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₀ p₁ p₂ : J → Fin 2 → ℤ}
    {τ₀ τ₁ : J → ℕ} {L₀ U₀ L₁ U₁ : J → Fin 2 → ℤ} (h₀ : zr_PinStep C₀ V T₀ T₁ p₀ p₁ τ₀ L₀ U₀)
    (hv : ∀ j d, V j → zr_pinned (T₀ j) (p₀ j) d →
      (C₀.post j d).state = some (if v j then a₁ else a₂))
    (ha : a = if b then a₁ else a₂)
    (h₁ : zr_PinStep C₁ (fun j => V j ∧ v j = b) T₁ T₂ p₁ p₂ τ₁ L₁ U₁) :
    ∀ j d, d.state = some e₀ → C₀.pre j d → (C₀.post j d).state = some a →
      C₁.pre j ((C₀.post j d).mapState fun _ => e₁) := by
  intro j d _ hp hs
  obtain ⟨hV, hd⟩ := h₀.1 j d hp
  have hb : v j = b := by
    rw [hv j d hV hd, ha, Option.some.injEq] at hs
    cases hvj : v j <;> cases b <;> simp only [hvj, if_true, if_false, Bool.false_eq_true] at hs
    · rfl
    · exact absurd hs.symm he
    · exact absurd hs he
    · rfl
  exact (h₁.2 j _ ⟨hV, hb⟩ ((zr_pinned_mapState_iff _).mpr (h₀.2 j d hV hd).2.1)).1

/-- **A pinned branch**: a pinned test whose verdict at `j` is `a₁` exactly when `v j`, followed
by two arms pinned from the test's endpoint pin to one endpoint pin, each at the indices it
selects, is a pinned step to that endpoint; its time is the selected arm's after the test and the
dispatch step. -/
private lemma zr_PinStep_branch {k : ℕ} {S₀ S₁ S₂ J : Type} [DecidableEq S₀] [DecidableEq S₁]
    {x : List (ZoneSym k)} {M₀ : MultiTapeTM 2 (ZoneSym k) S₀}
    {M₁ : MultiTapeTM 2 (ZoneSym k) S₁} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₀ a₁ a₂ : S₀}
    {e₁ : S₁} {e₂ : S₂} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)} (he : a₁ ≠ a₂)
    {C₀ : Contract M₀ e₀ {some a₁, some a₂} J x} {C₁ : Contract M₁ e₁ X₁ J x}
    {C₂ : Contract M₂ e₂ X₂ J x} {V : J → Prop} {v : J → Bool}
    {T₀ T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₀ p₁ p₂ : J → Fin 2 → ℤ}
    {τ₀ τ₁ τ₂ : J → ℕ} {L U : J → Fin 2 → ℤ} (h₀ : zr_PinStep C₀ V T₀ T₁ p₀ p₁ τ₀ L U)
    (hv : ∀ j d, V j → zr_pinned (T₀ j) (p₀ j) d →
      (C₀.post j d).state = some (if v j then a₁ else a₂))
    (h₁ : zr_PinStep C₁ (fun j => V j ∧ v j = true) T₁ T₂ p₁ p₂ τ₁ L U)
    (h₂ : zr_PinStep C₂ (fun j => V j ∧ v j = false) T₁ T₂ p₁ p₂ τ₂ L U)
    (hl₁ : ∀ j d, d.state = some e₀ → C₀.pre j d → (C₀.post j d).state = some a₁ →
      C₁.pre j ((C₀.post j d).mapState fun _ => e₁))
    (hl₂ : ∀ j d, d.state = some e₀ → C₀.pre j d → (C₀.post j d).state = some a₂ →
      C₂.pre j ((C₀.post j d).mapState fun _ => e₂)) :
    zr_PinStep (Contract.branch he C₀ C₁ C₂ (fun j => j) (fun j => j) hl₁ hl₂) V T₀ T₂ p₀ p₂
      (fun j => τ₀ j + 1 + if v j then τ₁ j else τ₂ j) L U := by
  refine ⟨fun j d hd => ?_, fun j d hV hd => ?_⟩
  · rw [Contract.branch_pre] at hd
    obtain ⟨hV, hd'⟩ := h₀.1 j _ hd
    exact ⟨hV, (zr_pinned_mapState_iff _).mp hd'⟩
  have hd₀ := (zr_pinned_mapState_iff (fun _ => e₀)).mpr hd
  obtain ⟨hp0, hq0, hi0, ho0, ht0, hb0⟩ := h₀.2 j _ hV hd₀
  have hs := hv j _ hV hd₀
  cases hvj : v j
  · have hne : (C₀.post j (d.mapState fun _ => e₀)).state ≠ some a₁ := by
      rw [hs, hvj]
      simp only [Bool.false_eq_true, if_false, ne_eq, Option.some.injEq]
      exact he.symm
    obtain ⟨-, hq2, hi2, ho2, ht2, hb2⟩ :=
      h₂.2 j _ ⟨hV, hvj⟩ ((zr_pinned_mapState_iff _).mpr hq0)
    refine ⟨by rw [Contract.branch_pre]; exact hp0, ?_, ?_, ?_, ?_, fun i => ?_⟩
    · rw [Contract.branch_post, if_neg hne]
      exact (zr_pinned_mapState_iff _).mpr hq2
    · rw [Contract.branch_post, if_neg hne, Cfg.mapState_inputPos, hi2, Cfg.mapState_inputPos,
        hi0, Cfg.mapState_inputPos]
    · rw [Contract.branch_post, if_neg hne, Cfg.mapState_output, ho2, Cfg.mapState_output, ho0,
        Cfg.mapState_output]
    · rw [Contract.branch_time, if_neg hne, ht0, ht2]
      show _ = τ₀ j + 1 + if v j = true then τ₁ j else τ₂ j
      rw [hvj]
      rfl
    · rw [Contract.branch_lo, Contract.branch_hi, if_neg hne, if_neg hne]
      exact ⟨le_min (hb0 i).1 (hb2 i).1, max_le (hb0 i).2 (hb2 i).2⟩
  · have heq : (C₀.post j (d.mapState fun _ => e₀)).state = some a₁ := by
      rw [hs, hvj]
      rfl
    obtain ⟨-, hq1, hi1, ho1, ht1, hb1⟩ :=
      h₁.2 j _ ⟨hV, hvj⟩ ((zr_pinned_mapState_iff _).mpr hq0)
    refine ⟨by rw [Contract.branch_pre]; exact hp0, ?_, ?_, ?_, ?_, fun i => ?_⟩
    · rw [Contract.branch_post, if_pos heq]
      exact (zr_pinned_mapState_iff _).mpr ((zr_pinned_mapState_iff _).mpr hq1)
    · rw [Contract.branch_post, if_pos heq, Cfg.mapState_inputPos, Cfg.mapState_inputPos, hi1,
        Cfg.mapState_inputPos, hi0, Cfg.mapState_inputPos]
    · rw [Contract.branch_post, if_pos heq, Cfg.mapState_output, Cfg.mapState_output, ho1,
        Cfg.mapState_output, ho0, Cfg.mapState_output]
    · rw [Contract.branch_time, if_pos heq, ht0, ht1]
      show _ = τ₀ j + 1 + if v j = true then τ₁ j else τ₂ j
      rw [hvj]
      rfl
    · rw [Contract.branch_lo, Contract.branch_hi, if_pos heq, if_pos heq]
      exact ⟨le_min (hb0 i).1 (hb1 i).1, max_le (hb0 i).2 (hb1 i).2⟩

/-- A pinned step re-indexed through `f`, under a validity predicate that implies the
original's at `f j`. -/
private lemma zr_PinStep_re {k : ℕ} {S I J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X : Set (Option S)} {C : Contract M e X I x}
    {V : I → Prop} {T₁ T₂ : I → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : I → Fin 2 → ℤ}
    {τ : I → ℕ} {L U : I → Fin 2 → ℤ} (h : zr_PinStep C V T₁ T₂ p₁ p₂ τ L U) (f : J → I)
    (V' : J → Prop) (hV : ∀ j, V' j → V (f j)) :
    zr_PinStep (zr_reindexContract C f (fun j d => V' j ∧ zr_pinned (T₁ (f j)) (p₁ (f j)) d)
        fun j d hd => (h.2 (f j) d (hV j hd.1) hd.2).1) V' (fun j => T₁ (f j))
      (fun j => T₂ (f j)) (fun j => p₁ (f j)) (fun j => p₂ (f j)) (fun j => τ (f j))
      (fun j => L (f j)) (fun j => U (f j)) :=
  zr_pinRe_step _ _ _ _ _ _ fun j d hV' hd => (h.2 (f j) d (hV j hV') hd).2

/-- A pinned segment re-indexed through `f`, under a validity predicate that implies the
original's at `f j`. -/
private def zr_segRe {k : ℕ} {S I J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e d : S} {V : I → Prop}
    {T₁ T₂ : I → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : I → Fin 2 → ℤ} {τ : I → ℕ}
    {L U : I → Fin 2 → ℤ} (A : zr_PinSeg x M e d V T₁ T₂ p₁ p₂ τ L U) (f : J → I)
    (V' : J → Prop) (hV : ∀ j, V' j → V (f j)) :
    zr_PinSeg x M e d V' (fun j => T₁ (f j)) (fun j => T₂ (f j)) (fun j => p₁ (f j))
      (fun j => p₂ (f j)) (fun j => τ (f j)) (fun j => L (f j)) (fun j => U (f j)) :=
  ⟨_, zr_PinStep_re A.step f V' hV⟩

/-- The one-cell leaf as a pinned test: read tape `i` at its head, record `choose` of the cell
as the verdict, and move the head by `dir`. -/
private def zr_pinTestContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop)
    (i : Fin 2) (choose : Option (ZoneSym k) → Bool) (dir : SignType)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :=
  zr_reindexContract (zr_exitsContract (zr_cellContract i choose none dir x) _ zr_verdicts_pair)
    (fun _ => ()) (fun j d => V j ∧ zr_pinned (T j) (p j) d) fun _ _ _ => by
      rw [zr_exitsContract, Contract.ofSegment_pre]
      trivial

/-- The pinned test keeps the tapes and moves only its head. -/
private lemma zr_pinTest_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop)
    (i : Fin 2) (choose : Option (ZoneSym k) → Bool) (dir : SignType)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :
    zr_PinStep (zr_pinTestContract x V i choose dir T p) V T T p
      (fun j => Function.update (p j) i (p j i + dir)) (fun _ => 1)
      (fun j i' => min (p j i') (Function.update (p j) i (p j i + dir) i'))
      (fun j i' => max (p j i') (Function.update (p j) i (p j i + dir) i')) :=
  zr_pinRe_ofSeg _ _ _ _ (fun _ _ _ => trivial) fun j d _ hd => by
    simp only [zr_cellContract, zr_cellPost, hd.1, hd.2]
    exact ⟨⟨rfl, rfl⟩, trivial, trivial, trivial, fun _ => ⟨le_rfl, le_rfl⟩⟩

/-- The pinned test's verdict is `choose` of the cell under its head. -/
private lemma zr_pinTest_state {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop)
    (i : Fin 2) (choose : Option (ZoneSym k) → Bool) (dir : SignType)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) (j : J)
    (d : Cfg 2 (ZoneSym k) (Option Bool) x) (hd : zr_pinned (T j) (p j) d) :
    ((zr_pinTestContract x V i choose dir T p).post j d).state =
      some (some (choose (T j i (p j i)))) := by
  simp only [zr_pinTestContract, zr_reindexContract, zr_exitsContract, Contract.ofSegment_post,
    zr_cellContract, zr_cellPost, Cfg.workTapeSymbols_eq, hd.1, hd.2]

/-- The image of a pair of live exits under a renaming. -/
private lemma zr_map_pair {S T : Type} (f : S → T) (a b : S) :
    (Option.map f '' {some a, some b}) = {some (f a), some (f b)} := by
  simp only [Set.image_insert_eq, Set.image_singleton, Option.map_some]

/-- The seam's image of the verdict pair. -/
private lemma zr_verdicts_inr {A : Type} :
    (Option.map (Sum.inr : Option Bool → A ⊕ Option Bool) ''
        {some (some true), some (some false)}) =
      {some (.inr (some true)), some (.inr (some false))} :=
  zr_map_pair _ _ _

/-- The stationary anchor leaf as a pinned zero-time step. -/
private def zr_pinAnchorContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :=
  zr_reindexContract (zr_anchorContract x) (fun _ => ()) (fun j d => V j ∧ zr_pinned (T j) (p j) d)
    fun _ _ _ => by
      rw [zr_anchorContract, Contract.ofSegment_pre]
      trivial

/-- The pinned anchor changes nothing and takes no step. -/
private lemma zr_pinAnchor_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :
    zr_PinStep (zr_pinAnchorContract x V T p) V T T p p (fun _ => 0) p p :=
  zr_pinRe_ofSeg _ _ _ _ (fun _ _ _ => trivial) fun _ _ _ hd =>
    ⟨hd, rfl, rfl, rfl, fun i => ⟨(congrFun hd.2 i).ge, (congrFun hd.2 i).le⟩⟩

/-- **A pinned peek**: step tape `i` by `δ`, test the cell there with `choose` while stepping
back. -/
private def zr_pinPeekContract {k : ℕ} {J : Type} (x : List (ZoneSym k)) (V : J → Prop)
    (i : Fin 2) (δ : SignType) (choose : Option (ZoneSym k) → Bool)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :=
  zr_exitsContract ((zr_pinCellContract x V i δ none T p).seq
      (zr_pinTestContract x V i choose (-δ) T fun j => Function.update (p j) i (p j i + δ))
      (fun j => j) (zr_pin_hlink (zr_pinCell_step V i δ none T p)
        (zr_pinTest_step V i choose (-δ) T _))) _ zr_verdicts_inr

/-- The pinned peek is stationary, in three steps, its heads within one cell. -/
private lemma zr_pinPeek_step {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop)
    (i : Fin 2) (δ : SignType) (choose : Option (ZoneSym k) → Bool)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) :
    zr_PinStep (zr_pinPeekContract x V i δ choose T p) V T T p p (fun _ => 3)
      (fun j i' => p j i' - 1) (fun j i' => p j i' + 1) := by
  unfold zr_pinPeekContract
  refine zr_PinStep_exits (hX := zr_verdicts_inr) (zr_PinStep_congr
    (zr_PinStep_seq (zr_pinCell_step V i δ none T p)
    (zr_pinTest_step V i choose (-δ) T _) _) (fun _ _ => rfl) (fun j _ => ?_) (fun _ _ => rfl)
    (fun j _ i' => ?_) (fun j _ i' => ?_))
  · simp only [Function.update_idem, Function.update_self, SignType.coe_neg, add_neg_cancel_right,
      Function.update_eq_self]
  · have hδ : (-1 : ℤ) ≤ δ ∧ (δ : ℤ) ≤ 1 := by cases δ <;> decide
    by_cases hi : i' = i
    · subst hi
      simp only [Function.update_self, SignType.coe_neg]
      omega
    · simp only [Function.update_of_ne hi]
      omega
  · have hδ : (-1 : ℤ) ≤ δ ∧ (δ : ℤ) ≤ 1 := by cases δ <;> decide
    by_cases hi : i' = i
    · subst hi
      simp only [Function.update_self, SignType.coe_neg]
      omega
    · simp only [Function.update_of_ne hi]
      omega

/-- The pinned peek's verdict is `choose` of the cell `δ` from tape `i`'s head. -/
private lemma zr_pinPeek_state {k : ℕ} {J : Type} {x : List (ZoneSym k)} (V : J → Prop)
    (i : Fin 2) (δ : SignType) (choose : Option (ZoneSym k) → Bool)
    (T : J → Fin 2 → ℤ → Option (ZoneSym k)) (p : J → Fin 2 → ℤ) (j : J) (hV : V j)
    (d : Cfg 2 (ZoneSym k) (Option Bool ⊕ Option Bool) x) (hd : zr_pinned (T j) (p j) d) :
    ((zr_pinPeekContract x V i δ choose T p).post j d).state =
      some (.inr (some (choose (T j i (p j i + δ))))) := by
  have h1 := ((zr_pinCell_step (x := x) V i δ none T p).2 j (d.mapState fun _ => none) hV
    ((zr_pinned_mapState_iff _).mpr hd)).2.1
  simp only [zr_pinPeekContract, zr_exitsContract, Contract.ofSegment_post, Contract.seq_post,
    Cfg.mapState_state]
  rw [zr_pinTest_state _ _ _ _ _ _ j _
      ((zr_pinned_mapState_iff (fun _ => (none : Option Bool))).mpr h1),
    Function.update_self]
  rfl

/-- The way back of a seam composite: only the second machine's states return. -/
private def zr_seqBack {S₁ S₂ : Type} (b : S₂ → Option (Option Bool)) :
    S₁ ⊕ S₂ → Option (Option Bool)
  | .inl _ => none
  | .inr s => b s

/-- The way back of a two-way branch: only the arms' states return. -/
private def zr_branchBack {S₀ S₁ S₂ : Type} (b₁ : S₁ → Option (Option Bool))
    (b₂ : S₂ → Option (Option Bool)) : (S₀ ⊕ S₁) ⊕ S₂ → Option (Option Bool)
  | .inl (.inl _) => none
  | .inl (.inr s) => b₁ s
  | .inr s => b₂ s

open Classical in
/-- The way back of a single live exit `d`, to the anchor-phase verdict `v`. -/
private noncomputable def zr_oneBack {S : Type} (d : S) (v : Bool) (s : S) :
    Option (Option Bool) :=
  if s = d then some (some v) else none

/-- A seam composite's exits are its way back's domain when the second machine's are. -/
private lemma zr_seqBack_hX {S₁ S₂ : Type} {X : Set (Option S₂)}
    {b : S₂ → Option (Option Bool)} (h : ∀ s, some s ∈ X ↔ b s ≠ none) :
    ∀ s : S₁ ⊕ S₂, some s ∈ Option.map Sum.inr '' X ↔ zr_seqBack b s ≠ none := by
  rintro (s | s)
  · simp only [zr_seqBack, ne_eq, not_true_eq_false, iff_false, Set.mem_image, not_exists,
      not_and]
    rintro (_ | _) _ h' <;> simp only [Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at h'
  · rw [zr_seqBack, ← h s]
    constructor
    · rintro ⟨(_ | u), hu, h'⟩ <;> simp only [Option.map_none, Option.map_some,
        reduceCtorEq, Option.some.injEq, Sum.inr.injEq] at h'
      exact h' ▸ hu
    · exact fun hs => ⟨some s, hs, rfl⟩

/-- A branch's exits are its way back's domain when the arms' are. -/
private lemma zr_branchBack_hX {S₀ S₁ S₂ : Type} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)}
    {b₁ : S₁ → Option (Option Bool)} {b₂ : S₂ → Option (Option Bool)}
    (h₁ : ∀ s, some s ∈ X₁ ↔ b₁ s ≠ none) (h₂ : ∀ s, some s ∈ X₂ ↔ b₂ s ≠ none) :
    ∀ s : (S₀ ⊕ S₁) ⊕ S₂, some s ∈ (Option.map (Sum.inl ∘ Sum.inr) '' X₁ ∪
      Option.map Sum.inr '' X₂) ↔ zr_branchBack b₁ b₂ s ≠ none := by
  rintro ((s | s) | s) <;> simp only [Set.mem_union, Set.mem_image, zr_branchBack]
  · simp only [ne_eq, not_true_eq_false, iff_false, not_or, not_exists, not_and]
    constructor <;> rintro (_ | _) _ h' <;> simp only [Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq, Function.comp_apply, Sum.inl.injEq] at h'
  · rw [← h₁ s]
    constructor
    · rintro (⟨(_ | u), hu, h'⟩ | ⟨(_ | u), hu, h'⟩) <;> simp only [Option.map_none,
        Option.map_some, reduceCtorEq, Option.some.injEq, Function.comp_apply, Sum.inl.injEq,
        Sum.inr.injEq] at h'
      exact h' ▸ hu
    · exact fun hs => Or.inl ⟨some s, hs, rfl⟩
  · rw [← h₂ s]
    constructor
    · rintro (⟨(_ | u), hu, h'⟩ | ⟨(_ | u), hu, h'⟩) <;> simp only [Option.map_none,
        Option.map_some, reduceCtorEq, Option.some.injEq, Function.comp_apply,
        Sum.inr.injEq] at h'
      exact h' ▸ hu
    · exact fun hs => Or.inr ⟨some s, hs, rfl⟩

/-- A single live exit is its way back's domain. -/
private lemma zr_oneBack_hX {S : Type} (d : S) (v : Bool) :
    ∀ s, some s ∈ ({some d} : Set (Option S)) ↔ zr_oneBack d v s ≠ none := by
  intro s
  rw [Set.mem_singleton_iff, Option.some.injEq, zr_oneBack]
  constructor
  · intro h
    rw [if_pos h]
    exact Option.some_ne_none _
  · intro h
    by_contra h'
    exact h (if_neg h')

/-- A pop round's exits are its way back's domain when its guarded arm's are. -/
private lemma zr_popBack_hX {S₀ S₁ S₂ S₃ : Type} {d : S₁} {w : Bool} {X : Set (Option S₂)}
    {b : S₂ → Option (Option Bool)} (h : ∀ s, some s ∈ X ↔ b s ≠ none) :
    ∀ s : (S₀ ⊕ S₁) ⊕ (S₃ ⊕ S₂), some s ∈ (Option.map (Sum.inl ∘ Sum.inr) '' {some d} ∪
      Option.map Sum.inr '' (Option.map Sum.inr '' X)) ↔
        zr_branchBack (zr_oneBack d w) (zr_seqBack b) s ≠ none :=
  zr_branchBack_hX (zr_oneBack_hX _ _) (zr_seqBack_hX h)

/-- **Every exit returns `w`**: from every entry configuration meeting the precondition, the
endpoint's state goes back to the anchor-phase verdict `w j`. -/
private def zr_BackIs {n : ℕ} {Γ S J : Type} {x : List Γ} {M : MultiTapeTM n Γ S} {e : S}
    {X : Set (Option S)} (C : Contract M e X J x) (b : S → Option (Option Bool))
    (w : J → Bool) : Prop :=
  ∀ j d, d.state = some e → C.pre j d → ∃ s, (C.post j d).state = some s ∧ b s = some (some (w j))

/-- A single live exit returns its verdict. -/
private lemma zr_BackIs_one {n : ℕ} {Γ S J : Type} {x : List Γ} {M : MultiTapeTM n Γ S} {e d : S}
    (C : Contract M e {some d} J x) (v : Bool) : zr_BackIs C (zr_oneBack d v) fun _ => v := by
  intro j c hc hp
  refine ⟨d, Set.mem_singleton_iff.mp (C.exit_mem j c hc hp), ?_⟩
  rw [zr_oneBack, if_pos rfl]

/-- A seam composite returns what its second machine returns. -/
private lemma zr_BackIs_seq {n : ℕ} {Γ S₁ S₂ J : Type} {x : List Γ} [DecidableEq S₁]
    {M₁ : MultiTapeTM n Γ S₁} {M₂ : MultiTapeTM n Γ S₂} {e₁ d₁ : S₁} {e₂ : S₂}
    {X₂ : Set (Option S₂)} {C₁ : Contract M₁ e₁ {some d₁} J x} {C₂ : Contract M₂ e₂ X₂ J x}
    {hl : ∀ j d, d.state = some e₁ → C₁.pre j d →
      C₂.pre j ((C₁.post j d).mapState fun _ => e₂)}
    {b : S₂ → Option (Option Bool)} {w : J → Bool} (h : zr_BackIs C₂ b w) :
    zr_BackIs (C₁.seq C₂ (fun j => j) hl) (zr_seqBack b) w := by
  intro j c hc hp
  rw [Contract.seq_pre] at hp
  have hc' : (c.mapState fun _ => e₁).state = some e₁ := by
    rw [Cfg.mapState_state, hc]
    rfl
  have hs1 := Set.mem_singleton_iff.mp (C₁.exit_mem j _ hc' hp)
  obtain ⟨s, hs, hb⟩ := h j _ (by rw [Cfg.mapState_state, hs1]; rfl) (hl j _ hc' hp)
  refine ⟨.inr s, ?_, hb⟩
  rw [Contract.seq_post, Cfg.mapState_state, hs]
  rfl

/-- **A pinned branch returns the selected arm's verdict.** -/
private lemma zr_BackIs_branch {k : ℕ} {S₀ S₁ S₂ J : Type} [DecidableEq S₀] [DecidableEq S₁]
    {x : List (ZoneSym k)} {M₀ : MultiTapeTM 2 (ZoneSym k) S₀}
    {M₁ : MultiTapeTM 2 (ZoneSym k) S₁} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₀ a₁ a₂ : S₀}
    {e₁ : S₁} {e₂ : S₂} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)} (he : a₁ ≠ a₂)
    {C₀ : Contract M₀ e₀ {some a₁, some a₂} J x} {C₁ : Contract M₁ e₁ X₁ J x}
    {C₂ : Contract M₂ e₂ X₂ J x} {V : J → Prop} {v : J → Bool}
    {T₀ T₁ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₀ p₁ : J → Fin 2 → ℤ} {τ₀ : J → ℕ}
    {L U : J → Fin 2 → ℤ} (h₀ : zr_PinStep C₀ V T₀ T₁ p₀ p₁ τ₀ L U)
    (hv : ∀ j d, V j → zr_pinned (T₀ j) (p₀ j) d →
      (C₀.post j d).state = some (if v j then a₁ else a₂))
    {hl₁ : ∀ j d, d.state = some e₀ → C₀.pre j d → (C₀.post j d).state = some a₁ →
      C₁.pre j ((C₀.post j d).mapState fun _ => e₁)}
    {hl₂ : ∀ j d, d.state = some e₀ → C₀.pre j d → (C₀.post j d).state = some a₂ →
      C₂.pre j ((C₀.post j d).mapState fun _ => e₂)}
    {b₁ : S₁ → Option (Option Bool)} {b₂ : S₂ → Option (Option Bool)} {w₁ w₂ : J → Bool}
    (h₁ : zr_BackIs C₁ b₁ w₁) (h₂ : zr_BackIs C₂ b₂ w₂) :
    zr_BackIs (Contract.branch he C₀ C₁ C₂ (fun j => j) (fun j => j) hl₁ hl₂)
      (zr_branchBack b₁ b₂) fun j => if v j then w₁ j else w₂ j := by
  intro j c hc0 hp
  rw [Contract.branch_pre] at hp
  have hc : (c.mapState fun _ => e₀).state = some e₀ := by
    rw [Cfg.mapState_state, hc0]
    rfl
  obtain ⟨hV, hd⟩ := h₀.1 j _ hp
  have hs := hv j _ hV hd
  cases hvj : v j
  · have hne : (C₀.post j (c.mapState fun _ => e₀)).state ≠ some a₁ := by
      rw [hs, hvj]
      simp only [Bool.false_eq_true, if_false, ne_eq, Option.some.injEq]
      exact he.symm
    have ha₂ : (C₀.post j (c.mapState fun _ => e₀)).state = some a₂ := by
      rw [hs, hvj]
      rfl
    obtain ⟨s, hs', hb⟩ := h₂ j _ (by rw [Cfg.mapState_state, ha₂]; rfl) (hl₂ j _ hc hp ha₂)
    refine ⟨.inr s, ?_, ?_⟩
    · rw [Contract.branch_post, if_neg hne, Cfg.mapState_state, hs']
      rfl
    · show b₂ s = some (some (if v j = true then w₁ j else w₂ j))
      rw [hb, hvj]
      rfl
  · have ha₁ : (C₀.post j (c.mapState fun _ => e₀)).state = some a₁ := by
      rw [hs, hvj]
      rfl
    obtain ⟨s, hs', hb⟩ := h₁ j _ (by rw [Cfg.mapState_state, ha₁]; rfl) (hl₁ j _ hc hp ha₁)
    refine ⟨.inl (.inr s), ?_, ?_⟩
    · rw [Contract.branch_post, if_pos ha₁, Cfg.mapState_state, Cfg.mapState_state, hs']
      rfl
    · show b₁ s = some (some (if v j = true then w₁ j else w₂ j))
      rw [hb, hvj]
      rfl

/-- No exit set built from live exits contains the halted state. -/
private lemma zr_none_not_mem_image {S T : Type} {X : Set (Option S)} (f : S → T)
    (h : none ∉ X) : none ∉ Option.map f '' X := by
  rintro ⟨(_ | _), hu, h'⟩
  · exact h hu
  · simp only [Option.map_some, reduceCtorEq] at h'

/-- A field of a doubling layout reads blank one cell in exactly when it is the home. -/
private lemma zr_second_isNone {α : Type} (w : List α) (n : ℕ) (hw : w.length = 2 ^ n) :
    (FinTM.bufferTape w 1).isNone = decide (n = 0) := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, FinTM.bufferTape_nat]
  by_cases h0 : n = 0
  · subst h0
    rw [List.getElem?_eq_none (by rw [hw]; norm_num)]
    rfl
  · rw [List.getElem?_eq_getElem (by rw [hw]; exact Nat.one_lt_two_pow h0)]
    simp only [Option.isNone_some, h0, decide_false]

/-- **The home test on the right layout**: one cell after field `n`'s start is blank exactly
when field `n` is the home. -/
private lemma zr_rhome_iff {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (n : ℕ) (hn : n ≤ ℓ) :
    (zonedTape z (zr_rstart n + 1)).isNone = decide (n = 0) := by
  rw [zr_rfield_at z n hn _ rfl 1 (by omega)
      (by rw [zr_rfield_length z n hn]; exact_mod_cast Nat.one_le_two_pow),
    zr_second_isNone _ n (zr_rfield_length z n hn)]

/-- **The home test on the left layout**, the same at left field `n`'s outermost cell. -/
private lemma zr_lhome_iff {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (n : ℕ) (hn : n ≤ ℓ) :
    (zonedTape z (zr_lstart n + 1)).isNone = decide (n = 0) := by
  rw [zr_lfield_at z n hn _ rfl 1 (by omega)
      (by rw [zr_lfield_length z n hn]; exact_mod_cast Nat.one_le_two_pow),
    zr_second_isNone _ n (zr_lfield_length z n hn)]

/-- The right layout's field starts increase. -/
private lemma zr_rstart_mono {m n : ℕ} (h : m ≤ n) : zr_rstart m ≤ zr_rstart n :=
  monotone_nat_of_le_succ (fun n => by
    have := zr_rstart_succ n
    have := Nat.two_pow_pos n
    omega) h

/-- The level-zero inward shift is the identity. -/
private lemma zr_shiftIn_zero {ℓ : ℕ} (w : ZoneContents ℓ) : zoneShiftIn true 0 w = w := by
  refine zr_contents_ext (zoneShiftIn_home true 0 w) ?_ ?_
  · funext j
    rw [zoneShiftIn_left, if_pos rfl]
  · funext j
    rw [zoneShiftIn_right, if_pos rfl, zoneShiftInW_eq, dif_neg (by omega)]

/-- The level-zero outward shift is the identity. -/
private lemma zr_shiftOut_zero {ℓ : ℕ} (w : ZoneContents ℓ) : zoneShiftOut false 0 w = w := by
  refine zr_contents_ext (zoneShiftOut_home false 0 w) ?_ ?_
  · funext j
    rw [zoneShiftOut_left, if_neg (by decide), zoneShiftOutW_eq, dif_neg (by omega)]
  · funext j
    rw [zoneShiftOut_right, if_neg (by decide)]
/-- A loop host's configuration at the anchor-phase state `v`, pinned at `(T, p)`, with `c`'s
input head and output. -/
private abbrev zr_hostCfg {k : ℕ} {B : Type} {x : List (ZoneSym k)}
    (c : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh B b) x) (v : Option Bool)
    (T : Fin 2 → ℤ → Option (ZoneSym k)) (p : Fin 2 → ℤ) :
    Cfg 2 (ZoneSym k) (Σ b, zr_hostPh B b) x :=
  { c with state := some ⟨false, v⟩, workTapes := T, workTapePos := p }

/-- **One round of a pinned loop**: on a loop host whose body is a pinned step from `(T j, p j)`
to `(T (nxt j), p (nxt j))`, its exit sent by `back` to the anchor or to the escape as `fin j`
says, a dispatch step and the body make a round from the anchor pinned at `j` to the
anchor-phase state `some (fin j)` pinned at `nxt j`, in `τ j + 2` steps, under any head relation
holding at the start and inside the body's box. -/
private lemma zr_pinRound {k : ℕ} {B J : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X J x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) {V : J → Prop}
    {T : J → Fin 2 → ℤ → Option (ZoneSym k)} {p : J → Fin 2 → ℤ} {nxt : J → J}
    {fin : J → Bool} {τ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (hstep : zr_PinStep C V T (fun j => T (nxt j)) p (fun j => p (nxt j)) τ L U)
    (hback : zr_BackIs C back fin)
    {sa sb : B} (hsa : back sa = some (some false)) (hsb : back sb = some (some true))
    (hsaX : some sa ∈ X) (hsbX : some sb ∈ X) (P : (Fin 2 → ℤ) → Prop) (j : J) (hV : V j)
    (c : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh B b) x) (hc : c.state = some ⟨false, some false⟩)
    (hcp : zr_pinned (T j) (p j) c) (hP0 : P c.workTapePos)
    (hPC : ∀ q : Fin 2 → ℤ, (∀ i, L j i ≤ q i ∧ q i ≤ U j i) → P q) :
    Round (zr_hostTM MB e back) ⟨false, some false⟩ {some ⟨false, some true⟩} P c
      (zr_hostCfg c (some (fin j)) (T (nxt j)) (p (nxt j))) (τ j + 2) := by
  have hrun1 := zr_host_dispatch_run MB e back c hc
  have hpin : zr_pinned (T j) (p j)
      (({ c with state := some ⟨true, e⟩ } : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh B b) x).mapState
        fun _ => e) := (zr_pinned_mapState_iff _).mpr hcp
  obtain ⟨hpre, hpost, hin, hout, htime, hbox⟩ := hstep.2 j _ hV hpin
  obtain ⟨s, hs, hbs⟩ := hback j _ (by rw [Cfg.mapState_state]; rfl) hpre
  have hB0 : (zr_hostBodyContract back C hnone hX).pre j { c with state := some ⟨true, e⟩ } := by
    rw [zr_hostBodyContract, Contract.inPhase_pre]
    exact hpre
  have hBt : (zr_hostBodyContract back C hnone hX).time j { c with state := some ⟨true, e⟩ } =
      τ j + 1 := by
    rw [zr_hostBodyContract, Contract.inPhase_time, htime]
  have hBpost : (zr_hostBodyContract back C hnone hX).post j { c with state := some ⟨true, e⟩ } =
      zr_hostCfg c (some (fin j)) (T (nxt j)) (p (nxt j)) := by
    rw [zr_hostBodyContract, Contract.inPhase_post]
    refine zr_bindState_eq _ _ _ ?_ ?_ hpost.1 hpost.2 ?_
    · rw [hs]
      show (back s).map _ = _
      rw [hbs]
      rfl
    · rw [hin, Cfg.mapState_inputPos]
    · rw [hout, Cfg.mapState_output]
  have hmem : ∀ v : Bool, ∀ s' : B, back s' = some (some v) → some s' ∈ X →
      some (⟨false, some v⟩ : Σ b, zr_hostPh B b) ∈
        {q | ∃ s, some s ∈ X ∧ q = zr_hostRed e back true s} := fun v s' h hx =>
    ⟨s', hx, by
      show _ = (back s').map _
      rw [h]
      rfl⟩
  have hend : ((zr_hostBodyContract back C hnone hX).post j
      { c with state := some ⟨true, e⟩ }).state ∈
      (insert (some ⟨false, some false⟩) {some ⟨false, some true⟩} :
        Set (Option (Σ b, zr_hostPh B b))) := by
    rw [hBpost]
    cases fin j
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  have hPC' : ∀ q, HeadBox ((zr_hostBodyContract back C hnone hX).lo j
      { c with state := some ⟨true, e⟩ })
      ((zr_hostBodyContract back C hnone hX).hi j { c with state := some ⟨true, e⟩ }) q →
      P q := by
    intro q hq
    refine hPC q fun i => ?_
    have h := (headBox_iff _ _ _).mp hq i
    rw [zr_hostBodyContract, Contract.inPhase_lo, Contract.inPhase_hi, Finset.mem_Icc] at h
    exact ⟨(hbox i).1.trans h.1, h.2.trans (hbox i).2⟩
  have hR := zr_round_of_body (zr_hostBodyContract back C hnone hX) j c _ hc hrun1 rfl hB0
    (hmem false sa hsa hsaX) (fun q hq => by
      rw [Set.mem_singleton_iff.mp hq]
      exact hmem true sb hsb hsbX) hend hP0 hPC'
  rwa [hBt, hBpost, show 1 + (τ j + 1) = τ j + 2 by omega] at hR

/-- **A pinned loop**: on a loop host whose body is a pinned step from `j` to `nxt j` (as in
`zr_pinRound`), validity passed on by every round that does not escape, the run from the anchor
pinned at `j₀` repeats the body along `j₀, nxt j₀, …` until round `n`, the first whose `fin` is
`true`, and stops at the escape pinned at `nxt^[n + 1] j₀`, after the rounds' times `τ + 2`,
under any head relation holding at each round's start and inside each round's body box. -/
private lemma zr_pinLoop {k : ℕ} {B J : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X J x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) {V : J → Prop}
    {T : J → Fin 2 → ℤ → Option (ZoneSym k)} {p : J → Fin 2 → ℤ} {nxt : J → J}
    {fin : J → Bool} {τ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (hstep : zr_PinStep C V T (fun j => T (nxt j)) p (fun j => p (nxt j)) τ L U)
    (hback : zr_BackIs C back fin)
    (hV : ∀ j, V j → fin j = false → V (nxt j))
    {sa sb : B} (hsa : back sa = some (some false)) (hsb : back sb = some (some true))
    (hsaX : some sa ∈ X) (hsbX : some sb ∈ X) (P : (Fin 2 → ℤ) → Prop) (j₀ : J) (n : ℕ)
    (hV₀ : V j₀) (hfin : fin (nxt^[n] j₀) = true) (hnf : ∀ m < n, fin (nxt^[m] j₀) = false)
    (hPs : ∀ m ≤ n, P (p (nxt^[m] j₀)))
    (hP : ∀ m ≤ n, ∀ q : Fin 2 → ℤ,
      (∀ i, L (nxt^[m] j₀) i ≤ q i ∧ q i ≤ U (nxt^[m] j₀) i) → P q)
    (c : Cfg 2 (ZoneSym k) (Σ b, zr_hostPh B b) x) (hc : c.state = some ⟨false, some false⟩)
    (hcp : zr_pinned (T j₀) (p j₀) c) :
    Segment (zr_hostTM MB e back) {some ⟨false, some true⟩} P c
      (zr_hostCfg c (some true) (T (nxt^[n + 1] j₀)) (p (nxt^[n + 1] j₀)))
      (∑ m ∈ Finset.range (n + 1), (τ (nxt^[m] j₀) + 2)) := by
  have hVm : ∀ m ≤ n, V (nxt^[m] j₀) := by
    intro m hm
    induction m with
    | zero => exact hV₀
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact hV _ (ih (by omega)) (hnf m (by omega))
  have hesc : (some ⟨false, some false⟩ : Option (Σ b, zr_hostPh B b)) ∉
      ({some ⟨false, some true⟩} : Set (Option (Σ b, zr_hostPh B b))) := by
    simp only [Set.mem_singleton_iff, Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and,
      Bool.false_eq_true, not_false_eq_true]
  have hround : ∀ m ≤ n,
      Round (zr_hostTM MB e back) ⟨false, some false⟩ {some ⟨false, some true⟩} P
        (zr_hostCfg c (some false) (T (nxt^[m] j₀)) (p (nxt^[m] j₀)))
        (zr_hostCfg c (some (fin (nxt^[m] j₀))) (T (nxt^[m + 1] j₀)) (p (nxt^[m + 1] j₀)))
        (τ (nxt^[m] j₀) + 2) := by
    intro m hm
    rw [Function.iterate_succ_apply']
    exact zr_pinRound back C hnone hX hstep hback hsa hsb hsaX hsbX P _ (hVm m hm) _ rfl
      ⟨rfl, rfl⟩ (hPs m hm) (hP m hm)
  have hseg : ∀ m ≤ n, Segment (zr_hostTM MB e back) {some ⟨false, some true⟩} P c
      (zr_hostCfg c (some false) (T (nxt^[m] j₀)) (p (nxt^[m] j₀)))
      (∑ r ∈ Finset.range m, (τ (nxt^[r] j₀) + 2)) := by
    intro m hm
    induction m with
    | zero =>
      have h0 : zr_hostCfg c (some false) (T (nxt^[0] j₀)) (p (nxt^[0] j₀)) = c :=
        Cfg.ext hc.symm rfl hcp.1.symm hcp.2.symm rfl
      rw [h0, Finset.sum_range_zero]
      exact Segment.zero (hcp.2 ▸ hPs 0 (Nat.zero_le _))
    | succ m ih =>
      have h2 := (hround m (by omega)).segment hesc
      rw [hnf m (by omega)] at h2
      rw [Finset.sum_range_succ]
      exact (ih (by omega)).trans h2
  have h2 := (hround n le_rfl).segment hesc
  rw [hfin] at h2
  rw [Finset.sum_range_succ]
  exact (hseg n le_rfl).trans h2

/-- **An anchor branch**: a pinned stationary test whose verdict at `j` is `a₁` exactly when
`v j`; on `a₁` it stops at the anchor leaf, otherwise it runs the pinned arm `C₂`. -/
private def zr_anchBranch {k : ℕ} {S₀ S₂ J : Type} [DecidableEq S₀] {x : List (ZoneSym k)}
    {M₀ : MultiTapeTM 2 (ZoneSym k) S₀} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₀ a₁ a₂ : S₀}
    {e₂ : S₂} {X₂ : Set (Option S₂)} (he : a₁ ≠ a₂) {C₀ : Contract M₀ e₀ {some a₁, some a₂} J x}
    {C₂ : Contract M₂ e₂ X₂ J x} {V : J → Prop} {v : J → Bool}
    {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ} {τ₀ τ₂ : J → ℕ}
    {L U : J → Fin 2 → ℤ} (h₀ : zr_PinStep C₀ V T₁ T₁ p₁ p₁ τ₀ L U)
    (hv : ∀ j d, V j → zr_pinned (T₁ j) (p₁ j) d →
      (C₀.post j d).state = some (if v j then a₁ else a₂))
    (h₂ : zr_PinStep C₂ (fun j => V j ∧ v j = false) T₁ T₂ p₁ p₂ τ₂ L U) :=
  Contract.branch he C₀ (zr_pinAnchorContract x (fun j => V j ∧ v j = true) T₁ p₁) C₂
    (fun j => j) (fun j => j) (zr_pin_blink true he h₀ hv rfl (zr_pinAnchor_step _ T₁ p₁))
    (zr_pin_blink false he h₀ hv rfl h₂)

/-- The anchor branch is a pinned step to the arm's endpoint pin, which the anchor already
meets at the indices it selects. -/
private lemma zr_anchBranch_step {k : ℕ} {S₀ S₂ J : Type} [DecidableEq S₀] {x : List (ZoneSym k)}
    {M₀ : MultiTapeTM 2 (ZoneSym k) S₀} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₀ a₁ a₂ : S₀}
    {e₂ : S₂} {X₂ : Set (Option S₂)} (he : a₁ ≠ a₂) {C₀ : Contract M₀ e₀ {some a₁, some a₂} J x}
    {C₂ : Contract M₂ e₂ X₂ J x} {V : J → Prop} {v : J → Bool}
    {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ} {τ₀ τ₂ : J → ℕ}
    {L U : J → Fin 2 → ℤ} (h₀ : zr_PinStep C₀ V T₁ T₁ p₁ p₁ τ₀ L U)
    (hv : ∀ j d, V j → zr_pinned (T₁ j) (p₁ j) d →
      (C₀.post j d).state = some (if v j then a₁ else a₂))
    (h₂ : zr_PinStep C₂ (fun j => V j ∧ v j = false) T₁ T₂ p₁ p₂ τ₂ L U)
    (hesc : ∀ j, V j → v j = true → T₂ j = T₁ j ∧ p₂ j = p₁ j)
    (hbox : ∀ j, V j → ∀ i, L j i ≤ p₁ j i ∧ p₁ j i ≤ U j i) :
    zr_PinStep (zr_anchBranch he h₀ hv h₂) V T₁ T₂ p₁ p₂
      (fun j => τ₀ j + 1 + if v j then 0 else τ₂ j) L U :=
  zr_PinStep_branch he h₀ hv (zr_PinStep_congr (zr_pinAnchor_step _ T₁ p₁)
    (fun j hj => (hesc j hj.1 hj.2).1.symm) (fun j hj => (hesc j hj.1 hj.2).2.symm)
    (fun _ _ => rfl) (fun j hj i => (hbox j hj.1 i).1) (fun j hj i => (hbox j hj.1 i).2)) h₂ _ _

/-- The anchor branch returns `u` at the anchor and the arm's verdict otherwise. -/
private lemma zr_anchBranch_back {k : ℕ} {S₀ S₂ J : Type} [DecidableEq S₀] {x : List (ZoneSym k)}
    {M₀ : MultiTapeTM 2 (ZoneSym k) S₀} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₀ a₁ a₂ : S₀}
    {e₂ : S₂} {X₂ : Set (Option S₂)} (he : a₁ ≠ a₂) {C₀ : Contract M₀ e₀ {some a₁, some a₂} J x}
    {C₂ : Contract M₂ e₂ X₂ J x} {V : J → Prop} {v : J → Bool}
    {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ} {τ₀ τ₂ : J → ℕ}
    {L U : J → Fin 2 → ℤ} (h₀ : zr_PinStep C₀ V T₁ T₁ p₁ p₁ τ₀ L U)
    (hv : ∀ j d, V j → zr_pinned (T₁ j) (p₁ j) d →
      (C₀.post j d).state = some (if v j then a₁ else a₂))
    (h₂ : zr_PinStep C₂ (fun j => V j ∧ v j = false) T₁ T₂ p₁ p₂ τ₂ L U)
    {b₂ : S₂ → Option (Option Bool)} {w₂ : J → Bool} (hb : zr_BackIs C₂ b₂ w₂) (u : Bool) :
    zr_BackIs (zr_anchBranch he h₀ hv h₂) (zr_branchBack (zr_oneBack (some false) u) b₂)
      fun j => if v j then u else w₂ j :=
  zr_BackIs_branch he h₀ hv (zr_BackIs_one _ u) hb

/-- A test's verdict state as a selection between its two verdicts. -/
private lemma zr_verdict_ite {S : Type} (f : Bool → S) (b : Bool) :
    some (f b) = some (if b then f true else f false) := by
  cases b <;> rfl

/-- The peek's two verdict states are distinct. -/
private lemma zr_peekNe :
    (Sum.inr (some true) : Option Bool ⊕ Option Bool) ≠ Sum.inr (some false) := by
  decide

/-- A pinned peek's verdict selects the branch `v` reads off the peeked cell. -/
private lemma zr_peek_verdict {k : ℕ} {J : Type} {x : List (ZoneSym k)} {V : J → Prop}
    {i : Fin 2} {δ : SignType} {choose : Option (ZoneSym k) → Bool}
    {T : J → Fin 2 → ℤ → Option (ZoneSym k)} {p : J → Fin 2 → ℤ} {v : J → Bool}
    (hv : ∀ j, v j = choose (T j i (p j i + δ))) :
    ∀ j d, V j → zr_pinned (T j) (p j) d →
      ((zr_pinPeekContract x V i δ choose T p).post j d).state =
        some (if v j then Sum.inr (some true) else Sum.inr (some false)) := fun j d hV hd => by
  rw [zr_pinPeek_state _ _ _ _ _ _ j hV d hd, ← hv]
  exact zr_verdict_ite (fun b => Sum.inr (some b)) _

/-- **A peek branch**: a pinned peek whose verdict is `v`, on `true` stopping at the anchor,
otherwise running the arm. -/
private def zr_peekBranch {k : ℕ} {S₂ J : Type} {x : List (ZoneSym k)} {V : J → Prop}
    {i : Fin 2} {δ : SignType} {choose : Option (ZoneSym k) → Bool}
    {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ} {τ₀ τ₂ : J → ℕ}
    {L U : J → Fin 2 → ℤ} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ J x} {v : J → Bool}
    (h₀ : zr_PinStep (zr_pinPeekContract x V i δ choose T₁ p₁) V T₁ T₁ p₁ p₁ τ₀ L U)
    (h₂ : zr_PinStep C₂ (fun j => V j ∧ v j = false) T₁ T₂ p₁ p₂ τ₂ L U)
    (hv : ∀ j, v j = choose (T₁ j i (p₁ j i + δ))) :=
  zr_anchBranch zr_peekNe h₀ (zr_peek_verdict hv) h₂

/-- A peek branch is a pinned step to the arm's endpoint pin, which the anchor meets at the
indices it selects. -/
private lemma zr_peekBranch_step {k : ℕ} {S₂ J : Type} {x : List (ZoneSym k)} {V : J → Prop}
    {i : Fin 2} {δ : SignType} {choose : Option (ZoneSym k) → Bool}
    {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ} {τ₀ τ₂ : J → ℕ}
    {L U : J → Fin 2 → ℤ} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ J x} {v : J → Bool}
    (h₀ : zr_PinStep (zr_pinPeekContract x V i δ choose T₁ p₁) V T₁ T₁ p₁ p₁ τ₀ L U)
    (h₂ : zr_PinStep C₂ (fun j => V j ∧ v j = false) T₁ T₂ p₁ p₂ τ₂ L U)
    (hv : ∀ j, v j = choose (T₁ j i (p₁ j i + δ)))
    (hesc : ∀ j, V j → v j = true → T₂ j = T₁ j ∧ p₂ j = p₁ j)
    (hbox : ∀ j, V j → ∀ i, L j i ≤ p₁ j i ∧ p₁ j i ≤ U j i) :
    zr_PinStep (zr_peekBranch h₀ h₂ hv) V T₁ T₂ p₁ p₂
      (fun j => τ₀ j + 1 + if v j then 0 else τ₂ j) L U :=
  zr_anchBranch_step zr_peekNe h₀ (zr_peek_verdict hv) h₂ hesc hbox

/-- A peek branch returns `u` at the anchor and the arm's verdict otherwise. -/
private lemma zr_peekBranch_back {k : ℕ} {S₂ J : Type} {x : List (ZoneSym k)} {V : J → Prop}
    {i : Fin 2} {δ : SignType} {choose : Option (ZoneSym k) → Bool}
    {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ} {τ₀ τ₂ : J → ℕ}
    {L U : J → Fin 2 → ℤ} {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ J x} {v : J → Bool}
    (h₀ : zr_PinStep (zr_pinPeekContract x V i δ choose T₁ p₁) V T₁ T₁ p₁ p₁ τ₀ L U)
    (h₂ : zr_PinStep C₂ (fun j => V j ∧ v j = false) T₁ T₂ p₁ p₂ τ₂ L U)
    (hv : ∀ j, v j = choose (T₁ j i (p₁ j i + δ)))
    {b₂ : S₂ → Option (Option Bool)} {w₂ : J → Bool} (hb : zr_BackIs C₂ b₂ w₂) (u : Bool) :
    zr_BackIs (zr_peekBranch h₀ h₂ hv) (zr_branchBack (zr_oneBack (some false) u) b₂)
      fun j => if v j then u else w₂ j :=
  zr_anchBranch_back zr_peekNe h₀ (zr_peek_verdict hv) h₂ hb u

/-- Writing scratch's cell `r` in a two-tape family writes its second tape. -/
private lemma zr_tapes_write {k : ℕ} (A B : ℤ → Option (ZoneSym k)) (r : ℤ)
    (v : Option (ZoneSym k)) :
    Function.update (zr_tapes A B) 1 (Function.update (zr_tapes A B 1) r v) =
      zr_tapes A (Function.update B r v) := by
  funext i
  fin_cases i <;> rfl

/-- Moving scratch's head in a head pair. -/
private lemma zr_heads_set1 (a b c : ℤ) : Function.update (zr_heads a b) 1 c = zr_heads a c := by
  funext i
  fin_cases i <;> rfl

/-- Moving the zoned head in a head pair. -/
private lemma zr_heads_set0 (a b c : ℤ) : Function.update (zr_heads a b) 0 c = zr_heads c b := by
  funext i
  fin_cases i <;> rfl

/-- The slot test on a cell that is not blank reads its slot. -/
private lemma zr_slotEmpty_iff {k : ℕ} (t : Fin k) {o : Option (ZoneSym k)} (h : o.isSome) :
    zr_slotEmpty t o = true ↔ o.map (zoneSlotOf t) = some none := by
  cases o with
  | none => exact absurd h Bool.false_ne_true
  | some c => rw [zr_slotEmpty, Option.map_some, Option.some.injEq, Option.isNone_iff_eq_none]

/-- A field of `2^i` cells, read from its first cell, is not blank there. -/
private lemma zr_field_isSome {k : ℕ} {T : ℤ → Option (ZoneSym k)} {a : ℤ}
    {w : List (ZoneSym k)} {i : ℕ}
    (h : ∀ q, -1 ≤ q → q ≤ (w.length : ℤ) → T (a + q) = FinTM.bufferTape w q)
    (hw : w.length = 2 ^ i) : (T a).isSome := by
  have h0 := h 0 (by omega) (by omega)
  rw [add_zero] at h0
  rw [h0, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, FinTM.bufferTape_nat,
    List.getElem?_eq_getElem (by rw [hw]; exact Nat.two_pow_pos i)]
  rfl

/-- A right field's first cell is not blank. -/
private lemma zr_rstart_isSome {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : ℕ) (hi : i ≤ ℓ) :
    (zonedTape z (zr_rstart i)).isSome :=
  zr_field_isSome (zr_rfield_at z i hi _ rfl) (zr_rfield_length z i hi)

/-- The state type of a contract's machine, read off its type. -/
private abbrev zr_stOf {n : ℕ} {Γ S I : Type} {x : List Γ} {M : MultiTapeTM n Γ S}
    {entry : S} {X : Set (Option S)} (_ : Contract M entry X I x) : Type :=
  S

/-- The live exit of a single-exit contract, read off its type. -/
private abbrev zr_exitOf {n : ℕ} {Γ S I : Type} {x : List Γ} {M : MultiTapeTM n Γ S}
    {entry d : S} (_ : Contract M entry {some d} I x) : S :=
  d

/-- The exit set of a contract, read off its type. -/
private abbrev zr_exitsOf {n : ℕ} {Γ S I : Type} {x : List Γ} {M : MultiTapeTM n Γ S}
    {entry : S} {X : Set (Option S)} (_ : Contract M entry X I x) : Set (Option S) :=
  X

/-- A return verdict restated pointwise. -/
private lemma zr_BackIs_congr {n : ℕ} {Γ S J : Type} {x : List Γ} {M : MultiTapeTM n Γ S}
    {e : S} {X : Set (Option S)} {C : Contract M e X J x} {b : S → Option (Option Bool)}
    {w w' : J → Bool} (h : zr_BackIs C b w) (hw : ∀ j, w j = w' j) : zr_BackIs C b w' := by
  intro j d hd hp
  obtain ⟨s, hs, hb⟩ := h j d hd hp
  exact ⟨s, hs, by rw [hb, hw]⟩

/-- A single live exit is not the halted state. -/
private lemma zr_none_not_mem_single {S : Type} (d : S) : none ∉ ({some d} : Set (Option S)) :=
  fun h => by cases Set.mem_singleton_iff.mp h

/-- A union of exit sets without the halted state has none. -/
private lemma zr_none_not_mem_union {S : Type} {A B : Set (Option S)} (ha : none ∉ A)
    (hb : none ∉ B) : none ∉ A ∪ B :=
  fun h => h.elim ha hb

/-- A two-way exit set whose first arm is a single exit has no halted state when its second arm
has none: the shape of every guard's and every round's exits. -/
private lemma zr_none_arm {S T U : Type} {f : S → U} {g : T → U} {d : S} {Y : Set (Option T)}
    (h : none ∉ Y) : none ∉ Option.map f '' {some d} ∪ Option.map g '' Y :=
  zr_none_not_mem_union (zr_none_not_mem_image _ (zr_none_not_mem_single _))
    (zr_none_not_mem_image _ h)

/-- Two single exits, the anchor's and an arm's. -/
private lemma zr_none_one {S T U : Type} {f : S → U} {g : T → U} {d : S} {e : T} :
    none ∉ Option.map f '' {some d} ∪ Option.map g '' {some e} :=
  zr_none_arm (zr_none_not_mem_single _)

/-- A seam into a two-way exit set: a descending round's exits. -/
private lemma zr_none_dn {S T U W : Type} {f : S → U} {g : T → U} {f' : U → W} {d : S}
    {Y : Set (Option T)} (h : none ∉ Y) :
    none ∉ Option.map f' '' (Option.map f '' {some d} ∪ Option.map g '' Y) :=
  zr_none_not_mem_image _ (zr_none_arm h)

/-- A single exit and a seam's arm: a pop round's exits. -/
private lemma zr_none_up {S T V U : Type} {f : S → U} {g : T → U} {g' : V → T} {d : S}
    {Y : Set (Option V)} (h : none ∉ Y) :
    none ∉ Option.map f '' {some d} ∪ Option.map g '' (Option.map g' '' Y) :=
  zr_none_arm (zr_none_not_mem_image _ h)

/-- **A pass index**: the data, the anchor's field, and scratch as a count stack — a base tape
`β`, blank from `b` on, with count marks on `[b, s)` and the head at `s`. -/
private structure zr_Px (k : ℕ) where
  /-- the data -/
  D : ZoneData k
  /-- the anchor's field -/
  i : ℕ
  /-- the base scratch tape -/
  β : ℤ → Option (ZoneSym k)
  /-- the stack's base -/
  b : ℤ
  /-- scratch's head, the stack's top -/
  s : ℤ

/-- The count stack: marks on `[b, s)` over the base tape. -/
private def zr_stk {k : ℕ} (β : ℤ → Option (ZoneSym k)) (b s : ℤ) (r : ℤ) :
    Option (ZoneSym k) :=
  if b ≤ r ∧ r < s then some (.inl false) else β r

/-- A pass index's scratch tape. -/
private abbrev zr_pσ {k : ℕ} (P : zr_Px k) : ℤ → Option (ZoneSym k) := zr_stk P.β P.b P.s

/-- A pass's anchor tapes: the zoned tape of the data, and the count stack. -/
private abbrev zr_pT {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes (zonedTape P.D.2) (zr_pσ P)

/-- A pass's validity: the anchor's field laid out, the stack over a base blank from its base,
the head at or above the base. -/
private def zr_pxV {k : ℕ} (P : zr_Px k) : Prop :=
  P.i ≤ P.D.1 ∧ P.b ≤ P.s ∧ ∀ r, P.b ≤ r → P.β r = none

/-- The count stack is blank from its top on. -/
private lemma zr_stk_blank {k : ℕ} {P : zr_Px k} (hV : zr_pxV P) :
    ∀ r, P.s ≤ r → zr_pσ P r = none := by
  intro r hr
  rw [zr_pσ, zr_stk, if_neg (by omega)]
  exact hV.2.2 r (by have := hV.2.1; omega)

/-- **A push**: a mark at the top raises the stack. -/
private lemma zr_stk_push {k : ℕ} (β : ℤ → Option (ZoneSym k)) {b s : ℤ} (hb : b ≤ s) :
    Function.update (zr_stk β b s) s (some (.inl false)) = zr_stk β b (s + 1) := by
  funext r
  by_cases hr : r = s
  · rw [hr, Function.update_self, zr_stk, if_pos (by omega)]
  · rw [Function.update_of_ne hr, zr_stk, zr_stk]
    by_cases h : b ≤ r ∧ r < s
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- **A pop**: blanking the top mark lowers the stack. -/
private lemma zr_stk_pop {k : ℕ} {β : ℤ → Option (ZoneSym k)} {b s : ℤ}
    (hβ : β (s - 1) = none) :
    Function.update (zr_stk β b s) (s - 1) none = zr_stk β b (s - 1) := by
  funext r
  by_cases hr : r = s - 1
  · rw [hr, Function.update_self, zr_stk, if_neg (by omega), hβ]
  · rw [Function.update_of_ne hr, zr_stk, zr_stk]
    by_cases h : b ≤ r ∧ r < s
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- The cell below the stack's top: a mark on a nonempty stack, the base's cell otherwise. -/
private lemma zr_stk_top {k : ℕ} (β : ℤ → Option (ZoneSym k)) (b s : ℤ) :
    zr_stk β b s (s - 1) = if b < s then some (.inl false) else β (s - 1) := by
  rw [zr_stk]
  by_cases h : b < s
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- **A pass's next index**: track `t` changed by `F` at the anchor's field, the field moved by
`G`, the stack's top moved by `δ`. -/
private abbrev zr_pxNxt {k : ℕ} (t : Fin k) (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ)
    (G : ℕ → ℕ) (δ : ℤ) (P : zr_Px k) : zr_Px k :=
  ⟨⟨P.D.1, Function.update P.D.2 t (F P.D.1 P.i (P.D.2 t))⟩, G P.i, P.β, P.b, P.s + δ⟩

/-- Track `t` after `m` rounds of a pass. -/
private abbrev zr_pxFold {k : ℕ} (t : Fin k) (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ)
    (G : ℕ → ℕ) (P : zr_Px k) (m : ℕ) : ZoneContents P.D.1 :=
  (List.range m).foldl (fun w r => F P.D.1 (G^[r] P.i) w) (P.D.2 t)

/-- **A pass after `m` rounds**: track `t` changed at the fields `P.i, G P.i, …`, every other
track and the stack's base kept, the field and the top moved `m` times. -/
private lemma zr_px_iter {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) (G : ℕ → ℕ) (δ : ℤ) (P : zr_Px k)
    (m : ℕ) :
    ((zr_pxNxt t F G δ)^[m] P).D = ⟨P.D.1, Function.update P.D.2 t (zr_pxFold t F G P m)⟩ ∧
      ((zr_pxNxt t F G δ)^[m] P).i = G^[m] P.i ∧ ((zr_pxNxt t F G δ)^[m] P).β = P.β ∧
      ((zr_pxNxt t F G δ)^[m] P).b = P.b ∧ ((zr_pxNxt t F G δ)^[m] P).s = P.s + m * δ := by
  induction m with
  | zero =>
    refine ⟨?_, rfl, rfl, rfl, by rw [Nat.cast_zero, zero_mul, add_zero]; rfl⟩
    show P.D = ⟨P.D.1, Function.update P.D.2 t (P.D.2 t)⟩
    rw [Function.update_eq_self]
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_, h3, h4, ?_⟩
    · show (⟨((zr_pxNxt t F G δ)^[m] P).D.1, Function.update ((zr_pxNxt t F G δ)^[m] P).D.2 t
        (F _ ((zr_pxNxt t F G δ)^[m] P).i (((zr_pxNxt t F G δ)^[m] P).D.2 t))⟩ : ZoneData k) = _
      rw [h1, h2]
      dsimp only
      unfold zr_pxFold
      rw [Function.update_self, Function.update_idem, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    · show G ((zr_pxNxt t F G δ)^[m] P).i = _
      rw [h2, Function.iterate_succ_apply']
    · show ((zr_pxNxt t F G δ)^[m] P).s + δ = _
      rw [h5]
      push_cast
      ring

/-- Stepping down and up `m` times. -/
private lemma zr_iterate_step (m n : ℕ) :
    (fun i => i - 1)^[m] n = n - m ∧ (fun i => i + 1)^[m] n = n + m := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1, ih.2]
    exact ⟨by omega, by omega⟩

/-- Stepping down `m` times. -/
private lemma zr_iterate_pred (m n : ℕ) : (fun i => i - 1)^[m] n = n - m :=
  (zr_iterate_step m n).1

/-- Stepping up `m` times. -/
private lemma zr_iterate_succ (m n : ℕ) : (fun i => i + 1)^[m] n = n + m :=
  (zr_iterate_step m n).2

/-- **A pass as a contract on its loop**: a pinned round body from each anchor to the next
index's, escaping after `n j` further rounds, its round boxes inside one pass box, runs from the
anchor to the escape after the rounds' times. -/
private noncomputable def zr_passContract {k : ℕ} {B J : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X J x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) {V : J → Prop}
    {T : J → Fin 2 → ℤ → Option (ZoneSym k)} {p : J → Fin 2 → ℤ} {nxt : J → J}
    {fin : J → Bool} {τ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (hstep : zr_PinStep C V T (fun j => T (nxt j)) p (fun j => p (nxt j)) τ L U)
    (hback : zr_BackIs C back fin) (hV : ∀ j, V j → fin j = false → V (nxt j))
    {sa sb : B} (hsa : back sa = some (some false)) (hsb : back sb = some (some true))
    (n : J → ℕ) (hfin : ∀ j, V j → fin (nxt^[n j] j) = true)
    (hnf : ∀ j, V j → ∀ m < n j, fin (nxt^[m] j) = false) (lo hi : J → Fin 2 → ℤ)
    (hbox : ∀ j, V j → ∀ m ≤ n j, ∀ i, lo j i ≤ L (nxt^[m] j) i ∧ U (nxt^[m] j) i ≤ hi j i)
    (hanchor : ∀ j, ∀ i, L j i ≤ p j i ∧ p j i ≤ U j i) :
    Contract (zr_hostTM MB e back) ⟨false, some false⟩ {some ⟨false, some true⟩} J x :=
  Contract.ofSegment (fun j c => V j ∧ zr_pinned (T j) (p j) c)
    (fun j _ => ∑ m ∈ Finset.range (n j + 1), (τ (nxt^[m] j) + 2))
    (fun j c => zr_hostCfg c (some true) (T (nxt^[n j + 1] j)) (p (nxt^[n j + 1] j)))
    (fun j _ => lo j) (fun j _ => hi j)
    (fun j c hc hp => zr_pinLoop back C hnone hX hstep hback hV hsa hsb
      ((hX _).mpr (by rw [hsa]; exact Option.some_ne_none _))
      ((hX _).mpr (by rw [hsb]; exact Option.some_ne_none _)) (HeadBox (lo j) (hi j)) j (n j)
      hp.1 (hfin j hp.1) (hnf j hp.1)
      (fun m hm => (headBox_iff _ _ _).mpr fun i => Finset.mem_Icc.mpr
        ⟨(hbox j hp.1 m hm i).1.trans (hanchor _ i).1,
          (hanchor _ i).2.trans (hbox j hp.1 m hm i).2⟩)
      (fun m hm q hq => (headBox_iff _ _ _).mpr fun i => Finset.mem_Icc.mpr
        ⟨(hbox j hp.1 m hm i).1.trans (hq i).1, (hq i).2.trans (hbox j hp.1 m hm i).2⟩) c hc hp.2)
    (fun _ _ _ _ => Set.mem_singleton _)

/-- **A pass is a pinned step**: from the anchor pinned at `j`, it stops at the escape pinned at
`nxt^[n j + 1] j` after its rounds, in its box. -/
private lemma zr_pass_step {k : ℕ} {B J : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X J x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) {V : J → Prop}
    {T : J → Fin 2 → ℤ → Option (ZoneSym k)} {p : J → Fin 2 → ℤ} {nxt : J → J}
    {fin : J → Bool} {τ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (hstep : zr_PinStep C V T (fun j => T (nxt j)) p (fun j => p (nxt j)) τ L U)
    (hback : zr_BackIs C back fin) (hV : ∀ j, V j → fin j = false → V (nxt j))
    {sa sb : B} (hsa : back sa = some (some false)) (hsb : back sb = some (some true))
    (n : J → ℕ) (hfin : ∀ j, V j → fin (nxt^[n j] j) = true)
    (hnf : ∀ j, V j → ∀ m < n j, fin (nxt^[m] j) = false) (lo hi : J → Fin 2 → ℤ)
    (hbox : ∀ j, V j → ∀ m ≤ n j, ∀ i, lo j i ≤ L (nxt^[m] j) i ∧ U (nxt^[m] j) i ≤ hi j i)
    (hanchor : ∀ j, ∀ i, L j i ≤ p j i ∧ p j i ≤ U j i) :
    zr_PinStep (zr_passContract back C hnone hX hstep hback hV hsa hsb n hfin hnf lo hi hbox
        hanchor) V T (fun j => T (nxt^[n j + 1] j)) p (fun j => p (nxt^[n j + 1] j))
      (fun j => ∑ m ∈ Finset.range (n j + 1), (τ (nxt^[m] j) + 2)) lo hi := by
  refine ⟨fun j d hd => ?_, fun j d hVj hd => ?_⟩
  · rw [zr_passContract, Contract.ofSegment_pre] at hd
    exact hd
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · rw [zr_passContract, Contract.ofSegment_pre]
    exact ⟨hVj, hd⟩
  · rw [zr_passContract, Contract.ofSegment_post]
    exact ⟨rfl, rfl⟩
  · rw [zr_passContract, Contract.ofSegment_post]
  · rw [zr_passContract, Contract.ofSegment_post]
  · rw [zr_passContract, Contract.ofSegment_time]
  · rw [zr_passContract, Contract.ofSegment_lo, Contract.ofSegment_hi]
    exact ⟨le_rfl, le_rfl⟩

/-- **A pass as a pinned segment**: its contract on its loop, with its pinned step. -/
private noncomputable def zr_passSeg {k : ℕ} {B J : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X J x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) {V : J → Prop}
    {T : J → Fin 2 → ℤ → Option (ZoneSym k)} {p : J → Fin 2 → ℤ} {nxt : J → J}
    {fin : J → Bool} {τ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (hstep : zr_PinStep C V T (fun j => T (nxt j)) p (fun j => p (nxt j)) τ L U)
    (hback : zr_BackIs C back fin) (hV : ∀ j, V j → fin j = false → V (nxt j))
    {sa sb : B} (hsa : back sa = some (some false)) (hsb : back sb = some (some true))
    (n : J → ℕ) (hfin : ∀ j, V j → fin (nxt^[n j] j) = true)
    (hnf : ∀ j, V j → ∀ m < n j, fin (nxt^[m] j) = false) (lo hi : J → Fin 2 → ℤ)
    (hbox : ∀ j, V j → ∀ m ≤ n j, ∀ i, lo j i ≤ L (nxt^[m] j) i ∧ U (nxt^[m] j) i ≤ hi j i)
    (hanchor : ∀ j, ∀ i, L j i ≤ p j i ∧ p j i ≤ U j i) :
    zr_PinSeg x (zr_hostTM MB e back) ⟨false, some false⟩ ⟨false, some true⟩ V T
      (fun j => T (nxt^[n j + 1] j)) p (fun j => p (nxt^[n j + 1] j))
      (fun j => ∑ m ∈ Finset.range (n j + 1), (τ (nxt^[m] j) + 2)) lo hi :=
  ⟨_, zr_pass_step back C hnone hX hstep hback hV hsa hsb n hfin hnf lo hi hbox hanchor⟩

/-- A shift index's tapes: the zoned tape of its data, and its scratch. -/
private abbrev zr_aT {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes (zonedTape J.D.2) J.σ

/-- A right shift index's heads: the zoned head at field `J.i`'s start. -/
private abbrev zr_rA {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ := zr_heads (zr_rstart J.i) J.s

/-- What every caller of a level move supplies: the level inside the layout and scratch blank
from its head on. -/
private def zr_shPre {k : ℕ} (J : zr_Ix k) : Prop :=
  1 ≤ J.i ∧ J.i < J.D.1 ∧ ∀ r, J.s ≤ r → J.σ r = none

/-- The right inward shift's guard verdict at `J`: `true` when the guard is off, the receiver's
innermost slot occupied. -/
private abbrev zr_inOff {k : ℕ} (t : Fin k) (J : zr_Ix k) : Bool :=
  (fun c => !zr_slotEmpty t c) (zr_aT J 0 (zr_rA J 0))

/-- With the guard on, the right inward shift's index is valid. -/
private lemma zr_inOff_valid {k : ℕ} {t : Fin k} {J : zr_Ix k} (hJ : zr_shPre J)
    (hg : zr_inOff t J = false) : zr_inV t J := by
  obtain ⟨h1, h2, hσ⟩ := hJ
  refine ⟨h1, h2, ?_, hσ⟩
  have hs : zr_slotEmpty t (zonedTape J.D.2 (zr_rstart J.i)) = true := by
    simpa only [Bool.not_eq_false'] using hg
  rw [zr_slotEmpty_iff t (zr_rstart_isSome J.D.2 _ (by omega)), zr_rstart,
    if_neg (by omega)] at hs
  exact hs

/-- With the guard off, the shifted tape is the zoned tape. -/
private lemma zr_inOff_esc {k : ℕ} {t : Fin k} {J : zr_Ix k} (hJ : zr_shPre J)
    (hoff : zr_inOff t J = true) : zr_tapes (zr_inZ t J) J.σ = zr_aT J := by
  obtain ⟨h1, h2, -⟩ := hJ
  have hs : zr_slotEmpty t (zonedTape J.D.2 (zr_rstart J.i)) = false := by
    simpa only [Bool.not_eq_true'] using hoff
  have hne : (J.D.2 t).right ⟨J.i - 1, by omega⟩ ≠ [] := by
    intro he
    have h := (zr_inGuard_iff J.D.2 t J.i h1 h2).mpr he
    rw [← zr_slotEmpty_iff t (zr_rstart_isSome J.D.2 _ (by omega)), hs] at h
    exact Bool.false_ne_true h
  rw [zr_inZ_off t J h1 h2 hne]

/-- The right inward shift's guard test, stationary at the receiver's start, in the shift's
box. -/
private lemma zr_inTest_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_pinTestContract x V 0 (fun c => !zr_slotEmpty t c) 0 (fun j => zr_aT (g j))
        fun j => zr_rA (g j)) V (fun j => zr_aT (g j)) (fun j => zr_aT (g j))
      (fun j => zr_rA (g j)) (fun j => zr_rA (g j)) (fun _ => 1) (fun j => zr_inL (g j))
      (fun j => zr_inU (g j)) :=
  zr_PinStep_congr (zr_pinTest_step _ 0 _ 0 _ _) (fun _ _ => rfl)
    (fun _ _ => by rw [SignType.coe_zero, add_zero, Function.update_eq_self]) (fun _ _ => rfl)
    (fun j hj i => by
      have h1 := (hV j hj).1
      have hm := zr_rstart_mono (show (g j).i - 1 ≤ (g j).i by omega)
      rw [SignType.coe_zero, add_zero, Function.update_eq_self, min_self]
      fin_cases i
      · show zr_rstart ((g j).i - 1) - 1 ≤ zr_rstart (g j).i
        omega
      · exact le_refl (g j).s)
    (fun j hj i => by
      have hm := zr_rstart_mono (show (g j).i ≤ (g j).i + 1 by omega)
      rw [SignType.coe_zero, add_zero, Function.update_eq_self, max_self]
      fin_cases i
      · show zr_rstart (g j).i ≤ zr_rstart ((g j).i + 1) + 4 * (zr_hh (g j) : ℤ)
        omega
      · show (g j).s ≤ (g j).s + 8 * (zr_hh (g j) : ℤ) + 2
        omega)

/-- **The guarded right inward shift** over the shift index `g j`: off, stop at the anchor; on,
shift. -/
private def zr_grdIn {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k)) (g : I → zr_Ix k)
    (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :=
  zr_anchBranch (by decide : (some true : Option Bool) ≠ some false) (zr_inTest_step t x g V hV)
    (fun j d _ hd => by
      rw [zr_pinTest_state _ _ _ _ _ _ j d hd]
      exact zr_verdict_ite some _)
    (zr_PinStep_re (zr_inSeg_spec t x) g (fun j => V j ∧ zr_inOff t (g j) = false)
      fun j h => zr_inOff_valid (hV j h.1) h.2)

/-- The guarded right inward shift ends at the shifted tape either way. -/
private lemma zr_grdIn_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_grdIn t x g V hV) V (fun j => zr_aT (g j))
      (fun j => zr_tapes (zr_inZ t (g j)) (g j).σ) (fun j => zr_rA (g j)) (fun j => zr_rA (g j))
      (fun j => 1 + 1 + if zr_inOff t (g j) then 0 else 76 * zr_hh (g j) + 77)
      (fun j => zr_inL (g j)) (fun j => zr_inU (g j)) :=
  zr_anchBranch_step _ _ _ _ (fun j hj hoff => ⟨zr_inOff_esc (hV j hj) hoff, rfl⟩)
    fun j hj i => by
      have h1 := (hV j hj).1
      have hm := zr_rstart_mono (show (g j).i - 1 ≤ (g j).i by omega)
      have hm' := zr_rstart_mono (show (g j).i ≤ (g j).i + 1 by omega)
      fin_cases i
      · exact ⟨show zr_rstart ((g j).i - 1) - 1 ≤ zr_rstart (g j).i by omega,
          show zr_rstart (g j).i ≤ zr_rstart ((g j).i + 1) + 4 * (zr_hh (g j) : ℤ) by omega⟩
      · exact ⟨le_refl (g j).s, show (g j).s ≤ (g j).s + 8 * (zr_hh (g j) : ℤ) + 2 by omega⟩

/-- The way back of a branch from the one-cell leaf's verdict pair to a single-exit arm: the
leaf's `some false` returns `v`, the arm's exit `e` returns `false`. -/
private noncomputable abbrev zr_brBack {S₀ S₂ : Type} (v : Bool) (e : S₂) :
    (S₀ ⊕ Option Bool) ⊕ S₂ → Option (Option Bool) :=
  zr_branchBack (zr_oneBack (some false) v) (zr_oneBack e false)

/-- The guarded right inward shift's way back, both exits to the anchor. -/
private noncomputable def zr_grdInBack {k : ℕ} (t : Fin k) :
    (Option Bool ⊕ Option Bool) ⊕ zr_stOf (zr_inSeg t ([] : List (ZoneSym k))).C →
      Option (Option Bool) :=
  zr_brBack false (zr_exitOf (zr_inSeg t ([] : List (ZoneSym k))).C)

/-- The guarded right inward shift returns to the anchor. -/
private lemma zr_grdIn_back {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_BackIs (zr_grdIn t x g V hV) (zr_grdInBack t) fun _ => false :=
  zr_BackIs_congr (zr_anchBranch_back _ _ _ _ (zr_BackIs_one _ false) false)
    fun j => by cases zr_inOff t (g j) <;> rfl

/-- The guarded right inward shift's exits are its way back's domain. -/
private lemma zr_grdIn_hX {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    ∀ s, some s ∈ zr_exitsOf (zr_grdIn t x g V hV) ↔ zr_grdInBack t s ≠ none :=
  zr_branchBack_hX (zr_oneBack_hX _ _) (zr_oneBack_hX _ _)

/-- The guarded right inward shift never halts. -/
private lemma zr_grdIn_none {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    none ∉ zr_exitsOf (zr_grdIn t x g V hV) :=
  zr_none_one

/-- A right pass's anchor heads: the zoned head at field `P.i`'s start, scratch at the top. -/
private abbrev zr_rH {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_rstart P.i) P.s

/-- The descending right pass's shift index: level `P.i - 1`, after the push. -/
private abbrev zr_p1G {k : ℕ} (P : zr_Px k) : zr_Ix k :=
  ⟨P.D, P.i - 1, zr_stk P.β P.b (P.s + 1), P.s + 1⟩

/-- A descending pass's unconditional next index: one field in, its level changed by `F`, one
mark pushed. -/
private abbrev zr_dnF {k : ℕ} (t : Fin k) (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) :
    zr_Px k → zr_Px k :=
  zr_pxNxt t F (fun i => i - 1) 1

/-- **The descending right pass's next index**: field `P.i - 1`, whose level is shifted inward
(the identity at the home), one count mark pushed. -/
private abbrev zr_p1Nxt {k : ℕ} (t : Fin k) : zr_Px k → zr_Px k :=
  zr_dnF t fun _ i w => zoneShiftIn true (i - 1) w

/-- The descending right pass's validity: a pass index whose anchor is past the home. -/
private def zr_p1V {k : ℕ} (P : zr_Px k) : Prop := zr_pxV P ∧ 1 ≤ P.i

/-- The descending right pass's round box, its lower corner. -/
private abbrev zr_p1L {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zr_rstart (P.i - 1 - 1) - 1) P.s

/-- The descending right pass's round box, its upper corner: the shift's reach, or the anchor
at the home's round. -/
private abbrev zr_p1U {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * zr_hh (zr_p1G P))
    (P.s + 8 * zr_hh (zr_p1G P) + 3)

/-- The layout facts behind the descending right pass's round box. -/
private lemma zr_p1_facts {k : ℕ} {P : zr_Px k} (hV : zr_p1V P) :
    zr_rstart (P.i - 1 - 1) ≤ zr_rstart (P.i - 1) ∧
      zr_rstart P.i = zr_rstart (P.i - 1) + ((2 ^ (P.i - 1) : ℕ) : ℤ) + 1 ∧
      (0 : ℤ) < ((2 ^ (P.i - 1) : ℕ) : ℤ) := by
  have := hV.2
  have hs := zr_rstart_succ (P.i - 1)
  rw [show P.i - 1 + 1 = P.i by omega] at hs
  exact ⟨zr_rstart_mono (by omega), hs, by exact_mod_cast Nat.two_pow_pos _⟩

/-- The descending right pass's lead: skip back over field `P.i - 1`, then push a count mark. -/
private def zr_p1Lead {k : ℕ} (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_p1V zr_pT (fun P => zr_aT (zr_p1G P)) zr_rH
      (fun P => zr_rA (zr_p1G P)) _ zr_p1L zr_p1U from
  zr_segSeq (zr_seg (zr_pinBack_step (x := x) zr_p1V 0 (fun P => zr_rfield P.D.2 (P.i - 1)) zr_pT
        zr_rH fun P hV q h1 h2 => by
          obtain ⟨-, hs, -⟩ := zr_p1_facts hV
          have := hV.1.1
          have hl := zr_rfield_length P.D.2 (P.i - 1) (by omega)
          show zonedTape P.D.2 (zr_rstart P.i - ((zr_rfield P.D.2 (P.i - 1)).length : ℤ) - 1 + q) =
            _
          exact zr_rfield_at P.D.2 (P.i - 1) (by omega) _ (by rw [hl]; omega) q h1 h2)
      (T₂' := zr_pT) (p₂' := fun P => zr_heads (zr_rstart (P.i - 1)) P.s) (L' := zr_p1L)
      (U' := zr_p1U) (fun _ _ => rfl) fun P hV => by
        obtain ⟨hm, hs, -⟩ := zr_p1_facts hV
        have := hV.1.1
        have hl := zr_rfield_length P.D.2 (P.i - 1) (by omega)
        refine ⟨?_, ?_, ?_⟩
        · show Function.update (zr_heads (zr_rstart P.i) P.s) 0
            (zr_rstart P.i - ((zr_rfield P.D.2 (P.i - 1)).length : ℤ) - 1) = _
          rw [zr_heads_set0, hl]
          congr 1
          omega
        · show ∀ i, zr_p1L P i ≤ Function.update (zr_heads (zr_rstart P.i) P.s) 0
            (zr_rstart P.i - ((zr_rfield P.D.2 (P.i - 1)).length : ℤ) - 2) i
          rw [zr_heads_set0, hl]
          exact zr_heads_le (show zr_rstart (P.i - 1 - 1) - 1 ≤
            zr_rstart P.i - ((2 ^ (P.i - 1) : ℕ) : ℤ) - 2 by omega) le_rfl
        · exact zr_heads_le (show zr_rstart P.i ≤
            (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) by
            split_ifs <;> omega) (show P.s ≤ P.s + 8 * (zr_hh (zr_p1G P) : ℤ) + 3 by omega))
    (zr_seg (zr_pinCell_step (x := x) zr_p1V 1 1 (some (some (.inl false))) zr_pT
        fun P => zr_heads (zr_rstart (P.i - 1)) P.s)
      (T₂' := fun P => zr_aT (zr_p1G P)) (p₂' := fun P => zr_rA (zr_p1G P)) (L' := zr_p1L)
      (U' := zr_p1U) (fun P hV => by
        show Function.update (zr_pT P) 1 (Function.update (zr_pT P 1) P.s _) = _
        rw [zr_tapes_write, zr_stk_push _ hV.1.2.1]) fun P hV => by
        obtain ⟨hm, hs, h2⟩ := zr_p1_facts hV
        refine ⟨?_, fun i => ?_, fun i => ?_⟩
        · show Function.update (zr_heads (zr_rstart (P.i - 1)) P.s) 1
            (P.s + ((1 : SignType) : ℤ)) = _
          rw [zr_heads_set1, SignType.coe_one]
        · show zr_p1L P i ≤ min (zr_heads (zr_rstart (P.i - 1)) P.s i)
            (Function.update (zr_heads (zr_rstart (P.i - 1)) P.s) 1 (P.s + ((1 : SignType) : ℤ)) i)
          rw [zr_heads_set1, SignType.coe_one]
          revert i
          exact zr_heads_le (show zr_rstart (P.i - 1 - 1) - 1 ≤ min (zr_rstart (P.i - 1))
            (zr_rstart (P.i - 1)) by omega) (show P.s ≤ min P.s (P.s + 1) by omega)
        · show max (zr_heads (zr_rstart (P.i - 1)) P.s i)
            (Function.update (zr_heads (zr_rstart (P.i - 1)) P.s) 1
              (P.s + ((1 : SignType) : ℤ)) i) ≤ zr_p1U P i
          rw [zr_heads_set1, SignType.coe_one]
          revert i
          exact zr_heads_le (show max (zr_rstart (P.i - 1)) (zr_rstart (P.i - 1)) ≤
            (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) by
            split_ifs <;> omega)
            (show max P.s (P.s + 1) ≤ P.s + 8 * (zr_hh (zr_p1G P) : ℤ) + 3 by omega))

/-- **A home test** one cell past a field's start, the field read through `st` (the right or the
left layout): blank exactly at the home. -/
private lemma zr_home_eq {k : ℕ} {P : zr_Px k} (st : ℕ → ℤ)
    (hst : ∀ n, n ≤ P.D.1 → (zonedTape P.D.2 (st n + 1)).isNone = decide (n = 0)) {n : ℕ}
    (hn : n ≤ P.i) (hV : zr_pxV P) :
    (zonedTape P.D.2 (st n + ((1 : SignType) : ℤ))).isNone = decide (n = 0) := by
  rw [SignType.coe_one]
  exact hst n (hn.trans hV.1)

/-- A descending pass's home test verdict, one cell past the field start `A` reads. -/
private abbrev zr_dnHome {k : ℕ} (A : zr_Ix k → Fin 2 → ℤ) (P : zr_Px k) : Bool :=
  Option.isNone (zr_aT (zr_p1G P) 0 (A (zr_p1G P) 0 + ((1 : SignType) : ℤ)))

/-- The descending right pass's home test verdict, one cell after field `P.i - 1`'s start. -/
private abbrev zr_p1Home {k : ℕ} (P : zr_Px k) : Bool := zr_dnHome zr_rA P

/-- The descending right pass's guard: a descending index away from the home. -/
private abbrev zr_p1On {k : ℕ} (P : zr_Px k) : Prop := zr_p1V P ∧ zr_p1Home P = false

/-- The home test's verdict is whether field `P.i - 1` is the home. -/
private lemma zr_p1Home_eq {k : ℕ} {P : zr_Px k} (hV : zr_pxV P) :
    zr_p1Home P = decide (P.i - 1 = 0) :=
  zr_home_eq zr_rstart (zr_rhome_iff _) (Nat.sub_le _ _) hV

/-- The descending right pass's home test, a peek one cell right, in the round box. -/
private lemma zr_p1Peek_step {k : ℕ} (x : List (ZoneSym k)) :
    zr_PinStep (zr_pinPeekContract x zr_p1V 0 1 Option.isNone (fun P => zr_aT (zr_p1G P))
        fun P => zr_rA (zr_p1G P)) zr_p1V (fun P => zr_aT (zr_p1G P))
      (fun P => zr_aT (zr_p1G P)) (fun P => zr_rA (zr_p1G P)) (fun P => zr_rA (zr_p1G P))
      (fun _ => 3) zr_p1L zr_p1U :=
  zr_PinStep_congr (zr_pinPeek_step _ 0 1 Option.isNone _ _) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun P hV i => by
      have := zr_p1_facts hV
      fin_cases i
      · show zr_rstart (P.i - 1 - 1) - 1 ≤ zr_rstart (P.i - 1) - 1
        omega
      · show P.s ≤ P.s + 1 - 1
        omega)
    (fun P hV i => by
      have := zr_p1_facts hV
      fin_cases i
      · show zr_rstart (P.i - 1) + 1 ≤
          (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ))
        split_ifs <;> omega
      · show P.s + 1 + 1 ≤ P.s + 8 * (zr_hh (zr_p1G P) : ℤ) + 3
        omega)

/-- Past the home, a descending pass's shift index meets the shift's requirements. -/
private lemma zr_dnG_pre {k : ℕ} {P : zr_Px k} {v : Bool} (h : zr_p1V P ∧ v = false)
    (hv : v = decide (P.i - 1 = 0)) : zr_shPre (zr_p1G P) := by
  obtain ⟨hV, h⟩ := h
  rw [hv, decide_eq_false_iff_not] at h
  have := hV.1.1
  refine ⟨show 1 ≤ P.i - 1 by omega, show P.i - 1 < P.D.1 by omega, fun r hr => ?_⟩
  have hr' : P.s + 1 ≤ r := hr
  show zr_stk P.β P.b (P.s + 1) r = none
  rw [zr_stk, if_neg (by omega)]
  exact hV.1.2.2 r (by have := hV.1.2.1; omega)

/-- Past the home, the descending right pass's shift index meets the shift's requirements. -/
private lemma zr_p1G_pre {k : ℕ} {P : zr_Px k} (h : zr_p1V P ∧ zr_p1Home P = false) :
    zr_shPre (zr_p1G P) :=
  zr_dnG_pre h (zr_p1Home_eq h.1.1)

/-- The descending right pass's guarded shift, in the round box. -/
private lemma zr_p1Grd_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_grdIn t x zr_p1G (fun P => zr_p1V P ∧ zr_p1Home P = false)
        fun _ h => zr_p1G_pre h) (fun P => zr_p1V P ∧ zr_p1Home P = false)
      (fun P => zr_aT (zr_p1G P)) (fun P => zr_pT (zr_p1Nxt t P)) (fun P => zr_rA (zr_p1G P))
      (fun P => zr_rH (zr_p1Nxt t P))
      (fun P => 1 + 1 + if zr_inOff t (zr_p1G P) then 0 else 76 * zr_hh (zr_p1G P) + 77)
      zr_p1L zr_p1U :=
  zr_PinStep_congr (zr_grdIn_step t x _ _ _) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun P hV => zr_heads_le le_rfl (show P.s ≤ P.s + 1 by omega)) fun P hV => by
      have h1 := (zr_p1G_pre hV).1
      have h1' : 1 ≤ P.i - 1 := h1
      have hh : P.i - 1 + 1 = P.i := by
        have : 1 ≤ P.i - 1 := h1
        omega
      show ∀ i, zr_heads (zr_rstart (P.i - 1 + 1) + 4 * (zr_hh (zr_p1G P) : ℤ))
        (P.s + 1 + 8 * (zr_hh (zr_p1G P) : ℤ) + 2) i ≤ _
      rw [hh]
      exact zr_heads_le (show zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ) ≤
          (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) by
          rw [if_neg (by omega)]) (show P.s + 1 + 8 * (zr_hh (zr_p1G P) : ℤ) + 2 ≤
        P.s + 8 * (zr_hh (zr_p1G P) : ℤ) + 3 by omega)

/-- **The descending right pass's branch**: at the home stop; otherwise run the guarded
shift. -/
private def zr_p1Br {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_peekBranch (zr_p1Peek_step x) (zr_p1Grd_step t x) fun _ => rfl

/-- The descending right pass's branch is a pinned step to the next index's anchor pin. -/
private lemma zr_p1Br_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p1Br t x) zr_p1V (fun P => zr_aT (zr_p1G P)) (fun P => zr_pT (zr_p1Nxt t P))
      (fun P => zr_rA (zr_p1G P)) (fun P => zr_rH (zr_p1Nxt t P))
      (fun P => 3 + 1 + if zr_p1Home P then 0 else
        1 + 1 + if zr_inOff t (zr_p1G P) then 0 else 76 * zr_hh (zr_p1G P) + 77) zr_p1L zr_p1U :=
  zr_peekBranch_step _ _ _ (fun P hV hh => by
      rw [zr_p1Home_eq hV.1, decide_eq_true_iff] at hh
      refine ⟨?_, rfl⟩
      show zr_tapes (zonedTape (Function.update P.D.2 t (zoneShiftIn true (P.i - 1) (P.D.2 t))))
        _ = _
      rw [hh, zr_shiftIn_zero, Function.update_eq_self]) fun P hV i => by
    have := zr_p1_facts hV
    fin_cases i
    · exact ⟨show zr_rstart (P.i - 1 - 1) - 1 ≤ zr_rstart (P.i - 1) by omega,
        show zr_rstart (P.i - 1) ≤
          (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) by
          split_ifs <;> omega⟩
    · exact ⟨show P.s ≤ P.s + 1 by omega,
        show P.s + 1 ≤ P.s + 8 * (zr_hh (zr_p1G P) : ℤ) + 3 by omega⟩

/-- **The descending right pass's round body**: skip back over a field and push a count mark,
then stop at the home or run the guarded inward shift at that field's level. -/
private def zr_p1Body {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  (zr_p1Lead x).C.seq (zr_p1Br t x) (fun P => P)
    (zr_pin_hlink (zr_p1Lead x).step (zr_p1Br_step t x))

/-- The descending right pass's round time. -/
private abbrev zr_p1Tau {k : ℕ} (t : Fin k) (P : zr_Px k) : ℕ :=
  (zr_rfield P.D.2 (P.i - 1)).length + 3 + 1 + 1 + 1 +
    (3 + 1 + if zr_p1Home P then 0 else
      1 + 1 + if zr_inOff t (zr_p1G P) then 0 else 76 * zr_hh (zr_p1G P) + 77)

/-- **The descending right pass's round** is a pinned step from the anchor to the next index's
anchor. -/
private lemma zr_p1Body_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p1Body t x) zr_p1V zr_pT (fun P => zr_pT (zr_p1Nxt t P)) zr_rH
      (fun P => zr_rH (zr_p1Nxt t P)) (zr_p1Tau t) zr_p1L zr_p1U :=
  zr_PinStep_seq' (zr_p1Lead x).step (zr_p1Br_step t x) _

/-- The descending right pass's way back: the home exit escapes, the guarded shift's exits
return to the anchor. -/
private noncomputable def zr_p1Back {k : ℕ} (t : Fin k) :
    zr_stOf (zr_p1Body t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_seqBack (zr_branchBack (zr_oneBack (some false) true) (zr_grdInBack t))

/-- The descending right pass's round escapes exactly at the home. -/
private lemma zr_p1Body_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_p1Body t x) (zr_p1Back t) zr_p1Home :=
  zr_BackIs_seq (zr_BackIs_congr (zr_peekBranch_back _ _ _ (zr_grdIn_back t x _ _ _) true)
    fun P => by cases zr_p1Home P <;> rfl)

/-- The descending right pass's round's exits are its way back's domain. -/
private lemma zr_p1Body_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_p1Body t x) ↔ zr_p1Back t s ≠ none :=
  zr_seqBack_hX (zr_branchBack_hX (zr_oneBack_hX _ _) (zr_grdIn_hX t x zr_p1G
    (fun P => zr_p1V P ∧ zr_p1Home P = false) fun _ h => zr_p1G_pre h))

/-- The descending right pass's round never halts. -/
private lemma zr_p1Body_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_p1Body t x) :=
  zr_none_dn (zr_grdIn_none t x zr_p1G zr_p1On fun _ => zr_p1G_pre)

/-- A descending pass after `m` rounds: `m` fields further in, `m` marks pushed. -/
private lemma zr_dn_iter {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) (P : zr_Px k) (m : ℕ) :
    ((zr_dnF t F)^[m] P).D.1 = P.D.1 ∧ ((zr_dnF t F)^[m] P).i = P.i - m ∧
      ((zr_dnF t F)^[m] P).β = P.β ∧ ((zr_dnF t F)^[m] P).b = P.b ∧
      ((zr_dnF t F)^[m] P).s = P.s + m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := zr_px_iter t F (fun i => i - 1) 1 P m
  exact ⟨by rw [h1], by rw [h2, zr_iterate_pred], h3, h4, by rw [h5, mul_one]⟩

/-- A descending pass stays valid before its home round. -/
private lemma zr_dn_valid {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) {P : zr_Px k} (hV : zr_p1V P) (m : ℕ)
    (hm : m < P.i) : zr_p1V ((zr_dnF t F)^[m] P) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := zr_dn_iter t F P m
  obtain ⟨⟨hi, hbs, hβ⟩, -⟩ := hV
  refine ⟨⟨by rw [h2, h1]; omega, by rw [h4, h5]; omega, fun r hr => ?_⟩, by rw [h2]; omega⟩
  rw [h3]
  exact hβ r (by rw [h4] at hr; exact hr)

/-- Round `m` of the descending right pass is at the home exactly when it is the last. -/
private lemma zr_p1_home {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_p1V P) (m : ℕ)
    (hm : m < P.i) : zr_p1Home ((zr_p1Nxt t)^[m] P) = decide (P.i - m - 1 = 0) := by
  rw [zr_p1Home_eq (zr_dn_valid t (fun _ i w => zoneShiftIn true (i - 1) w) hV m hm).1,
    (zr_dn_iter t (fun _ i w => zoneShiftIn true (i - 1) w) P m).2.1]

/-- A round that is not at the home leaves a valid index. -/
private lemma zr_p1_next_valid {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_p1V P)
    (hh : zr_p1Home P = false) : zr_p1V (zr_p1Nxt t P) := by
  rw [zr_p1Home_eq hV.1, decide_eq_false_iff_not] at hh
  have := zr_dn_valid t (fun _ i w => zoneShiftIn true (i - 1) w) hV 1 (by omega)
  exact this

/-- The descending right pass's head box: the zoned head from one cell left of the home to past
the start field's shift reach, scratch over the marks and the shifts' work areas. -/
private abbrev zr_p1Lo {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (-1) P.s

/-- The descending right pass's head box, its upper corner: the first round's reach. -/
private abbrev zr_p1Hi {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * zr_hh (zr_p1G P))
    (P.s + P.i + 8 * ((2 ^ P.i : ℕ) : ℤ) + 3)

/-- Each round's box lies in the pass's box. -/
private lemma zr_p1_round_box {k : ℕ} (t : Fin k) {P : zr_Px k} (m : ℕ) (hm : m < P.i) :
    ∀ i, zr_p1Lo P i ≤ zr_p1L ((zr_p1Nxt t)^[m] P) i ∧
      zr_p1U ((zr_p1Nxt t)^[m] P) i ≤ zr_p1Hi P i := by
  obtain ⟨-, h2, -, -, h5⟩ := zr_dn_iter t (fun _ i w => zoneShiftIn true (i - 1) w) P m
  have hr0 : 0 ≤ zr_rstart (((zr_p1Nxt t)^[m] P).i - 1 - 1) := by
    have := zr_rstart_mono (Nat.zero_le (((zr_p1Nxt t)^[m] P).i - 1 - 1))
    rwa [zr_rstart, if_pos rfl] at this
  have hrm : zr_rstart ((zr_p1Nxt t)^[m] P).i ≤ zr_rstart P.i :=
    zr_rstart_mono (by rw [h2]; omega)
  have hh : zr_hh (zr_p1G ((zr_p1Nxt t)^[m] P)) ≤ 2 ^ P.i := by
    show 2 ^ (((zr_p1Nxt t)^[m] P).i - 1 - 1) ≤ 2 ^ P.i
    exact Nat.pow_le_pow_right (by norm_num) (by rw [h2]; omega)
  have hh' : (zr_hh (zr_p1G ((zr_p1Nxt t)^[m] P)) : ℤ) ≤ ((2 ^ P.i : ℕ) : ℤ) := by
    exact_mod_cast hh
  have hmi : (m : ℤ) ≤ P.i := by exact_mod_cast hm.le
  intro i
  fin_cases i
  · have hhm : zr_hh (zr_p1G ((zr_p1Nxt t)^[m] P)) ≤ zr_hh (zr_p1G P) := by
      show 2 ^ (((zr_p1Nxt t)^[m] P).i - 1 - 1) ≤ 2 ^ (P.i - 1 - 1)
      exact Nat.pow_le_pow_right (by norm_num) (by rw [h2]; omega)
    have hhm' : (zr_hh (zr_p1G ((zr_p1Nxt t)^[m] P)) : ℤ) ≤ (zr_hh (zr_p1G P) : ℤ) := by
      exact_mod_cast hhm
    have hr1 : zr_rstart 1 ≤ zr_rstart P.i := zr_rstart_mono (by omega)
    have hqi : ((zr_p1Nxt t)^[m] P).i = P.i - m := h2
    exact ⟨show (-1 : ℤ) ≤ zr_rstart (((zr_p1Nxt t)^[m] P).i - 1 - 1) - 1 by omega,
      show (if ((zr_p1Nxt t)^[m] P).i = 1 then zr_rstart ((zr_p1Nxt t)^[m] P).i else
          zr_rstart ((zr_p1Nxt t)^[m] P).i + 4 * (zr_hh (zr_p1G ((zr_p1Nxt t)^[m] P)) : ℤ)) ≤
        (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) by
        split_ifs with ha hb hb
        · omega
        · rw [ha]
          omega
        · omega
        · omega⟩
  · refine ⟨show P.s ≤ ((zr_p1Nxt t)^[m] P).s by rw [h5]; omega, ?_⟩
    show ((zr_p1Nxt t)^[m] P).s + 8 * (zr_hh (zr_p1G ((zr_p1Nxt t)^[m] P)) : ℤ) + 3 ≤
      P.s + P.i + 8 * ((2 ^ P.i : ℕ) : ℤ) + 3
    rw [h5]
    omega

/-- An anchor lies in its round's box. -/
private lemma zr_p1_anchor_box {k : ℕ} (P : zr_Px k) :
    ∀ i, zr_p1L P i ≤ zr_rH P i ∧ zr_rH P i ≤ zr_p1U P i := by
  have hm := zr_rstart_mono (show P.i - 1 - 1 ≤ P.i by omega)
  intro i
  fin_cases i
  · exact ⟨show zr_rstart (P.i - 1 - 1) - 1 ≤ zr_rstart P.i by omega,
      show zr_rstart P.i ≤
        (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) by
        split_ifs <;> omega⟩
  · exact ⟨le_refl P.s, show P.s ≤ P.s + 8 * (zr_hh (zr_p1G P) : ℤ) + 3 by omega⟩

/-- **The descending right pass**, as a pinned segment on its loop: from the anchor at field `P.i`'s
start, `P.i` rounds shift track `t` inward at levels `P.i - 1, …, 1` (the last round, at the home,
shifts nothing), push `P.i` count marks, and stop at the home. -/
private noncomputable def zr_p1Pass {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_passSeg (zr_p1Back t) (zr_p1Body t x) (zr_p1Body_none t x) (zr_p1Body_hX t x)
    (zr_p1Body_step t x) (zr_p1Body_back t x) (fun _ hV hh => zr_p1_next_valid t hV hh)
    (sa := .inr (.inr (.inl (.inr (some false))))) (sb := .inr (.inl (.inr (some false))))
    (by
      show zr_oneBack (some false) false (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (by
      show zr_oneBack (some false) true (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (fun P => P.i - 1)
    (fun P hV => by
      have := hV.2
      show zr_p1Home ((zr_p1Nxt t)^[P.i - 1] P) = true
      rw [zr_p1_home t hV _ (by omega)]
      exact decide_eq_true (by omega))
    (fun P hV m hm => by
      have hm' : m < P.i - 1 := hm
      rw [zr_p1_home t hV _ (by omega)]
      exact decide_eq_false (by omega))
    zr_p1Lo zr_p1Hi (fun P hV m hm => by
      have := hV.2
      have hm' : m ≤ P.i - 1 := hm
      exact zr_p1_round_box t m (by omega))
    zr_p1_anchor_box

/-- The room probe's facts at a valid index: the fields' lengths and starts, the outer zone's
rest past the room cell, and the ruler's length. -/
private lemma zr_prLen {k : ℕ} (t : Fin k) {J : zr_Ix k} (hV : zr_shPre J) :
    (zr_lfield J.D.2 (J.i + 1)).length = 4 * zr_hh J ∧
      (zr_lfield J.D.2 J.i).length = 2 * zr_hh J ∧
      (zr_lfield J.D.2 (J.i - 1)).length = zr_hh J ∧ 0 < zr_hh J ∧
      zr_lstart J.i = zr_lstart (J.i + 1) + 4 * zr_hh J + 1 ∧
      zr_lstart (J.i - 1) = zr_lstart J.i + 2 * zr_hh J + 1 ∧
      ((zr_lfield J.D.2 (J.i + 1)).drop (zr_hh J - 1)).length = 3 * zr_hh J + 1 ∧
      (zr_col t (zr_lfield J.D.2 (J.i - 1))).length = zr_hh J := by
  obtain ⟨e1, e2, e3, h, s1, s2⟩ := zr_lfields hV.1 hV.2.1
  refine ⟨e1, e2, e3, h, s1, s2, ?_, by rw [zr_col, List.length_map, e3]⟩
  rw [List.length_drop, e1]
  omega

/-- The room probe's head box: the zoned head from two cells left of the outer zone to past the
field one inward, scratch over the ruler. -/
private abbrev zr_prL {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (J.i + 1) - 2) (J.s - 1)

/-- The room probe's head box, its upper corner. -/
private abbrev zr_prU {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + zr_hh J + 3)
/-- **The room probe**: copy the field one inward as a ruler and walk the zoned head onto the
outer zone's room cell. -/
private def zr_prSeg {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ (zr_shPre) (fun J => zr_inT J (zonedTape J.D.2) [])
      (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
      (fun J => zr_heads (zr_lstart J.i) J.s)
      (fun J => zr_heads (zr_lstart (J.i + 1) + zr_hh J - 1) (J.s + zr_hh J + 2)) _ zr_prL
      zr_prU from
  -- step 1: scratch right, past the count
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_inT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart J.i) J.s))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 2: skip the inner zone
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_lfield J.D.2 J.i)
        (fun J => zr_inT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_prLen t hV
          have := zr_prLen t hV
          show (zonedTape J.D.2)
            (zr_lstart J.i + q) = _
          exact zr_lfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _
            (by omega) _ (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 3: copy the field one inward's column as a ruler
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_lfield J.D.2 (J.i - 1))
        (fun J => zr_inT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_prLen t hV
          have := zr_prLen t hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) + q) = _
          exact zr_lfield_at J.D.2 (J.i - 1) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun J hV => by
        have := zr_prLen t hV
        exact zr_scr_copy _ _ _ _ [] _ _ _ _
          (by rw [List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_prL, zr_prU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 4: back over the inner zone
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 J.i)
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart (J.i - 1)) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_prLen t hV
          have := zr_prLen t hV
          show (zonedTape J.D.2)
            (zr_lstart (J.i - 1) - (zr_lfield J.D.2 J.i).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 5: back over the outer zone
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_lfield J.D.2 (J.i + 1))
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_prLen t hV
          have := zr_prLen t hV
          show (zonedTape J.D.2)
            (zr_lstart J.i - (zr_lfield J.D.2 (J.i + 1)).length - 1 + q) = _
          exact zr_lfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _
            (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 6: zoned head left
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart (J.i + 1)) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 7: zoned head left again
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart (J.i + 1) - 1) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 8: walk over the ruler, to the room cell
  (zr_seg (zr_pinWalk_step _ 1 (fun J => zr_col t (zr_lfield J.D.2 (J.i - 1)))
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart (J.i + 1) - 2) (J.s + 1))
        fun J hV q hq => by
          have := zr_prLen t hV
          show zr_scr J.σ (J.s) [zr_col t (zr_lfield J.D.2 (J.i - 1))]
            (J.s + 1 + ↑q) = _
          exact zr_scr_at (hV.2.2 _ (by omega))
            [zr_col t (zr_lfield J.D.2 (J.i - 1))] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) ↑q (by omega) (by exact_mod_cast hq))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_prL, zr_prU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega))

/-- **The probe's return**: skip back to the inner zone, clear the ruler, restore scratch. -/
private def zr_retSeg {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ (zr_shPre)
      (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
      (fun J => zr_inT J (zonedTape J.D.2) [])
      (fun J => zr_heads (zr_lstart (J.i + 1) + zr_hh J - 1) (J.s + zr_hh J + 2))
      (fun J => zr_heads (zr_lstart J.i) J.s) _ zr_prL zr_prU from
  -- step 9: skip the outer zone's rest, to the inner zone
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => (zr_lfield J.D.2 (J.i + 1)).drop (zr_hh J - 1))
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart (J.i + 1) + zr_hh J - 1) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_prLen t hV
          have h1' : q ≤ (((zr_lfield J.D.2 (J.i + 1)).drop (zr_hh J - 1)).length : ℤ) := h1
          show zonedTape J.D.2 (zr_lstart (J.i + 1) + zr_hh J - 1 + q) = _
          rw [show zr_lstart (J.i + 1) + (zr_hh J : ℤ) - 1 + q =
              zr_lstart (J.i + 1) + ((zr_hh J : ℤ) - 1 + q) by ring,
            zr_lfield_at J.D.2 (J.i + 1) (by have := hV.2.1; omega) _ rfl _ (by omega)
              (by omega), FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos (by omega),
            if_pos h0, List.getElem?_drop]
          congr 1
          omega)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 10: back over the ruler
  zr_segSeq (zr_seg (zr_pinBack_step _ 1 (fun J => zr_col t (zr_lfield J.D.2 (J.i - 1)))
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart J.i) (J.s + zr_hh J + 2))
        fun J hV q h0 h1 => by
          have := zr_prLen t hV
          show zr_scr J.σ (J.s) [zr_col t (zr_lfield J.D.2 (J.i - 1))]
            (J.s + zr_hh J + 2 - ((zr_col t (zr_lfield J.D.2 (J.i - 1))).length : ℤ) - 1 + q) = _
          exact zr_scr_at (hV.2.2 _ (by omega))
            [zr_col t (zr_lfield J.D.2 (J.i - 1))] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 11: clear the ruler
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_col t (zr_lfield J.D.2 (J.i - 1)))
        (fun J => zr_inT J (zonedTape J.D.2) [zr_col t (zr_lfield J.D.2 (J.i - 1))])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_prLen t hV
          show zr_scr J.σ (J.s) [zr_col t (zr_lfield J.D.2 (J.i - 1))]
            (J.s + 1 + q) = _
          exact zr_scr_at (hV.2.2 _ (by omega))
            [zr_col t (zr_lfield J.D.2 (J.i - 1))] 0 (by simp) _
            (by rw [fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_prLen t hV
        exact zr_scr_clear _ _ _ [] _ _
          (by rw [zr_heads_one, List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_prL, zr_prU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 12: scratch left, to its start
  (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_inT J (zonedTape J.D.2) [])
        (fun J => zr_heads (zr_lstart J.i) (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        have := zr_prLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_prL, zr_prU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega))

/-- The room probe's tapes at its end: the zoned tape, and the ruler on scratch past the head. -/
private abbrev zr_prT {k : ℕ} (t : Fin k) (J : zr_Ix k) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes (zonedTape J.D.2) (zr_scr J.σ J.s [zr_col t (zr_lfield J.D.2 (J.i - 1))])

/-- The room probe's heads at its end: the zoned head on the outer zone's room cell, scratch
past the ruler. -/
private abbrev zr_prH {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (J.i + 1) + zr_hh J - 1) (J.s + zr_hh J + 2)

/-- A left shift index's heads: the zoned head at left field `J.i`'s outermost cell. -/
private abbrev zr_lA {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ := zr_heads (zr_lstart J.i) J.s

/-- **The room probe**, its time in closed form. -/
private lemma zr_prSeg_spec {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_prSeg t x).C zr_shPre zr_aT (zr_prT t) zr_lA zr_prH
      (fun J => 11 * zr_hh J + 20) zr_prL zr_prU :=
  zr_PinStep_start (zr_PinStep_congr (zr_prSeg t x).step (fun _ _ => rfl) (fun _ _ => rfl)
      (fun J hV => by
        have := zr_prLen t hV
        omega)
      (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl))
    (fun J hV => by rw [zr_inT, zr_scr_nil hV.2.2])

/-- **The probe's return**, its time in closed form. -/
private lemma zr_retSeg_spec {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_retSeg t x).C zr_shPre (zr_prT t) zr_aT zr_prH zr_lA
      (fun J => 6 * zr_hh J + 11) zr_prL zr_prU :=
  zr_PinStep_congr (zr_retSeg t x).step (fun J hV => by rw [zr_inT, zr_scr_nil hV.2.2])
    (fun _ _ => rfl)
    (fun J hV => by
      have := zr_prLen t hV
      omega)
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)

/-- A left field's outermost cell is not blank. -/
private lemma zr_lstart_isSome {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (i : ℕ) (hi : i ≤ ℓ) :
    (zonedTape z (zr_lstart i)).isSome :=
  zr_field_isSome (zr_lfield_at z i hi _ rfl) (zr_lfield_length z i hi)

/-- The left outward shift's first guard verdict at `J`: `true` when the guard is off, the inner
zone's outermost slot empty. -/
private abbrev zr_out1Off {k : ℕ} (t : Fin k) (J : zr_Ix k) : Bool :=
  zr_slotEmpty t (zr_aT J 0 (zr_lA J 0))

/-- The left outward shift's second guard verdict at `J`: `true` when the guard is off, the
outer zone's room cell occupied. -/
private abbrev zr_out2Off {k : ℕ} (t : Fin k) (J : zr_Ix k) : Bool :=
  (fun c => !zr_slotEmpty t c) (zr_prT t J 0 (zr_prH J 0))

/-- The first verdict reads whether the inner zone is full. -/
private lemma zr_out1Off_iff {k : ℕ} {t : Fin k} {J : zr_Ix k} (hJ : zr_shPre J) :
    zr_out1Off t J = false ↔
      ((J.D.2 t).left ⟨J.i - 1, by have := hJ.2.1; omega⟩).length = zoneCapacity (J.i - 1) := by
  have hi := hJ.2.1
  rw [← zr_outFull_iff J.D.2 t J.i hJ.1 hi, ne_eq,
    ← zr_slotEmpty_iff t (zr_lstart_isSome J.D.2 _ (by omega)), Bool.not_eq_true]
  rfl

/-- The second verdict reads whether the outer zone has room. -/
private lemma zr_out2Off_iff {k : ℕ} {t : Fin k} {J : zr_Ix k} (hJ : zr_shPre J) :
    zr_out2Off t J = false ↔
      ((J.D.2 t).left ⟨J.i, hJ.2.1⟩).length + 2 ^ (J.i - 1) ≤ zoneCapacity J.i := by
  have hl := zr_prLen t hJ
  have hr : (zonedTape J.D.2 (zr_lstart (J.i + 1) + (zr_hh J : ℤ) - 1)).map (zoneSlotOf t) =
      some none ↔ _ := zr_outRoom_iff J.D.2 t J.i hJ.1 hJ.2.1
  have hc : (zonedTape J.D.2 (zr_lstart (J.i + 1) + (zr_hh J : ℤ) - 1)).isSome := by
    have h := zr_lfield_at J.D.2 (J.i + 1) (by have := hJ.2.1; omega) _ rfl
      ((zr_hh J : ℤ) - 1) (by omega) (by rw [hl.1]; omega)
    rw [show zr_lstart (J.i + 1) + ((zr_hh J : ℤ) - 1) =
      zr_lstart (J.i + 1) + (zr_hh J : ℤ) - 1 by ring] at h
    rw [h, FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_eq_getElem (by
      rw [hl.1]
      omega)]
    rfl
  rw [← hr, ← zr_slotEmpty_iff t hc]
  show (!zr_slotEmpty t (zonedTape J.D.2 (zr_lstart (J.i + 1) + zr_hh J - 1))) = false ↔ _
  simp only [Bool.not_eq_false']

/-- With both guards on, the left outward shift's index is valid. -/
private lemma zr_outOn_valid {k : ℕ} {t : Fin k} {J : zr_Ix k} (hJ : zr_shPre J)
    (h1 : zr_out1Off t J = false) (h2 : zr_out2Off t J = false) : zr_outV t J := by
  have hi := hJ.2.1
  refine ⟨hJ.1, hi, ?_, ?_, hJ.2.2⟩
  · rw [zr_lword, dif_pos (by omega)]
    exact (zr_out1Off_iff hJ).mp h1
  · rw [zr_lword, dif_pos hi]
    exact (zr_out2Off_iff hJ).mp h2

/-- The guarded left outward shift's head box: the room probe's and the shift's together. -/
private abbrev zr_goL {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (J.i + 1) - 2) (J.s - 1)

/-- The guarded left outward shift's head box, its upper corner. -/
private abbrev zr_goU {k : ℕ} (J : zr_Ix k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (J.i - 1) + zr_hh J + 1) (J.s + 6 * zr_hh J + 3)

/-- A left shift index's anchor lies in the guarded shift's box. -/
private lemma zr_go_anchor {k : ℕ} {J : zr_Ix k} (hJ : zr_shPre J) :
    ∀ i, zr_goL J i ≤ zr_lA J i ∧ zr_lA J i ≤ zr_goU J i := by
  obtain ⟨-, -, -, h, s1, s2⟩ := zr_lfields hJ.1 hJ.2.1
  intro i
  fin_cases i
  · exact ⟨show zr_lstart (J.i + 1) - 2 ≤ zr_lstart J.i by omega,
      show zr_lstart J.i ≤ zr_lstart (J.i - 1) + zr_hh J + 1 by omega⟩
  · exact ⟨show J.s - 1 ≤ J.s by omega, show J.s ≤ J.s + 6 * zr_hh J + 3 by omega⟩

/-- The left outward shift's first guard test, stationary at the inner zone's outermost cell,
in the guarded shift's box. -/
private lemma zr_out1Test_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_pinTestContract x V 0 (zr_slotEmpty t) 0 (fun j => zr_aT (g j))
        fun j => zr_lA (g j)) V (fun j => zr_aT (g j)) (fun j => zr_aT (g j))
      (fun j => zr_lA (g j)) (fun j => zr_lA (g j)) (fun _ => 1) (fun j => zr_goL (g j))
      (fun j => zr_goU (g j)) :=
  zr_PinStep_congr (zr_pinTest_step _ 0 _ 0 _ _) (fun _ _ => rfl)
    (fun _ _ => by rw [SignType.coe_zero, add_zero, Function.update_eq_self]) (fun _ _ => rfl)
    (fun j hj i => by
      rw [SignType.coe_zero, add_zero, Function.update_eq_self, min_self]
      exact (zr_go_anchor (hV j hj) i).1)
    (fun j hj i => by
      rw [SignType.coe_zero, add_zero, Function.update_eq_self, max_self]
      exact (zr_go_anchor (hV j hj) i).2)

/-- The left outward shift's second guard test, stationary on the room cell, in the guarded
shift's box. -/
private lemma zr_out2Test_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_pinTestContract x V 0 (fun c => !zr_slotEmpty t c) 0 (fun j => zr_prT t (g j))
        fun j => zr_prH (g j)) V (fun j => zr_prT t (g j)) (fun j => zr_prT t (g j))
      (fun j => zr_prH (g j)) (fun j => zr_prH (g j)) (fun _ => 1) (fun j => zr_goL (g j))
      (fun j => zr_goU (g j)) := by
  have hb : ∀ j, V j → ∀ i, zr_goL (g j) i ≤ zr_prH (g j) i ∧ zr_prH (g j) i ≤ zr_goU (g j) i := by
    intro j hj i
    obtain ⟨-, -, -, h, s1, s2⟩ := zr_lfields (hV j hj).1 (hV j hj).2.1
    fin_cases i
    · exact ⟨show zr_lstart ((g j).i + 1) - 2 ≤ zr_lstart ((g j).i + 1) + zr_hh (g j) - 1 by
          omega, show zr_lstart ((g j).i + 1) + zr_hh (g j) - 1 ≤
          zr_lstart ((g j).i - 1) + zr_hh (g j) + 1 by omega⟩
    · exact ⟨show (g j).s - 1 ≤ (g j).s + zr_hh (g j) + 2 by omega,
        show (g j).s + zr_hh (g j) + 2 ≤ (g j).s + 6 * zr_hh (g j) + 3 by omega⟩
  exact zr_PinStep_congr (zr_pinTest_step _ 0 _ 0 _ _) (fun _ _ => rfl)
    (fun _ _ => by rw [SignType.coe_zero, add_zero, Function.update_eq_self]) (fun _ _ => rfl)
    (fun j hj i => by
      rw [SignType.coe_zero, add_zero, Function.update_eq_self, min_self]
      exact (hb j hj i).1)
    (fun j hj i => by
      rw [SignType.coe_zero, add_zero, Function.update_eq_self, max_self]
      exact (hb j hj i).2)

/-- The guard off leaves the zoned tape unchanged. -/
private lemma zr_outOff_esc {k : ℕ} {t : Fin k} {J : zr_Ix k} (hJ : zr_shPre J)
    (hoff : zr_out1Off t J = true ∨ zr_out2Off t J = true) :
    zr_tapes (zr_outZ t J) J.σ = zr_aT J := by
  have hi := hJ.2.1
  rw [zr_outZ_off t J hJ.1 hi fun ⟨hf, hr⟩ => ?_]
  rcases hoff with h | h
  · rw [(zr_out1Off_iff hJ).mpr hf] at h
    exact Bool.false_ne_true h
  · rw [(zr_out2Off_iff hJ).mpr hr] at h
    exact Bool.false_ne_true h

/-- A room-probe half, re-indexed through `g`, in the guarded outward shift's box. -/
private lemma zr_go_widen {k : ℕ} {S J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e : S} {X : Set (Option S)} {C : Contract M e X J x}
    {V : J → Prop} {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ}
    {τ : J → ℕ} (g : J → zr_Ix k)
    (h : zr_PinStep C V T₁ T₂ p₁ p₂ τ (fun j => zr_prL (g j)) fun j => zr_prU (g j)) :
    zr_PinStep C V T₁ T₂ p₁ p₂ τ (fun j => zr_goL (g j)) fun j => zr_goU (g j) :=
  zr_PinStep_congr h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => zr_heads_le le_rfl le_rfl)
    (fun j _ => zr_heads_le le_rfl (show (g j).s + zr_hh (g j) + 3 ≤
      (g j).s + 6 * zr_hh (g j) + 3 by omega))

/-- The room probe, re-indexed, in the guarded shift's box. -/
private lemma zr_goProbe_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_reindexContract (zr_prSeg t x).C g
        (fun j d => (V j ∧ zr_out1Off t (g j) = false) ∧ zr_pinned (zr_aT (g j)) (zr_lA (g j)) d)
        fun j d hd => ((zr_prSeg_spec t x).2 (g j) d (hV j hd.1.1) hd.2).1)
      (fun j => V j ∧ zr_out1Off t (g j) = false) (fun j => zr_aT (g j))
      (fun j => zr_prT t (g j)) (fun j => zr_lA (g j)) (fun j => zr_prH (g j))
      (fun j => 11 * zr_hh (g j) + 20) (fun j => zr_goL (g j)) (fun j => zr_goU (g j)) :=
  zr_go_widen g (zr_PinStep_re (zr_prSeg_spec t x) g _ fun j h => hV j h.1)

/-- The room probe's return, re-indexed at the indices `V'` selects. -/
private abbrev zr_goRet {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k)) (g : I → zr_Ix k)
    (V' : I → Prop) (hV : ∀ j, V' j → zr_shPre (g j)) :=
  zr_reindexContract (zr_retSeg t x).C g
    (fun j d => V' j ∧ zr_pinned (zr_prT t (g j)) (zr_prH (g j)) d)
    fun j d hd => ((zr_retSeg_spec t x).2 (g j) d (hV j hd.1) hd.2).1

/-- The probe's return, re-indexed, in the guarded shift's box. -/
private lemma zr_goRet_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V' : I → Prop) (hV : ∀ j, V' j → zr_shPre (g j)) :
    zr_PinStep (zr_goRet t x g V' hV) V' (fun j => zr_prT t (g j)) (fun j => zr_aT (g j))
      (fun j => zr_prH (g j)) (fun j => zr_lA (g j)) (fun j => 6 * zr_hh (g j) + 11)
      (fun j => zr_goL (g j)) (fun j => zr_goU (g j)) :=
  zr_go_widen g (zr_PinStep_re (zr_retSeg_spec t x) g V' hV)

/-- The left outward shift, re-indexed at the indices whose guards are on. -/
private abbrev zr_goShift {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :=
  zr_reindexContract (zr_outSeg t x).C g
    (fun j d => ((V j ∧ zr_out1Off t (g j) = false) ∧ zr_out2Off t (g j) = false) ∧
      zr_pinned (zr_aT (g j)) (zr_lA (g j)) d)
    fun j d hd => ((zr_outSeg_spec t x).2 (g j) d
      (zr_outOn_valid (hV j hd.1.1.1) hd.1.1.2 hd.1.2) hd.2).1

/-- The left outward shift, re-indexed, in the guarded shift's box. -/
private lemma zr_goShift_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_goShift t x g V hV)
      (fun j => (V j ∧ zr_out1Off t (g j) = false) ∧ zr_out2Off t (g j) = false)
      (fun j => zr_aT (g j)) (fun j => zr_tapes (zr_outZ t (g j)) (g j).σ)
      (fun j => zr_lA (g j)) (fun j => zr_lA (g j)) (fun j => 76 * zr_hh (g j) + 107)
      (fun j => zr_goL (g j)) (fun j => zr_goU (g j)) :=
  zr_PinStep_congr (zr_PinStep_re (zr_outSeg_spec t x) g _ fun j h =>
      zr_outOn_valid (hV j h.1.1) h.1.2 h.2) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun j _ => zr_heads_le (show zr_lstart ((g j).i + 1) - 2 ≤ zr_lstart ((g j).i + 1) - 1 by
      omega) (show (g j).s - 1 ≤ (g j).s by omega)) (fun _ _ => zr_heads_le le_rfl le_rfl)

/-- With room, return and shift. -/
private abbrev zr_goOn {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k)) (g : I → zr_Ix k)
    (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :=
  (zr_goRet t x g (fun j => (V j ∧ zr_out1Off t (g j) = false) ∧ zr_out2Off t (g j) = false)
      fun j h => hV j h.1.1).seq (zr_goShift t x g V hV) (fun j => j)
    (zr_pin_hlink (zr_goRet_step t x g _ _) (zr_goShift_step t x g V hV))

/-- The room branch: without room only return, with room return and shift. -/
private def zr_goRoom {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k)) (g : I → zr_Ix k)
    (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :=
  Contract.branch (by decide : (some true : Option Bool) ≠ some false)
    (zr_pinTestContract x (fun j => V j ∧ zr_out1Off t (g j) = false) 0
      (fun c => !zr_slotEmpty t c) 0 (fun j => zr_prT t (g j)) fun j => zr_prH (g j))
    (zr_goRet t x g (fun j => (V j ∧ zr_out1Off t (g j) = false) ∧ zr_out2Off t (g j) = true)
      fun j h => hV j h.1.1)
    (zr_goOn t x g V hV) (fun j => j) (fun j => j)
    (zr_pin_blink true (by decide : (some true : Option Bool) ≠ some false)
      (zr_out2Test_step t x g _ fun j h => hV j h.1)
      (fun j d _ hd => by
        rw [zr_pinTest_state _ _ _ _ _ _ j d hd]
        exact zr_verdict_ite some _) rfl (zr_goRet_step t x g _ _))
    (zr_pin_blink false (by decide : (some true : Option Bool) ≠ some false)
      (zr_out2Test_step t x g _ fun j h => hV j h.1)
      (fun j d _ hd => by
        rw [zr_pinTest_state _ _ _ _ _ _ j d hd]
        exact zr_verdict_ite some _) rfl
      (zr_PinStep_seq' (zr_goRet_step t x g _ _) (zr_goShift_step t x g V hV) _))

/-- The room branch ends at the shifted tape either way. -/
private lemma zr_goRoom_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_goRoom t x g V hV) (fun j => V j ∧ zr_out1Off t (g j) = false)
      (fun j => zr_prT t (g j)) (fun j => zr_tapes (zr_outZ t (g j)) (g j).σ)
      (fun j => zr_prH (g j)) (fun j => zr_lA (g j))
      (fun j => 1 + 1 + if zr_out2Off t (g j) then 6 * zr_hh (g j) + 11 else
        6 * zr_hh (g j) + 11 + 1 + (76 * zr_hh (g j) + 107))
      (fun j => zr_goL (g j)) (fun j => zr_goU (g j)) :=
  zr_PinStep_branch (by decide : (some true : Option Bool) ≠ some false)
    (zr_out2Test_step t x g _ fun j h => hV j h.1)
    (fun j d _ hd => by
      rw [zr_pinTest_state _ _ _ _ _ _ j d hd]
      exact zr_verdict_ite some _)
    (zr_PinStep_congr (zr_goRet_step t x g _ _)
      (fun j h => (zr_outOff_esc (hV j h.1.1) (Or.inr h.2)).symm) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl))
    (zr_PinStep_seq' (zr_goRet_step t x g _ _) (zr_goShift_step t x g V hV) _) _ _

set_option synthInstance.maxSize 1024 in
/-- The inner zone full: probe the room, then branch on it. -/
private abbrev zr_goFull {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :=
  (zr_reindexContract (zr_prSeg t x).C g
      (fun j d => (V j ∧ zr_out1Off t (g j) = false) ∧ zr_pinned (zr_aT (g j)) (zr_lA (g j)) d)
      fun j d hd => ((zr_prSeg_spec t x).2 (g j) d (hV j hd.1.1) hd.2).1).seq
    (zr_goRoom t x g V hV) (fun j => j)
    (zr_pin_hlink (zr_goProbe_step t x g V hV) (zr_goRoom_step t x g V hV))

set_option synthInstance.maxSize 1024 in
/-- **The guarded left outward shift** over the shift index `g j`: inner zone not full, stop at
the anchor; full, probe the outer zone's room, return, and shift if there is room. -/
private def zr_grdOut {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k)) (g : I → zr_Ix k)
    (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :=
  zr_anchBranch (by decide : (some true : Option Bool) ≠ some false) (zr_out1Test_step t x g V hV)
    (fun j d _ hd => by
      rw [zr_pinTest_state _ _ _ _ _ _ j d hd]
      exact zr_verdict_ite some _)
    (zr_PinStep_seq' (zr_goProbe_step t x g V hV) (zr_goRoom_step t x g V hV)
      (zr_pin_hlink (zr_goProbe_step t x g V hV) (zr_goRoom_step t x g V hV)))

/-- The guarded left outward shift ends at the shifted tape whichever guard fails. -/
private lemma zr_grdOut_step {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_PinStep (zr_grdOut t x g V hV) V (fun j => zr_aT (g j))
      (fun j => zr_tapes (zr_outZ t (g j)) (g j).σ) (fun j => zr_lA (g j)) (fun j => zr_lA (g j))
      (fun j => 1 + 1 + if zr_out1Off t (g j) then 0 else
        11 * zr_hh (g j) + 20 + 1 + (1 + 1 + if zr_out2Off t (g j) then 6 * zr_hh (g j) + 11 else
          6 * zr_hh (g j) + 11 + 1 + (76 * zr_hh (g j) + 107)))
      (fun j => zr_goL (g j)) (fun j => zr_goU (g j)) :=
  zr_anchBranch_step _ _ _ _ (fun j hj h => ⟨zr_outOff_esc (hV j hj) (Or.inl h), rfl⟩)
    fun j hj => zr_go_anchor (hV j hj)

/-- The room branch returns to the anchor. -/
private lemma zr_goRoom_back {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_BackIs (zr_goRoom t x g V hV)
      (zr_branchBack (zr_oneBack (zr_exitOf (zr_retSeg t ([] : List (ZoneSym k))).C) false)
        (zr_seqBack (zr_oneBack (zr_exitOf (zr_outSeg t ([] : List (ZoneSym k))).C) false)))
      fun _ => false :=
  zr_BackIs_congr (zr_BackIs_branch (by decide : (some true : Option Bool) ≠ some false)
    (zr_out2Test_step t x g _ fun j h => hV j h.1)
    (fun j d _ hd => by
      rw [zr_pinTest_state _ _ _ _ _ _ j d hd]
      exact zr_verdict_ite some _) (zr_BackIs_one _ false) (zr_BackIs_seq (zr_BackIs_one _ false)))
    fun _ => ite_self _

/-- The guarded left outward shift's way back, every exit to the anchor. -/
private noncomputable def zr_grdOutBack {k : ℕ} (t : Fin k) :
    (Option Bool ⊕ Option Bool) ⊕ (zr_stOf (zr_prSeg t ([] : List (ZoneSym k))).C ⊕
      ((Option Bool ⊕ zr_stOf (zr_retSeg t ([] : List (ZoneSym k))).C) ⊕
        (zr_stOf (zr_retSeg t ([] : List (ZoneSym k))).C ⊕
          zr_stOf (zr_outSeg t ([] : List (ZoneSym k))).C))) → Option (Option Bool) :=
  zr_branchBack (zr_oneBack (some false) false)
    (zr_seqBack (zr_branchBack (zr_oneBack (zr_exitOf (zr_retSeg t ([] : List (ZoneSym k))).C)
      false) (zr_seqBack (zr_oneBack (zr_exitOf (zr_outSeg t ([] : List (ZoneSym k))).C) false))))

set_option synthInstance.maxSize 1024 in
/-- The guarded left outward shift returns to the anchor. -/
private lemma zr_grdOut_back {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    zr_BackIs (zr_grdOut t x g V hV) (zr_grdOutBack t) fun _ => false :=
  zr_BackIs_congr (zr_anchBranch_back _ _ _ _ (zr_BackIs_seq (zr_goRoom_back t x g V hV)) false)
    fun j => by cases zr_out1Off t (g j) <;> rfl

/-- The guarded left outward shift's exits are its way back's domain. -/
private lemma zr_grdOut_hX {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    ∀ s, some s ∈ zr_exitsOf (zr_grdOut t x g V hV) ↔ zr_grdOutBack t s ≠ none :=
  zr_branchBack_hX (zr_oneBack_hX _ _) (zr_seqBack_hX (zr_branchBack_hX (zr_oneBack_hX _ _)
    (zr_seqBack_hX (zr_oneBack_hX _ _))))

/-- The guarded left outward shift never halts. -/
private lemma zr_grdOut_none {k : ℕ} {I : Type} (t : Fin k) (x : List (ZoneSym k))
    (g : I → zr_Ix k) (V : I → Prop) (hV : ∀ j, V j → zr_shPre (g j)) :
    none ∉ zr_exitsOf (zr_grdOut t x g V hV) :=
  zr_none_up (zr_none_arm (zr_none_not_mem_image _ (zr_none_not_mem_single _)))

/-- The left layout's field starts decrease outward. -/
private lemma zr_lstart_anti {m n : ℕ} (h : m ≤ n) : zr_lstart n ≤ zr_lstart m :=
  antitone_nat_of_succ_le (fun n => by
    have := zr_lstart_succ n
    have := Nat.two_pow_pos (n + 1)
    omega) h

/-- The count stack's pop test verdict, the cell below the top: `true` when the stack is
empty. -/
private abbrev zr_popE {k : ℕ} (P : zr_Px k) : Bool :=
  Option.isNone (zr_pσ P (P.s + ((-1 : SignType) : ℤ)))

/-- Over a base blank just below the stack, the pop test reads emptiness. -/
private lemma zr_popE_eq {k : ℕ} {P : zr_Px k} (hV : zr_pxV P) (hβ : P.β (P.b - 1) = none) :
    zr_popE P = decide (P.s = P.b) := by
  have := hV.2.1
  show (zr_stk P.β P.b P.s (P.s + ((-1 : SignType) : ℤ))).isNone = _
  rw [SignType.coe_neg_one, ← sub_eq_add_neg, zr_stk_top]
  by_cases h : P.b < P.s
  · rw [if_pos h, decide_eq_false (by omega)]
    rfl
  · rw [if_neg h, show P.s = P.b by omega, hβ, decide_eq_true rfl]
    rfl

/-- The stack after a pop. -/
private abbrev zr_popT {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes (zonedTape P.D.2) (zr_stk P.β P.b (P.s - 1))

/-- **A pop**: step scratch down and blank the top mark, the zoned head at `a P`. -/
private def zr_popSeg {k : ℕ} (x : List (ZoneSym k)) (V : zr_Px k → Prop) (a : zr_Px k → ℤ)
    (hV : ∀ P, V P → zr_pxV P ∧ P.b < P.s) :=
  show zr_PinSeg x _ _ _ V zr_pT zr_popT (fun P => zr_heads (a P) P.s)
      (fun P => zr_heads (a P) (P.s - 1)) _ (fun P => zr_heads (a P) (P.s - 1))
      (fun P => zr_heads (a P) P.s) from
  zr_segSeq (zr_seg (zr_pinCell_step (x := x) V 1 (-1) none zr_pT fun P => zr_heads (a P) P.s)
      (T₂' := zr_pT) (p₂' := fun P => zr_heads (a P) (P.s - 1))
      (L' := fun P => zr_heads (a P) (P.s - 1)) (U' := fun P => zr_heads (a P) P.s)
      (fun _ _ => rfl) fun P _ => by
        have hp : Function.update (zr_heads (a P) P.s) 1 (P.s + ((-1 : SignType) : ℤ)) =
            zr_heads (a P) (P.s - 1) := by
          rw [zr_heads_set1, SignType.coe_neg_one, ← sub_eq_add_neg]
        refine ⟨hp, fun i => ?_, fun i => ?_⟩
        · show zr_heads (a P) (P.s - 1) i ≤ min (zr_heads (a P) P.s i)
            (Function.update (zr_heads (a P) P.s) 1 (P.s + ((-1 : SignType) : ℤ)) i)
          rw [hp]
          fin_cases i
          · show a P ≤ min (a P) (a P)
            omega
          · show P.s - 1 ≤ min P.s (P.s - 1)
            omega
        · show max (zr_heads (a P) P.s i)
            (Function.update (zr_heads (a P) P.s) 1 (P.s + ((-1 : SignType) : ℤ)) i) ≤
              zr_heads (a P) P.s i
          rw [hp]
          fin_cases i
          · show max (a P) (a P) ≤ a P
            omega
          · show max P.s (P.s - 1) ≤ P.s
            omega)
    (zr_seg (zr_pinCell_step (x := x) V 1 0 (some none) zr_pT fun P => zr_heads (a P) (P.s - 1))
      (T₂' := zr_popT) (p₂' := fun P => zr_heads (a P) (P.s - 1))
      (L' := fun P => zr_heads (a P) (P.s - 1)) (U' := fun P => zr_heads (a P) P.s)
      (fun P hP => by
        obtain ⟨⟨-, -, hβ⟩, hs⟩ := hV P hP
        show Function.update (zr_pT P) 1 (Function.update (zr_pT P 1) (P.s - 1) none) = _
        rw [zr_tapes_write, zr_stk_pop (hβ _ (by omega))]) fun P _ => by
        have hp : Function.update (zr_heads (a P) (P.s - 1)) 1
            (P.s - 1 + ((0 : SignType) : ℤ)) = zr_heads (a P) (P.s - 1) := by
          rw [zr_heads_set1, SignType.coe_zero, add_zero]
        refine ⟨hp, fun i => ?_, fun i => ?_⟩
        · show zr_heads (a P) (P.s - 1) i ≤ min (zr_heads (a P) (P.s - 1) i)
            (Function.update (zr_heads (a P) (P.s - 1)) 1 (P.s - 1 + ((0 : SignType) : ℤ)) i)
          rw [hp, min_self]
        · show max (zr_heads (a P) (P.s - 1) i)
            (Function.update (zr_heads (a P) (P.s - 1)) 1 (P.s - 1 + ((0 : SignType) : ℤ)) i) ≤
              zr_heads (a P) P.s i
          rw [hp, max_self]
          fin_cases i
          · exact le_refl (a P)
          · show P.s - 1 ≤ P.s
            omega)

/-- **A conditional pass's next index**: unchanged where the pass stops. -/
private abbrev zr_cNxt {k : ℕ} (c : zr_Px k → Prop) [DecidablePred c] (f : zr_Px k → zr_Px k)
    (P : zr_Px k) : zr_Px k :=
  if c P then P else f P

/-- Before a conditional pass stops, its rounds are its unconditional rounds. -/
private lemma zr_cNxt_iter {k : ℕ} (c : zr_Px k → Prop) [DecidablePred c]
    (f : zr_Px k → zr_Px k) (P : zr_Px k) (m : ℕ) (h : ∀ r < m, ¬ c (f^[r] P)) :
    (zr_cNxt c f)^[m] P = f^[m] P := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun r hr => h r (by omega)]
    exact if_neg (h m (by omega))

/-- The left outward lead's box, its lower corner. -/
private abbrev zr_ldL {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (P.i + 1) - 1) (P.s - 1)

/-- The left outward lead's box, its upper corner. -/
private abbrev zr_ldU {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i) P.s

/-- **The left outward lead**: pop a count mark, then skip back over left field `P.i + 1` to its
outermost cell. -/
private def zr_ldLead {k : ℕ} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (hV : ∀ P, V P → (zr_pxV P ∧ P.b < P.s) ∧ P.i < P.D.1) :=
  show zr_PinSeg x _ _ _ V zr_pT zr_popT (fun P => zr_heads (zr_lstart P.i) P.s)
      (fun P => zr_heads (zr_lstart (P.i + 1)) (P.s - 1)) _ zr_ldL zr_ldU from
  zr_segSeq (zr_seg (zr_popSeg x V (fun P => zr_lstart P.i) fun P h => (hV P h).1).step
      (fun _ _ => rfl) fun P _ => by
        have := zr_lstart_anti (show P.i ≤ P.i + 1 by omega)
        exact ⟨rfl, zr_heads_le (show zr_lstart (P.i + 1) - 1 ≤ zr_lstart P.i by omega) le_rfl,
          zr_heads_le le_rfl le_rfl⟩)
    (zr_seg (zr_pinBack_step (x := x) V 0 (fun P => zr_lfield P.D.2 (P.i + 1)) zr_popT
        (fun P => zr_heads (zr_lstart P.i) (P.s - 1)) fun P hP q h1 h2 => by
          have hi := (hV P hP).2
          have hl := zr_lfield_length P.D.2 (P.i + 1) (by omega)
          have hs := zr_lstart_succ P.i
          show zonedTape P.D.2 (zr_lstart P.i - ((zr_lfield P.D.2 (P.i + 1)).length : ℤ) - 1 + q) =
            _
          exact zr_lfield_at P.D.2 (P.i + 1) (by omega) _ (by rw [hl]; omega) q h1 h2)
      (fun _ _ => rfl) fun P hP => by
        have hi := (hV P hP).2
        have hl := zr_lfield_length P.D.2 (P.i + 1) (by omega)
        have hs := zr_lstart_succ P.i
        refine ⟨?_, ?_, ?_⟩
        · show Function.update (zr_heads (zr_lstart P.i) (P.s - 1)) 0
            (zr_lstart P.i - ((zr_lfield P.D.2 (P.i + 1)).length : ℤ) - 1) = _
          rw [zr_heads_set0, hl]
          congr 1
          omega
        · show ∀ i, zr_ldL P i ≤ Function.update (zr_heads (zr_lstart P.i) (P.s - 1)) 0
            (zr_lstart P.i - ((zr_lfield P.D.2 (P.i + 1)).length : ℤ) - 2) i
          rw [zr_heads_set0, hl]
          exact zr_heads_le (show zr_lstart (P.i + 1) - 1 ≤
            zr_lstart P.i - ((2 ^ (P.i + 1) : ℕ) : ℤ) - 2 by omega) le_rfl
        · exact zr_heads_le le_rfl (show P.s - 1 ≤ P.s by omega))

/-- A left pass's anchor heads: the zoned head at left field `P.i`'s outermost cell. -/
private abbrev zr_lH {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i) P.s

/-- A pop pass's validity: a pass index over a base blank just below the stack, with `c` more
left fields than its marks need. -/
private def zr_popV {k : ℕ} (c : ℤ) (P : zr_Px k) : Prop :=
  zr_pxV P ∧ P.β (P.b - 1) = none ∧ (P.i : ℤ) + (P.s - P.b) + c ≤ P.D.1

/-- The walk out's validity: enough left fields for its marks. -/
private abbrev zr_woV {k : ℕ} (P : zr_Px k) : Prop := zr_popV 0 P

/-- **The walk out's next index**: one left field out and one mark popped, unless the stack is
empty. -/
private abbrev zr_woNxt {k : ℕ} (t : Fin k) : zr_Px k → zr_Px k :=
  zr_cNxt (fun P => P.s ≤ P.b) (zr_pxNxt t (fun _ _ w => w) (fun i => i + 1) (-1))

/-- The walk out's run with marks left: the lead, then the skip across left field `P.i + 1`. -/
private abbrev zr_woRun {k : ℕ} (P : zr_Px k) : ℕ :=
  1 + 1 + 1 + 1 + ((zr_lfield P.D.2 (P.i + 1)).length + 3)

/-- The walk out's round box, its lower corner: the lead's reach unless the stack is empty. -/
private abbrev zr_woL {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 1) - 1) (P.s - 2)

/-- The walk out's round box, its upper corner. -/
private abbrev zr_woU {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i + 1) (P.s + 1)

/-- With marks left, the walk out's index meets the lead's requirements. -/
private lemma zr_wo_lead {k : ℕ} {P : zr_Px k} (h : zr_woV P ∧ zr_popE P = false) :
    (zr_pxV P ∧ P.b < P.s) ∧ P.i < P.D.1 := by
  obtain ⟨⟨hV, hβ, hl⟩, hp⟩ := h
  rw [zr_popE_eq hV hβ, decide_eq_false_iff_not] at hp
  have := hV.2.1
  exact ⟨⟨hV, by omega⟩, by omega⟩

/-- **A peek round**: peek at tape `j`, `δ` from its head (the zoned head at `a P`); on verdict
`v P` stop at the anchor, otherwise run the arm. -/
private def zr_peekRound {k : ℕ} {S₂ : Type} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (j : Fin 2) (δ : SignType) (v : zr_Px k → Bool) (a : zr_Px k → ℤ)
    (hv : ∀ P, v P = Option.isNone (zr_pT P j (zr_heads (a P) P.s j + δ)))
    (L U : zr_Px k → Fin 2 → ℤ)
    (hL : ∀ P, V P → ∀ i, L P i ≤ zr_heads (a P) P.s i - 1)
    (hU : ∀ P, V P → ∀ i, zr_heads (a P) P.s i + 1 ≤ U P i)
    {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ (zr_Px k) x} {T₂ : zr_Px k → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₂ : zr_Px k → Fin 2 → ℤ} {τ₂ : zr_Px k → ℕ}
    (h₂ : zr_PinStep C₂ (fun P => V P ∧ v P = false) zr_pT T₂ (fun P => zr_heads (a P) P.s) p₂ τ₂
      L U) :=
  zr_anchBranch (by decide : (Sum.inr (some true) : Option Bool ⊕ Option Bool) ≠
      Sum.inr (some false))
    (zr_PinStep_congr (zr_pinPeek_step (x := x) V j δ Option.isNone zr_pT
      fun P => zr_heads (a P) P.s) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (T₂' := zr_pT) (p₂' := fun P => zr_heads (a P) P.s) (τ' := fun _ => 3) hL hU)
    (fun P d hV hd => by
      rw [zr_pinPeek_state _ _ _ _ _ _ P hV d hd, ← hv]
      exact zr_verdict_ite (fun b => Sum.inr (some b)) _) h₂

/-- A peek round is a pinned step to the arm's endpoint pin, which the anchor meets on the
verdict. -/
private lemma zr_peekRound_step {k : ℕ} {S₂ : Type} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (j : Fin 2) (δ : SignType) (v : zr_Px k → Bool) (a : zr_Px k → ℤ)
    (hv : ∀ P, v P = Option.isNone (zr_pT P j (zr_heads (a P) P.s j + δ)))
    (L U : zr_Px k → Fin 2 → ℤ)
    (hL : ∀ P, V P → ∀ i, L P i ≤ zr_heads (a P) P.s i - 1)
    (hU : ∀ P, V P → ∀ i, zr_heads (a P) P.s i + 1 ≤ U P i)
    {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ (zr_Px k) x} {T₂ : zr_Px k → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₂ : zr_Px k → Fin 2 → ℤ} {τ₂ : zr_Px k → ℕ}
    (h₂ : zr_PinStep C₂ (fun P => V P ∧ v P = false) zr_pT T₂ (fun P => zr_heads (a P) P.s) p₂ τ₂
      L U)
    (hesc : ∀ P, V P → v P = true → T₂ P = zr_pT P ∧ p₂ P = zr_heads (a P) P.s) :
    zr_PinStep (zr_peekRound x V j δ v a hv L U hL hU h₂) V zr_pT T₂ (fun P => zr_heads (a P) P.s)
      p₂ (fun P => 3 + 1 + if v P then 0 else τ₂ P) L U :=
  zr_anchBranch_step _ _ _ _ hesc fun P hV i =>
    ⟨(hL P hV i).trans (by omega), (by omega : _ ≤ zr_heads (a P) P.s i + 1).trans (hU P hV i)⟩

/-- A peek round escapes exactly on the verdict. -/
private lemma zr_peekRound_back {k : ℕ} {S₂ : Type} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (j : Fin 2) (δ : SignType) (v : zr_Px k → Bool) (a : zr_Px k → ℤ)
    (hv : ∀ P, v P = Option.isNone (zr_pT P j (zr_heads (a P) P.s j + δ)))
    (L U : zr_Px k → Fin 2 → ℤ)
    (hL : ∀ P, V P → ∀ i, L P i ≤ zr_heads (a P) P.s i - 1)
    (hU : ∀ P, V P → ∀ i, zr_heads (a P) P.s i + 1 ≤ U P i)
    {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ (zr_Px k) x} {T₂ : zr_Px k → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₂ : zr_Px k → Fin 2 → ℤ} {τ₂ : zr_Px k → ℕ}
    (h₂ : zr_PinStep C₂ (fun P => V P ∧ v P = false) zr_pT T₂ (fun P => zr_heads (a P) P.s) p₂ τ₂
      L U) {b₂ : S₂ → Option (Option Bool)} (hb : zr_BackIs C₂ b₂ fun _ => false) :
    zr_BackIs (zr_peekRound x V j δ v a hv L U hL hU h₂)
      (zr_branchBack (zr_oneBack (some false) true) b₂) v :=
  zr_BackIs_congr (zr_anchBranch_back _ _ _ _ hb true) fun P => by cases v P <;> rfl

/-- **A pop round**: on an empty stack stop at the anchor; otherwise run the arm. -/
private def zr_popRound {k : ℕ} {S₂ : Type} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (a : zr_Px k → ℤ) (L U : zr_Px k → Fin 2 → ℤ)
    (hL : ∀ P, V P → ∀ i, L P i ≤ zr_heads (a P) P.s i - 1)
    (hU : ∀ P, V P → ∀ i, zr_heads (a P) P.s i + 1 ≤ U P i)
    {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ (zr_Px k) x} {T₂ : zr_Px k → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₂ : zr_Px k → Fin 2 → ℤ} {τ₂ : zr_Px k → ℕ}
    (h₂ : zr_PinStep C₂ (fun P => V P ∧ zr_popE P = false) zr_pT T₂
      (fun P => zr_heads (a P) P.s) p₂ τ₂ L U) :=
  zr_peekRound x V 1 (-1) zr_popE a (fun _ => rfl) L U hL hU h₂

/-- A pop round is a pinned step to the arm's endpoint pin, which an empty stack meets. -/
private lemma zr_popRound_step {k : ℕ} {S₂ : Type} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (a : zr_Px k → ℤ) (L U : zr_Px k → Fin 2 → ℤ)
    (hL : ∀ P, V P → ∀ i, L P i ≤ zr_heads (a P) P.s i - 1)
    (hU : ∀ P, V P → ∀ i, zr_heads (a P) P.s i + 1 ≤ U P i)
    {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ (zr_Px k) x} {T₂ : zr_Px k → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₂ : zr_Px k → Fin 2 → ℤ} {τ₂ : zr_Px k → ℕ}
    (h₂ : zr_PinStep C₂ (fun P => V P ∧ zr_popE P = false) zr_pT T₂
      (fun P => zr_heads (a P) P.s) p₂ τ₂ L U)
    (hesc : ∀ P, V P → zr_popE P = true → T₂ P = zr_pT P ∧ p₂ P = zr_heads (a P) P.s) :
    zr_PinStep (zr_popRound x V a L U hL hU h₂) V zr_pT T₂ (fun P => zr_heads (a P) P.s) p₂
      (fun P => 3 + 1 + if zr_popE P then 0 else τ₂ P) L U :=
  zr_peekRound_step x V 1 (-1) zr_popE a (fun _ => rfl) L U hL hU h₂ hesc

/-- At an empty stack a pop pass's next index is the index itself. -/
private lemma zr_popEsc {k : ℕ} {c : ℤ} {P : zr_Px k} (N : zr_Px k) (H : zr_Px k → Fin 2 → ℤ)
    (hV : zr_popV c P) (hp : zr_popE P = true) :
    zr_pT (if P.s ≤ P.b then P else N) = zr_pT P ∧ H (if P.s ≤ P.b then P else N) = H P := by
  have hs : P.s ≤ P.b := by
    rw [zr_popE_eq hV.1 hV.2.1, decide_eq_true_iff] at hp
    omega
  rw [if_pos hs]
  exact ⟨rfl, rfl⟩

/-- At the home a return's next index is the index itself. -/
private lemma zr_homeEsc {k : ℕ} {P : zr_Px k} {v : Bool} (N : zr_Px k) (H : zr_Px k → Fin 2 → ℤ)
    (hh : v = true) (hv : v = decide (P.i = 0)) :
    zr_pT (if P.i = 0 then P else N) = zr_pT P ∧ H (if P.i = 0 then P else N) = H P := by
  have hi : P.i = 0 := by rwa [hv, decide_eq_true_iff] at hh
  rw [if_pos hi]
  exact ⟨rfl, rfl⟩

/-- A pop round escapes exactly on an empty stack. -/
private lemma zr_popRound_back {k : ℕ} {S₂ : Type} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (a : zr_Px k → ℤ) (L U : zr_Px k → Fin 2 → ℤ)
    (hL : ∀ P, V P → ∀ i, L P i ≤ zr_heads (a P) P.s i - 1)
    (hU : ∀ P, V P → ∀ i, zr_heads (a P) P.s i + 1 ≤ U P i)
    {M₂ : MultiTapeTM 2 (ZoneSym k) S₂} {e₂ : S₂} {X₂ : Set (Option S₂)}
    {C₂ : Contract M₂ e₂ X₂ (zr_Px k) x} {T₂ : zr_Px k → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₂ : zr_Px k → Fin 2 → ℤ} {τ₂ : zr_Px k → ℕ}
    (h₂ : zr_PinStep C₂ (fun P => V P ∧ zr_popE P = false) zr_pT T₂
      (fun P => zr_heads (a P) P.s) p₂ τ₂ L U) {b₂ : S₂ → Option (Option Bool)}
    (hb : zr_BackIs C₂ b₂ fun _ => false) :
    zr_BackIs (zr_popRound x V a L U hL hU h₂) (zr_branchBack (zr_oneBack (some false) true) b₂)
      zr_popE :=
  zr_peekRound_back x V 1 (-1) zr_popE a (fun _ => rfl) L U hL hU h₂ hb

/-- The walk out's lead, from the anchor to the next index's anchor, in the round box. -/
private lemma zr_woLead_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_ldLead x (fun P => zr_woV P ∧ zr_popE P = false) fun _ h => zr_wo_lead h).C
      (fun P => zr_woV P ∧ zr_popE P = false) zr_pT (fun P => zr_pT (zr_woNxt t P)) zr_lH
      (fun P => zr_lH (zr_woNxt t P))
      (fun P => 1 + 1 + 1 + 1 + ((zr_lfield P.D.2 (P.i + 1)).length + 3)) zr_woL zr_woU := by
  refine zr_PinStep_congr (zr_ldLead x _ _).step (fun P hP => ?_) (fun P hP => ?_)
    (fun _ _ => rfl) (fun P hP i => ?_) (fun P hP i => ?_)
  · have hs := (zr_wo_lead hP).1.2
    show _ = zr_pT (if P.s ≤ P.b then P else _)
    rw [if_neg (by omega)]
    show _ = zr_tapes (zonedTape (Function.update P.D.2 t (P.D.2 t))) (zr_stk P.β P.b (P.s + -1))
    rw [Function.update_eq_self, ← sub_eq_add_neg]
  · have hs := (zr_wo_lead hP).1.2
    show _ = zr_lH (if P.s ≤ P.b then P else _)
    rw [if_neg (by omega)]
    show _ = zr_heads (zr_lstart (P.i + 1)) (P.s + -1)
    rw [← sub_eq_add_neg]
  · fin_cases i
    · show (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 1) - 1) ≤
        zr_lstart (P.i + 1) - 1
      rw [hP.2, if_neg Bool.false_ne_true]
    · show P.s - 2 ≤ P.s - 1
      omega
  · fin_cases i
    · show zr_lstart P.i ≤ zr_lstart P.i + 1
      omega
    · show P.s ≤ P.s + 1
      omega

/-- **The walk out's round body**: on an empty stack stop; otherwise pop a mark and step out one
left field. -/
private def zr_woBody {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_popRound x zr_woV (fun P => zr_lstart P.i) zr_woL zr_woU (fun P _ i => by
      have := zr_lstart_anti (show P.i ≤ P.i + 1 by omega)
      fin_cases i
      · show (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 1) - 1) ≤ zr_lstart P.i - 1
        split_ifs <;> omega
      · show P.s - 2 ≤ P.s - 1
        omega)
    (fun P _ i => by fin_cases i <;> exact le_refl _) (zr_woLead_step t x)

/-- An anchor lies in the walk out's round box. -/
private lemma zr_wo_anchor {k : ℕ} (P : zr_Px k) :
    ∀ i, zr_woL P i ≤ zr_lH P i ∧ zr_lH P i ≤ zr_woU P i := by
  have := zr_lstart_anti (show P.i ≤ P.i + 1 by omega)
  intro i
  fin_cases i
  · refine ⟨?_, show zr_lstart P.i ≤ zr_lstart P.i + 1 by omega⟩
    show (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 1) - 1) ≤ zr_lstart P.i
    split_ifs <;> omega
  · exact ⟨show P.s - 2 ≤ P.s by omega, show P.s ≤ P.s + 1 by omega⟩

/-- The walk out's round time. -/
private abbrev zr_woTau {k : ℕ} (P : zr_Px k) : ℕ :=
  3 + 1 + if zr_popE P then 0 else zr_woRun P

/-- **The walk out's round** is a pinned step from the anchor to the next index's anchor. -/
private lemma zr_woBody_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_woBody t x) zr_woV zr_pT (fun P => zr_pT (zr_woNxt t P)) zr_lH
      (fun P => zr_lH (zr_woNxt t P))
      zr_woTau zr_woL zr_woU :=
  zr_popRound_step _ _ _ _ _ _ _ _ (fun P hV hp => by
      have hs : P.s ≤ P.b := by
        rw [zr_popE_eq hV.1 hV.2.1, decide_eq_true_iff] at hp
        omega
      exact ⟨show zr_pT (if P.s ≤ P.b then P else _) = _ by rw [if_pos hs],
        show zr_lH (if P.s ≤ P.b then P else _) = _ by rw [if_pos hs]⟩)

/-- The walk out's way back: the empty stack escapes, the lead returns to the anchor. -/
private noncomputable def zr_woBack {k : ℕ} (t : Fin k) :
    zr_stOf (zr_woBody t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_branchBack (zr_oneBack (some false) true)
    (zr_oneBack (zr_exitOf (zr_ldLead ([] : List (ZoneSym k))
      (fun P => zr_woV P ∧ zr_popE P = false) fun _ h => zr_wo_lead h).C) false)

/-- The walk out's round escapes exactly on an empty stack. -/
private lemma zr_woBody_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_woBody t x) (zr_woBack t) zr_popE :=
  zr_popRound_back _ _ _ _ _ _ _ _ (zr_BackIs_one _ false)

/-- The walk out's round's exits are its way back's domain. -/
private lemma zr_woBody_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_woBody t x) ↔ zr_woBack t s ≠ none :=
  zr_branchBack_hX (zr_oneBack_hX _ _) (zr_oneBack_hX _ _)

/-- The walk out's round never halts. -/
private lemma zr_woBody_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_woBody t x) :=
  zr_none_one

/-- A pop pass's unconditional next index: one field out, its level changed by `F`, one mark
popped. -/
private abbrev zr_popF {k : ℕ} (t : Fin k) (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) :
    zr_Px k → zr_Px k :=
  zr_pxNxt t F (fun i => i + 1) (-1)

/-- **A pop pass after `m` rounds**, while marks remain: `m` fields out, `m` marks popped. -/
private lemma zr_pop_iter {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) (P : zr_Px k) (m : ℕ)
    (hm : (m : ℤ) ≤ P.s - P.b) :
    (zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t F))^[m] P = (zr_popF t F)^[m] P ∧
      ((zr_popF t F)^[m] P).D.1 = P.D.1 ∧ ((zr_popF t F)^[m] P).i = P.i + m ∧
      ((zr_popF t F)^[m] P).β = P.β ∧ ((zr_popF t F)^[m] P).b = P.b ∧
      ((zr_popF t F)^[m] P).s = P.s - m := by
  have hit := zr_px_iter t F (fun i => i + 1) (-1) P
  refine ⟨zr_cNxt_iter _ _ P m fun r hr => ?_, ?_⟩
  · obtain ⟨-, -, -, h4, h5⟩ := hit r
    show ¬ ((zr_pxNxt t F (fun i => i + 1) (-1))^[r] P).s ≤
      ((zr_pxNxt t F (fun i => i + 1) (-1))^[r] P).b
    rw [h4, h5]
    have : (r : ℤ) < m := by exact_mod_cast hr
    omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hit m
    exact ⟨by rw [h1], by rw [h2, zr_iterate_succ], h3, h4, by rw [h5]; ring⟩

/-- A pop pass stays valid while marks remain. -/
private lemma zr_pop_valid {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) {c : ℤ} (hc : 0 ≤ c) {P : zr_Px k}
    (hV : zr_popV c P) (m : ℕ) (hm : (m : ℤ) ≤ P.s - P.b) :
    zr_popV c ((zr_popF t F)^[m] P) := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := zr_pop_iter t F P m hm
  obtain ⟨⟨hi, hbs, hβ⟩, hβ1, hl⟩ := hV
  refine ⟨⟨?_, by rw [h4, h5]; omega, fun r hr => ?_⟩, by rw [h3, h4]; exact hβ1, ?_⟩
  · rw [h2, h1]
    omega
  · rw [h3]
    exact hβ r (by rw [h4] at hr; exact hr)
  · rw [h2, h1, h4, h5]
    push_cast
    omega

/-- Round `m` of a pop pass finds the stack empty exactly when all marks are popped. -/
private lemma zr_pop_pop {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) {c : ℤ} (hc : 0 ≤ c) {P : zr_Px k}
    (hV : zr_popV c P) (m : ℕ) (hm : (m : ℤ) ≤ P.s - P.b) :
    zr_popE ((zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t F))^[m] P) = decide (P.s - m = P.b) := by
  obtain ⟨he, -, -, -, h4, h5⟩ := zr_pop_iter t F P m hm
  have hv := zr_pop_valid t F hc hV m hm
  rw [he, zr_popE_eq hv.1 hv.2.1, h5, h4]

/-- A round with marks left leaves a valid index. -/
private lemma zr_pop_next_valid {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) {c : ℤ} (hc : 0 ≤ c) {P : zr_Px k}
    (hV : zr_popV c P) (hp : zr_popE P = false) :
    zr_popV c (zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t F) P) := by
  rw [zr_popE_eq hV.1 hV.2.1, decide_eq_false_iff_not] at hp
  have := hV.1.2.1
  show zr_popV c (if P.s ≤ P.b then P else _)
  rw [if_neg (by omega)]
  exact zr_pop_valid t F hc hV 1 (by push_cast; omega)

/-- The walk out's head box: the zoned head from the outermost field it reaches to the start,
scratch over the marks. -/
private abbrev zr_woLo {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (P.i + (P.s - P.b).toNat) - 1) (P.b - 2)

/-- The walk out's head box, its upper corner. -/
private abbrev zr_woHi {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i + 1) (P.s + 1)

/-- Each round's box lies in the walk out's box. -/
private lemma zr_wo_round_box {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_woV P) (m : ℕ)
    (hm : m ≤ (P.s - P.b).toNat) :
    ∀ i, zr_woLo P i ≤ zr_woL ((zr_woNxt t)^[m] P) i ∧
      zr_woU ((zr_woNxt t)^[m] P) i ≤ zr_woHi P i := by
  have hbs := hV.1.2.1
  have hm' : (m : ℤ) ≤ P.s - P.b := by omega
  obtain ⟨he, -, h2, -, -, h5⟩ := zr_pop_iter t (fun _ _ w => w) P m hm'
  have hp := zr_pop_pop t (fun _ _ w => w) le_rfl hV m hm'
  have he' : (zr_woNxt t)^[m] P = (zr_popF t fun _ _ w => w)^[m] P := he
  rw [he] at hp
  rw [he']
  have ha := zr_lstart_anti (show P.i ≤ P.i + m by omega)
  intro i
  fin_cases i
  · refine ⟨?_, ?_⟩
    · show zr_lstart (P.i + (P.s - P.b).toNat) - 1 ≤
        (if zr_popE ((zr_popF t fun _ _ w => w)^[m] P) then
          zr_lstart ((zr_popF t fun _ _ w => w)^[m] P).i - 1 else
          zr_lstart (((zr_popF t fun _ _ w => w)^[m] P).i + 1) - 1)
      rw [hp, h2]
      by_cases he : P.s - m = P.b
      · rw [decide_eq_true he, if_pos rfl,
          show (P.s - P.b).toNat = m by omega]
      · rw [decide_eq_false he, if_neg Bool.false_ne_true]
        have := zr_lstart_anti (show P.i + m + 1 ≤ P.i + (P.s - P.b).toNat by omega)
        omega
    · show zr_lstart ((zr_popF t fun _ _ w => w)^[m] P).i + 1 ≤ zr_lstart P.i + 1
      rw [h2]
      omega
  · refine ⟨?_, ?_⟩
    · show P.b - 2 ≤ ((zr_popF t fun _ _ w => w)^[m] P).s - 2
      rw [h5]
      omega
    · show ((zr_popF t fun _ _ w => w)^[m] P).s + 1 ≤ P.s + 1
      rw [h5]
      omega

/-- **The walk out**, as a pinned segment on its loop: from the anchor at left field `P.i`'s
outermost cell, one round per count mark pops it and steps one left field out; on the empty stack it
stops. -/
private noncomputable def zr_woPass {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_passSeg (zr_woBack t) (zr_woBody t x) (zr_woBody_none t x) (zr_woBody_hX t x)
    (zr_woBody_step t x) (zr_woBody_back t x)
    (fun _ hV hp => zr_pop_next_valid t (fun _ _ w => w) le_rfl hV hp)
    (sa := .inr (zr_exitOf (zr_ldLead ([] : List (ZoneSym k))
      (fun P => zr_woV P ∧ zr_popE P = false) fun _ h => zr_wo_lead h).C))
    (sb := .inl (.inr (some false)))
    (by
      show zr_oneBack _ false _ = _
      rw [zr_oneBack, if_pos rfl])
    (by
      show zr_oneBack (some false) true (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (fun P => (P.s - P.b).toNat)
    (fun P hV => by
      have := hV.1.2.1
      show zr_popE ((zr_woNxt t)^[(P.s - P.b).toNat] P) = true
      rw [zr_pop_pop t (fun _ _ w => w) le_rfl hV _ (by omega)]
      exact decide_eq_true (by omega))
    (fun P hV m hm => by
      have := hV.1.2.1
      have hm' : m < (P.s - P.b).toNat := hm
      rw [zr_pop_pop t (fun _ _ w => w) le_rfl hV _ (by omega)]
      exact decide_eq_false (by omega))
    zr_woLo zr_woHi (fun P hV m hm => zr_wo_round_box t hV m hm) zr_wo_anchor

/-- A pop pass's shift index: level `P.i + 1`, after the pop. -/
private abbrev zr_popG {k : ℕ} (P : zr_Px k) : zr_Ix k :=
  ⟨P.D, P.i + 1, zr_stk P.β P.b (P.s - 1), P.s - 1⟩

/-- An ascending pass's validity: a pop pass's, with every level it shifts inside the layout. -/
private abbrev zr_upV {k : ℕ} (P : zr_Px k) : Prop := zr_popV 1 P

/-- **The ascending left pass's next index**: one left field out, its level shifted outward,
one mark popped, unless the stack is empty. -/
private abbrev zr_p4Nxt {k : ℕ} (t : Fin k) : zr_Px k → zr_Px k :=
  zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t fun _ i w => zoneShiftOut false (i + 1) w)

/-- With marks left, an ascending pass's index meets its lead's requirements. -/
private lemma zr_up_lead {k : ℕ} {P : zr_Px k} (h : zr_upV P ∧ zr_popE P = false) :
    (zr_pxV P ∧ P.b < P.s) ∧ P.i < P.D.1 :=
  zr_wo_lead ⟨⟨h.1.1, h.1.2.1, by have := h.1.2.2; omega⟩, h.2⟩

/-- The ascending passes' guard: a pop index with marks left. -/
private abbrev zr_upOn {k : ℕ} (P : zr_Px k) : Prop := zr_upV P ∧ zr_popE P = false

/-- With marks left, a pop pass's shift index meets the shift's requirements. -/
private lemma zr_popG_pre {k : ℕ} {P : zr_Px k} (h : zr_upOn P) :
    zr_shPre (zr_popG P) := by
  have hb := (zr_up_lead h).1.2
  obtain ⟨⟨hV, hβ, hl⟩, -⟩ := h
  refine ⟨show 1 ≤ P.i + 1 by omega, show P.i + 1 < P.D.1 by omega, fun r hr => ?_⟩
  have hr' : P.s - 1 ≤ r := hr
  show zr_stk P.β P.b (P.s - 1) r = none
  rw [zr_stk, if_neg (by omega)]
  exact hV.2.2 r (by omega)

/-- The ascending left pass's round box, its lower corner: the shift's reach unless the stack is
empty. -/
private abbrev zr_p4L {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 2) - 2) (P.s - 2)

/-- The ascending left pass's round box, its upper corner. -/
private abbrev zr_p4U {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if zr_popE P then zr_lstart P.i + 1 else zr_lstart P.i + zr_hh (zr_popG P) + 1)
    (P.s + 6 * zr_hh (zr_popG P) + 3)

/-- The ascending left pass's arm: the lead, then the guarded outward shift at level
`P.i + 1`. -/
private abbrev zr_p4Arm {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  (zr_ldLead x (fun P => zr_upV P ∧ zr_popE P = false) fun _ h => zr_up_lead h).C.seq
    (zr_grdOut t x zr_popG (fun P => zr_upV P ∧ zr_popE P = false) fun _ h => zr_popG_pre h)
    (fun P => P)
    (zr_pin_hlink (zr_ldLead x _ _).step (zr_grdOut_step t x zr_popG _ fun _ h => zr_popG_pre h))

/-- The ascending left pass's arm, from the anchor to the next index's anchor, in the round
box. -/
private lemma zr_p4Arm_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p4Arm t x) (fun P => zr_upV P ∧ zr_popE P = false) zr_pT
      (fun P => zr_pT (zr_p4Nxt t P)) zr_lH (fun P => zr_lH (zr_p4Nxt t P))
      (fun P => 1 + 1 + 1 + 1 + ((zr_lfield P.D.2 (P.i + 1)).length + 3) + 1 +
        (1 + 1 + if zr_out1Off t (zr_popG P) then 0 else
          11 * zr_hh (zr_popG P) + 20 + 1 + (1 + 1 + if zr_out2Off t (zr_popG P) then
            6 * zr_hh (zr_popG P) + 11 else
            6 * zr_hh (zr_popG P) + 11 + 1 + (76 * zr_hh (zr_popG P) + 107))))
      zr_p4L zr_p4U := by
  have hL : ∀ P : zr_Px k, zr_upV P ∧ zr_popE P = false → ∀ i, zr_p4L P i ≤ zr_ldL P i ∧
      zr_p4L P i ≤ zr_goL (zr_popG P) i := by
    intro P hP i
    have := zr_lstart_anti (show P.i + 1 ≤ P.i + 2 by omega)
    fin_cases i
    · show (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 2) - 2) ≤
        zr_lstart (P.i + 1) - 1 ∧
        (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 2) - 2) ≤
          zr_lstart (P.i + 1 + 1) - 2
      rw [hP.2, if_neg Bool.false_ne_true, show P.i + 1 + 1 = P.i + 2 by omega]
      omega
    · exact ⟨show P.s - 2 ≤ P.s - 1 by omega, show P.s - 2 ≤ P.s - 1 - 1 by omega⟩
  have hU : ∀ P : zr_Px k, zr_upV P ∧ zr_popE P = false → ∀ i, zr_ldU P i ≤ zr_p4U P i ∧
      zr_goU (zr_popG P) i ≤ zr_p4U P i := by
    intro P hP i
    fin_cases i
    · show zr_lstart P.i ≤
        (if zr_popE P then zr_lstart P.i + 1 else zr_lstart P.i + zr_hh (zr_popG P) + 1) ∧
        zr_lstart (P.i + 1 - 1) + zr_hh (zr_popG P) + 1 ≤
          (if zr_popE P then zr_lstart P.i + 1 else zr_lstart P.i + zr_hh (zr_popG P) + 1)
      rw [hP.2, if_neg Bool.false_ne_true, Nat.add_sub_cancel]
      omega
    · exact ⟨show P.s ≤ P.s + 6 * zr_hh (zr_popG P) + 3 by omega,
        show P.s - 1 + 6 * zr_hh (zr_popG P) + 3 ≤ P.s + 6 * zr_hh (zr_popG P) + 3 by omega⟩
  refine zr_PinStep_seq' (zr_PinStep_congr (zr_ldLead x _ _).step (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun P hP i => (hL P hP i).1)
      (fun P hP i => (hU P hP i).1))
    (zr_PinStep_congr (zr_grdOut_step t x zr_popG _ fun _ h => zr_popG_pre h)
      (fun P hP => ?_) (fun P hP => ?_) (fun _ _ => rfl) (fun P hP i => (hL P hP i).2)
      (fun P hP i => (hU P hP i).2)) _
  · have hs := (zr_up_lead hP).1.2
    show _ = zr_pT (if P.s ≤ P.b then P else _)
    rw [if_neg (by omega)]
    show _ = zr_tapes (zonedTape (Function.update P.D.2 t
      (zoneShiftOut false (P.i + 1) (P.D.2 t)))) (zr_stk P.β P.b (P.s + -1))
    rw [← sub_eq_add_neg]
  · have hs := (zr_up_lead hP).1.2
    show _ = zr_lH (if P.s ≤ P.b then P else _)
    rw [if_neg (by omega)]
    show _ = zr_heads (zr_lstart (P.i + 1)) (P.s + -1)
    rw [← sub_eq_add_neg]

/-- **The ascending left pass's round body**: on an empty stack stop; otherwise pop a mark, step
out one left field and run the guarded outward shift at its level. -/
private def zr_p4Body {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_popRound x zr_upV (fun P => zr_lstart P.i) zr_p4L zr_p4U (fun P _ i => by
      have := zr_lstart_anti (show P.i ≤ P.i + 2 by omega)
      fin_cases i
      · show (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 2) - 2) ≤ zr_lstart P.i - 1
        split_ifs <;> omega
      · show P.s - 2 ≤ P.s - 1
        omega)
    (fun P _ i => by
      fin_cases i
      · show zr_lstart P.i + 1 ≤
          (if zr_popE P then zr_lstart P.i + 1 else zr_lstart P.i + zr_hh (zr_popG P) + 1)
        have := Nat.two_pow_pos (P.i + 1 - 1)
        split_ifs <;> omega
      · show P.s + 1 ≤ P.s + 6 * zr_hh (zr_popG P) + 3
        have := Nat.two_pow_pos (P.i + 1 - 1)
        omega) (zr_p4Arm_step t x)

/-- A left field's outermost cell plus its length decreases outward. -/
private lemma zr_lstart_pow_anti {m n : ℕ} (h : m ≤ n) :
    zr_lstart n + ((2 ^ n : ℕ) : ℤ) ≤ zr_lstart m + ((2 ^ m : ℕ) : ℤ) := by
  have := zr_rstart_mono h
  rw [zr_lstart, zr_lstart]
  omega

/-- An anchor lies in the ascending left pass's round box. -/
private lemma zr_p4_anchor {k : ℕ} (P : zr_Px k) :
    ∀ i, zr_p4L P i ≤ zr_lH P i ∧ zr_lH P i ≤ zr_p4U P i := by
  have := zr_lstart_anti (show P.i ≤ P.i + 2 by omega)
  have := Nat.two_pow_pos (P.i + 1 - 1)
  intro i
  fin_cases i
  · constructor
    · show (if zr_popE P then zr_lstart P.i - 1 else zr_lstart (P.i + 2) - 2) ≤ zr_lstart P.i
      split_ifs <;> omega
    · show zr_lstart P.i ≤
        (if zr_popE P then zr_lstart P.i + 1 else zr_lstart P.i + zr_hh (zr_popG P) + 1)
      split_ifs <;> omega
  · exact ⟨show P.s - 2 ≤ P.s by omega, show P.s ≤ P.s + 6 * zr_hh (zr_popG P) + 3 by omega⟩

/-- The ascending left pass's round time. -/
private abbrev zr_p4Tau {k : ℕ} (t : Fin k) (P : zr_Px k) : ℕ :=
  3 + 1 + if zr_popE P then 0 else
    zr_woRun P + 1 + (1 + 1 + if zr_out1Off t (zr_popG P) then 0 else
      11 * zr_hh (zr_popG P) + 20 + 1 + (1 + 1 + if zr_out2Off t (zr_popG P) then
        6 * zr_hh (zr_popG P) + 11 else
        6 * zr_hh (zr_popG P) + 11 + 1 + (76 * zr_hh (zr_popG P) + 107)))

/-- **The ascending left pass's round** is a pinned step from the anchor to the next index's
anchor. -/
private lemma zr_p4Body_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p4Body t x) zr_upV zr_pT (fun P => zr_pT (zr_p4Nxt t P)) zr_lH
      (fun P => zr_lH (zr_p4Nxt t P))
      (zr_p4Tau t) zr_p4L zr_p4U :=
  zr_popRound_step _ _ _ _ _ _ _ _ fun _ hV hp => zr_popEsc _ zr_lH hV hp

/-- The ascending left pass's way back: the empty stack escapes, the guarded shift's exits
return to the anchor. -/
private noncomputable def zr_p4Back {k : ℕ} (t : Fin k) :
    zr_stOf (zr_p4Body t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_branchBack (zr_oneBack (some false) true) (zr_seqBack (zr_grdOutBack t))

/-- The ascending left pass's round escapes exactly on an empty stack. -/
private lemma zr_p4Body_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_p4Body t x) (zr_p4Back t) zr_popE :=
  zr_popRound_back _ _ _ _ _ _ _ _ (zr_BackIs_seq (zr_grdOut_back t x _ _ _))

/-- The ascending left pass's round's exits are its way back's domain. -/
private lemma zr_p4Body_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_p4Body t x) ↔ zr_p4Back t s ≠ none :=
  zr_popBack_hX (zr_grdOut_hX t x zr_popG zr_upOn fun _ => zr_popG_pre)

/-- The ascending left pass's round never halts. -/
private lemma zr_p4Body_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_p4Body t x) :=
  zr_none_up (zr_grdOut_none t x zr_popG zr_upOn fun _ => zr_popG_pre)

/-- The ascending left pass's head box: the zoned head from two cells past the outermost zone it
shifts to the start's field and its reach, scratch over the marks and the shifts' work areas. -/
private abbrev zr_p4Lo {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (P.i + (P.s - P.b).toNat + 1) - 2) (P.b - 2)

/-- The ascending left pass's head box, its upper corner. -/
private abbrev zr_p4Hi {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart P.i + ((2 ^ P.i : ℕ) : ℤ) + 1)
    (P.s + 6 * ((2 ^ (P.i + (P.s - P.b).toNat) : ℕ) : ℤ) + 3)

/-- Each round's box lies in the ascending left pass's box. -/
private lemma zr_p4_round_box {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_upV P) (m : ℕ)
    (hm : m ≤ (P.s - P.b).toNat) :
    ∀ i, zr_p4Lo P i ≤ zr_p4L ((zr_p4Nxt t)^[m] P) i ∧
      zr_p4U ((zr_p4Nxt t)^[m] P) i ≤ zr_p4Hi P i := by
  have hbs := hV.1.2.1
  have hm' : (m : ℤ) ≤ P.s - P.b := by omega
  have hc : (0 : ℤ) ≤ 1 := by omega
  obtain ⟨he, -, h2, -, -, h5⟩ :=
    zr_pop_iter t (fun _ i w => zoneShiftOut false (i + 1) w) P m hm'
  have hp := zr_pop_pop t (fun _ i w => zoneShiftOut false (i + 1) w) hc hV m hm'
  have he' : (zr_p4Nxt t)^[m] P =
    (zr_popF t fun _ i w => zoneShiftOut false (i + 1) w)^[m] P := he
  rw [he] at hp
  rw [he']
  set Q := (zr_popF t fun _ i w => zoneShiftOut false (i + 1) w)^[m] P with hQ
  have hpa := zr_lstart_pow_anti (show P.i ≤ P.i + m by omega)
  have hpw : 2 ^ (P.i + m) ≤ 2 ^ (P.i + (P.s - P.b).toNat) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpw' : ((2 ^ (P.i + m) : ℕ) : ℤ) ≤ ((2 ^ (P.i + (P.s - P.b).toNat) : ℕ) : ℤ) := by
    exact_mod_cast hpw
  have hh : zr_hh (zr_popG Q) = 2 ^ (P.i + m) := by
    show 2 ^ (Q.i + 1 - 1) = _
    rw [h2, Nat.add_sub_cancel]
  intro i
  fin_cases i
  · refine ⟨?_, ?_⟩
    · show zr_lstart (P.i + (P.s - P.b).toNat + 1) - 2 ≤
        (if zr_popE Q then zr_lstart Q.i - 1 else zr_lstart (Q.i + 2) - 2)
      rw [hp, h2]
      by_cases he2 : P.s - m = P.b
      · rw [decide_eq_true he2, if_pos rfl, show (P.s - P.b).toNat = m by omega]
        have := zr_lstart_anti (show P.i + m ≤ P.i + m + 1 by omega)
        omega
      · rw [decide_eq_false he2, if_neg Bool.false_ne_true]
        have := zr_lstart_anti (show P.i + m + 2 ≤ P.i + (P.s - P.b).toNat + 1 by omega)
        omega
    · show (if zr_popE Q then zr_lstart Q.i + 1 else zr_lstart Q.i + zr_hh (zr_popG Q) + 1) ≤
        zr_lstart P.i + ((2 ^ P.i : ℕ) : ℤ) + 1
      rw [hh, h2]
      have := Nat.two_pow_pos (P.i + m)
      split_ifs <;> omega
  · refine ⟨?_, ?_⟩
    · show P.b - 2 ≤ Q.s - 2
      rw [h5]
      omega
    · show Q.s + 6 * (zr_hh (zr_popG Q) : ℤ) + 3 ≤
        P.s + 6 * ((2 ^ (P.i + (P.s - P.b).toNat) : ℕ) : ℤ) + 3
      rw [hh, h5]
      omega

/-- **The ascending left pass**, as a pinned segment on its loop: from the anchor at left field
`P.i`'s outermost cell, one round per count mark pops it, steps one left field out and runs the
guarded outward shift at that field's level; on the empty stack it stops. -/
private noncomputable def zr_p4Pass {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_passSeg (zr_p4Back t) (zr_p4Body t x) (zr_p4Body_none t x) (zr_p4Body_hX t x)
    (zr_p4Body_step t x) (zr_p4Body_back t x)
    (fun _ hV hp => zr_pop_next_valid t _ (by omega) hV hp)
    (sa := .inr (.inr (.inl (.inr (some false))))) (sb := .inl (.inr (some false)))
    (by
      show zr_oneBack (some false) false (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (by
      show zr_oneBack (some false) true (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (fun P => (P.s - P.b).toNat)
    (fun P hV => by
      have := hV.1.2.1
      show zr_popE ((zr_p4Nxt t)^[(P.s - P.b).toNat] P) = true
      rw [zr_pop_pop t _ (by omega) hV _ (by omega)]
      exact decide_eq_true (by omega))
    (fun P hV m hm => by
      have := hV.1.2.1
      have hm' : m < (P.s - P.b).toNat := hm
      rw [zr_pop_pop t _ (by omega) hV _ (by omega)]
      exact decide_eq_false (by omega))
    zr_p4Lo zr_p4Hi (fun P hV m hm => zr_p4_round_box t hV m hm) zr_p4_anchor

/-- The right outward lead's box, its lower corner. -/
private abbrev zr_reL {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_rstart P.i) (P.s - 1)

/-- The right outward lead's box, its upper corner. -/
private abbrev zr_reU {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_rstart (P.i + 1)) P.s

/-- **The right outward lead**: pop a count mark, then skip over right field `P.i` to the next
field's start. -/
private def zr_reLead {k : ℕ} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (hV : ∀ P, V P → (zr_pxV P ∧ P.b < P.s) ∧ P.i < P.D.1) :=
  show zr_PinSeg x _ _ _ V zr_pT zr_popT (fun P => zr_heads (zr_rstart P.i) P.s)
      (fun P => zr_heads (zr_rstart (P.i + 1)) (P.s - 1)) _ zr_reL zr_reU from
  zr_segSeq (zr_seg (zr_popSeg x V (fun P => zr_rstart P.i) fun P h => (hV P h).1).step
      (fun _ _ => rfl) fun P _ => by
        have := zr_rstart_mono (show P.i ≤ P.i + 1 by omega)
        exact ⟨rfl, zr_heads_le le_rfl le_rfl,
          zr_heads_le (show zr_rstart P.i ≤ zr_rstart (P.i + 1) by omega) le_rfl⟩)
    (zr_seg (zr_pinSkip_step (x := x) V 0 (fun P => zr_rfield P.D.2 P.i) zr_popT
        (fun P => zr_heads (zr_rstart P.i) (P.s - 1)) fun P hP q h1 h2 => by
          have hi := (hV P hP).2
          show zonedTape P.D.2 (zr_rstart P.i + q) = _
          exact zr_rfield_at P.D.2 P.i (by omega) _ rfl q (by omega) h2)
      (fun _ _ => rfl) fun P hP => by
        have hi := (hV P hP).2
        have hl := zr_rfield_length P.D.2 P.i (by omega)
        have hs := zr_rstart_succ P.i
        refine ⟨?_, zr_heads_le le_rfl le_rfl, ?_⟩
        · show Function.update (zr_heads (zr_rstart P.i) (P.s - 1)) 0
            (zr_rstart P.i + ((zr_rfield P.D.2 P.i).length : ℤ) + 1) = _
          rw [zr_heads_set0, hl, hs]
        · show ∀ i, Function.update (zr_heads (zr_rstart P.i) (P.s - 1)) 0
            (zr_rstart P.i + ((zr_rfield P.D.2 P.i).length : ℤ) + 1) i ≤ zr_reU P i
          rw [zr_heads_set0, hl, ← hs]
          exact zr_heads_le le_rfl (show P.s - 1 ≤ P.s by omega))

/-- **The ascending right pass's next index**: one right field out, its level shifted inward,
one mark popped, unless the stack is empty. -/
private abbrev zr_p3Nxt {k : ℕ} (t : Fin k) : zr_Px k → zr_Px k :=
  zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t fun _ i w => zoneShiftIn true (i + 1) w)

/-- The ascending right pass's round box, its lower corner. -/
private abbrev zr_p3L {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_rstart P.i - 1) (P.s - 2)

/-- The ascending right pass's round box, its upper corner: the shift's reach unless the stack
is empty. -/
private abbrev zr_p3U {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if zr_popE P then zr_rstart P.i + 1 else
    zr_rstart (P.i + 2) + 4 * zr_hh (zr_popG P)) (P.s + 8 * zr_hh (zr_popG P) + 1)

/-- The ascending right pass's arm: the lead, then the guarded inward shift at level
`P.i + 1`. -/
private abbrev zr_p3Arm {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  (zr_reLead x (fun P => zr_upV P ∧ zr_popE P = false) fun _ h => zr_up_lead h).C.seq
    (zr_grdIn t x zr_popG (fun P => zr_upV P ∧ zr_popE P = false) fun _ h => zr_popG_pre h)
    (fun P => P)
    (zr_pin_hlink (zr_reLead x _ _).step (zr_grdIn_step t x zr_popG _ fun _ h => zr_popG_pre h))

/-- The ascending right pass's arm, from the anchor to the next index's anchor, in the round
box. -/
private lemma zr_p3Arm_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p3Arm t x) (fun P => zr_upV P ∧ zr_popE P = false) zr_pT
      (fun P => zr_pT (zr_p3Nxt t P)) zr_rH (fun P => zr_rH (zr_p3Nxt t P))
      (fun P => 1 + 1 + 1 + 1 + ((zr_rfield P.D.2 P.i).length + 1) + 1 +
        (1 + 1 + if zr_inOff t (zr_popG P) then 0 else 76 * zr_hh (zr_popG P) + 77))
      zr_p3L zr_p3U := by
  have hL : ∀ P : zr_Px k, ∀ i, zr_p3L P i ≤ zr_reL P i ∧
      zr_p3L P i ≤ zr_inL (zr_popG P) i := by
    intro P i
    fin_cases i
    · exact ⟨show zr_rstart P.i - 1 ≤ zr_rstart P.i by omega,
        show zr_rstart P.i - 1 ≤ zr_rstart (P.i + 1 - 1) - 1 by rw [Nat.add_sub_cancel]⟩
    · exact ⟨show P.s - 2 ≤ P.s - 1 by omega, show P.s - 2 ≤ P.s - 1 by omega⟩
  have hU : ∀ P : zr_Px k, zr_upV P ∧ zr_popE P = false → ∀ i, zr_reU P i ≤ zr_p3U P i ∧
      zr_inU (zr_popG P) i ≤ zr_p3U P i := by
    intro P hP i
    have := zr_rstart_mono (show P.i + 1 ≤ P.i + 2 by omega)
    fin_cases i
    · show zr_rstart (P.i + 1) ≤ (if zr_popE P then zr_rstart P.i + 1 else
          zr_rstart (P.i + 2) + 4 * zr_hh (zr_popG P)) ∧
        zr_rstart (P.i + 1 + 1) + 4 * zr_hh (zr_popG P) ≤ (if zr_popE P then zr_rstart P.i + 1
          else zr_rstart (P.i + 2) + 4 * zr_hh (zr_popG P))
      rw [hP.2, if_neg Bool.false_ne_true, show P.i + 1 + 1 = P.i + 2 by omega]
      omega
    · exact ⟨show P.s ≤ P.s + 8 * zr_hh (zr_popG P) + 1 by omega,
        show P.s - 1 + 8 * zr_hh (zr_popG P) + 2 ≤ P.s + 8 * zr_hh (zr_popG P) + 1 by omega⟩
  refine zr_PinStep_seq' (zr_PinStep_congr (zr_reLead x _ _).step (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun P _ i => (hL P i).1)
      (fun P hP i => (hU P hP i).1))
    (zr_PinStep_congr (zr_grdIn_step t x zr_popG _ fun _ h => zr_popG_pre h)
      (fun P hP => ?_) (fun P hP => ?_) (fun _ _ => rfl) (fun P _ i => (hL P i).2)
      (fun P hP i => (hU P hP i).2)) _
  · have hs := (zr_up_lead hP).1.2
    show _ = zr_pT (if P.s ≤ P.b then P else _)
    rw [if_neg (by omega)]
    show _ = zr_tapes (zonedTape (Function.update P.D.2 t
      (zoneShiftIn true (P.i + 1) (P.D.2 t)))) (zr_stk P.β P.b (P.s + -1))
    rw [← sub_eq_add_neg]
  · have hs := (zr_up_lead hP).1.2
    show _ = zr_rH (if P.s ≤ P.b then P else _)
    rw [if_neg (by omega)]
    show _ = zr_heads (zr_rstart (P.i + 1)) (P.s + -1)
    rw [← sub_eq_add_neg]

/-- **The ascending right pass's round body**: on an empty stack stop; otherwise pop a mark, step
out one right field and run the guarded inward shift at its level. -/
private def zr_p3Body {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_popRound x zr_upV (fun P => zr_rstart P.i) zr_p3L zr_p3U (fun P _ i => by
      fin_cases i
      · exact le_refl (zr_rstart P.i - 1)
      · show P.s - 2 ≤ P.s - 1
        omega)
    (fun P _ i => by
      fin_cases i
      · show zr_rstart P.i + 1 ≤ (if zr_popE P then zr_rstart P.i + 1 else
          zr_rstart (P.i + 2) + 4 * zr_hh (zr_popG P))
        have := zr_rstart_succ (P.i + 1)
        rw [show P.i + 1 + 1 = P.i + 2 by omega] at this
        have := zr_rstart_succ P.i
        have : (0 : ℤ) < ((2 ^ P.i : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos _
        have : (0 : ℤ) < ((2 ^ (P.i + 1) : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos _
        split_ifs <;> omega
      · show P.s + 1 ≤ P.s + 8 * zr_hh (zr_popG P) + 1
        omega) (zr_p3Arm_step t x)

/-- An anchor lies in the ascending right pass's round box. -/
private lemma zr_p3_anchor {k : ℕ} (P : zr_Px k) :
    ∀ i, zr_p3L P i ≤ zr_rH P i ∧ zr_rH P i ≤ zr_p3U P i := by
  have := zr_rstart_succ (P.i + 1)
  rw [show P.i + 1 + 1 = P.i + 2 by omega] at this
  have := zr_rstart_succ P.i
  have : (0 : ℤ) < ((2 ^ P.i : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos _
  have : (0 : ℤ) < ((2 ^ (P.i + 1) : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos _
  intro i
  fin_cases i
  · refine ⟨show zr_rstart P.i - 1 ≤ zr_rstart P.i by omega, ?_⟩
    show zr_rstart P.i ≤ (if zr_popE P then zr_rstart P.i + 1 else
      zr_rstart (P.i + 2) + 4 * zr_hh (zr_popG P))
    split_ifs <;> omega
  · exact ⟨show P.s - 2 ≤ P.s by omega, show P.s ≤ P.s + 8 * zr_hh (zr_popG P) + 1 by omega⟩

/-- The ascending right pass's round time. -/
private abbrev zr_p3Tau {k : ℕ} (t : Fin k) (P : zr_Px k) : ℕ :=
  3 + 1 + if zr_popE P then 0 else
    1 + 1 + 1 + 1 + ((zr_rfield P.D.2 P.i).length + 1) + 1 +
    (1 + 1 + if zr_inOff t (zr_popG P) then 0 else 76 * zr_hh (zr_popG P) + 77)

/-- **The ascending right pass's round** is a pinned step from the anchor to the next index's
anchor. -/
private lemma zr_p3Body_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p3Body t x) zr_upV zr_pT (fun P => zr_pT (zr_p3Nxt t P)) zr_rH
      (fun P => zr_rH (zr_p3Nxt t P))
      (zr_p3Tau t) zr_p3L zr_p3U :=
  zr_popRound_step _ _ _ _ _ _ _ _ fun _ hV hp => zr_popEsc _ zr_rH hV hp

/-- The ascending right pass's way back: the empty stack escapes, the guarded shift's exits
return to the anchor. -/
private noncomputable def zr_p3Back {k : ℕ} (t : Fin k) :
    zr_stOf (zr_p3Body t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_branchBack (zr_oneBack (some false) true) (zr_seqBack (zr_grdInBack t))

/-- The ascending right pass's round escapes exactly on an empty stack. -/
private lemma zr_p3Body_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_p3Body t x) (zr_p3Back t) zr_popE :=
  zr_popRound_back _ _ _ _ _ _ _ _ (zr_BackIs_seq (zr_grdIn_back t x _ _ _))

/-- The ascending right pass's round's exits are its way back's domain. -/
private lemma zr_p3Body_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_p3Body t x) ↔ zr_p3Back t s ≠ none :=
  zr_popBack_hX (zr_grdIn_hX t x zr_popG zr_upOn fun _ => zr_popG_pre)

/-- The ascending right pass's round never halts. -/
private lemma zr_p3Body_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_p3Body t x) :=
  zr_none_up (zr_grdIn_none t x zr_popG zr_upOn fun _ => zr_popG_pre)

/-- The ascending right pass's head box: the zoned head from one cell left of the start's field
to the last shift's reach, scratch over the marks and the shifts' work areas. -/
private abbrev zr_p3Lo {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_rstart P.i - 1) (P.b - 2)

/-- The ascending right pass's head box, its upper corner. -/
private abbrev zr_p3Hi {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if (P.s - P.b).toNat = 0 then zr_rstart P.i + 1 else
    zr_rstart (P.i + (P.s - P.b).toNat + 1) +
      4 * ((2 ^ (P.i + (P.s - P.b).toNat - 1) : ℕ) : ℤ))
    (P.s + 8 * ((2 ^ (P.i + (P.s - P.b).toNat) : ℕ) : ℤ) + 1)

/-- Each round's box lies in the ascending right pass's box. -/
private lemma zr_p3_round_box {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_upV P) (m : ℕ)
    (hm : m ≤ (P.s - P.b).toNat) :
    ∀ i, zr_p3Lo P i ≤ zr_p3L ((zr_p3Nxt t)^[m] P) i ∧
      zr_p3U ((zr_p3Nxt t)^[m] P) i ≤ zr_p3Hi P i := by
  have hbs := hV.1.2.1
  have hm' : (m : ℤ) ≤ P.s - P.b := by omega
  have hc : (0 : ℤ) ≤ 1 := by omega
  obtain ⟨he, -, h2, -, -, h5⟩ := zr_pop_iter t (fun _ i w => zoneShiftIn true (i + 1) w) P m hm'
  have hp := zr_pop_pop t (fun _ i w => zoneShiftIn true (i + 1) w) hc hV m hm'
  have he' : (zr_p3Nxt t)^[m] P = (zr_popF t fun _ i w => zoneShiftIn true (i + 1) w)^[m] P := he
  rw [he] at hp
  rw [he']
  set Q := (zr_popF t fun _ i w => zoneShiftIn true (i + 1) w)^[m] P with hQ
  have hh : zr_hh (zr_popG Q) = 2 ^ (P.i + m) := by
    show 2 ^ (Q.i + 1 - 1) = _
    rw [h2, Nat.add_sub_cancel]
  have hpw : 2 ^ (P.i + m) ≤ 2 ^ (P.i + (P.s - P.b).toNat) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpw' : ((2 ^ (P.i + m) : ℕ) : ℤ) ≤ ((2 ^ (P.i + (P.s - P.b).toNat) : ℕ) : ℤ) := by
    exact_mod_cast hpw
  intro i
  fin_cases i
  · refine ⟨?_, ?_⟩
    · show zr_rstart P.i - 1 ≤ zr_rstart Q.i - 1
      rw [h2]
      have := zr_rstart_mono (show P.i ≤ P.i + m by omega)
      omega
    · show (if zr_popE Q then zr_rstart Q.i + 1 else zr_rstart (Q.i + 2) + 4 * zr_hh (zr_popG Q)) ≤
        (if (P.s - P.b).toNat = 0 then zr_rstart P.i + 1 else
          zr_rstart (P.i + (P.s - P.b).toNat + 1) +
            4 * ((2 ^ (P.i + (P.s - P.b).toNat - 1) : ℕ) : ℤ))
      rw [hp, hh, h2]
      by_cases he2 : P.s - m = P.b
      · rw [decide_eq_true he2, if_pos rfl]
        have hn : (P.s - P.b).toNat = m := by omega
        rw [hn]
        by_cases h0 : m = 0
        · rw [if_pos h0, h0, Nat.add_zero]
        · rw [if_neg h0]
          have := zr_rstart_succ (P.i + m)
          have : (0 : ℤ) < ((2 ^ (P.i + m) : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos _
          have : (0 : ℤ) < ((2 ^ (P.i + m - 1) : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos _
          omega
      · rw [decide_eq_false he2, if_neg Bool.false_ne_true, if_neg (by omega)]
        have := zr_rstart_mono (show P.i + m + 2 ≤ P.i + (P.s - P.b).toNat + 1 by omega)
        have : 2 ^ (P.i + m) ≤ 2 ^ (P.i + (P.s - P.b).toNat - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have : ((2 ^ (P.i + m) : ℕ) : ℤ) ≤ ((2 ^ (P.i + (P.s - P.b).toNat - 1) : ℕ) : ℤ) := by
          exact_mod_cast this
        omega
  · refine ⟨?_, ?_⟩
    · show P.b - 2 ≤ Q.s - 2
      rw [h5]
      omega
    · show Q.s + 8 * (zr_hh (zr_popG Q) : ℤ) + 1 ≤
        P.s + 8 * ((2 ^ (P.i + (P.s - P.b).toNat) : ℕ) : ℤ) + 1
      rw [hh, h5]
      omega

/-- **The ascending right pass**, as a pinned segment on its loop: from the anchor at right field
`P.i`'s start, one round per count mark pops it, steps one right field out and runs the guarded
inward shift at that field's level; on the empty stack it stops. -/
private noncomputable def zr_p3Pass {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_passSeg (zr_p3Back t) (zr_p3Body t x) (zr_p3Body_none t x) (zr_p3Body_hX t x)
    (zr_p3Body_step t x) (zr_p3Body_back t x)
    (fun _ hV hp => zr_pop_next_valid t _ (by omega) hV hp)
    (sa := .inr (.inr (.inl (.inr (some false))))) (sb := .inl (.inr (some false)))
    (by
      show zr_oneBack (some false) false (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (by
      show zr_oneBack (some false) true (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (fun P => (P.s - P.b).toNat)
    (fun P hV => by
      have := hV.1.2.1
      show zr_popE ((zr_p3Nxt t)^[(P.s - P.b).toNat] P) = true
      rw [zr_pop_pop t _ (by omega) hV _ (by omega)]
      exact decide_eq_true (by omega))
    (fun P hV m hm => by
      have := hV.1.2.1
      have hm' : m < (P.s - P.b).toNat := hm
      rw [zr_pop_pop t _ (by omega) hV _ (by omega)]
      exact decide_eq_false (by omega))
    zr_p3Lo zr_p3Hi (fun P hV m hm => zr_p3_round_box t hV m hm) zr_p3_anchor

/-- The left layout's home is at cell `0`. -/
private lemma zr_lstart_zero : zr_lstart 0 = 0 := by
  rw [zr_lstart, zr_rstart, if_pos rfl]
  norm_num

/-- The descending left pass's round box, its lower corner. -/
private abbrev zr_p2L {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i - 2) P.s

/-- The descending left pass's round box, its upper corner. -/
private abbrev zr_p2U {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (P.i - 1 - 1) + zr_hh (zr_p1G P) + 1) (P.s + 6 * zr_hh (zr_p1G P) + 4)

/-- The layout facts behind the descending left pass's round box. -/
private lemma zr_p2_facts {k : ℕ} {P : zr_Px k} (hV : zr_p1V P) :
    zr_lstart P.i ≤ zr_lstart (P.i - 1) ∧ zr_lstart (P.i - 1) ≤ zr_lstart (P.i - 1 - 1) ∧
      zr_lstart (P.i - 1) = zr_lstart P.i + ((2 ^ P.i : ℕ) : ℤ) + 1 ∧
      (0 : ℤ) < ((2 ^ P.i : ℕ) : ℤ) := by
  have := hV.2
  have hs := zr_lstart_succ (P.i - 1)
  rw [show P.i - 1 + 1 = P.i by omega] at hs
  exact ⟨zr_lstart_anti (by omega), zr_lstart_anti (by omega), hs,
    by exact_mod_cast Nat.two_pow_pos _⟩

/-- **The left inward skip**: skip over left field `P.i` to the next field inward's outermost
cell. -/
private def zr_lsSeg {k : ℕ} (x : List (ZoneSym k)) (V : zr_Px k → Prop)
    (hV : ∀ P, V P → zr_pxV P ∧ 1 ≤ P.i) :=
  show zr_PinSeg x _ _ _ V zr_pT zr_pT zr_lH (fun P => zr_heads (zr_lstart (P.i - 1)) P.s) _ zr_lH
      (fun P => zr_heads (zr_lstart (P.i - 1)) P.s) from
  zr_seg (zr_pinSkip_step (x := x) V 0 (fun P => zr_lfield P.D.2 P.i) zr_pT zr_lH
      fun P hP q h1 h2 => by
        have := (hV P hP).1.1
        show zonedTape P.D.2 (zr_lstart P.i + q) = _
        exact zr_lfield_at P.D.2 P.i (by omega) _ rfl q (by omega) h2)
    (fun _ _ => rfl) fun P hP => by
      have := (hV P hP).1.1
      have := (hV P hP).2
      have hl := zr_lfield_length P.D.2 P.i (by omega)
      have hs := zr_lstart_succ (P.i - 1)
      rw [show P.i - 1 + 1 = P.i by omega] at hs
      have hp : Function.update (zr_heads (zr_lstart P.i) P.s) 0
          (zr_lstart P.i + ((zr_lfield P.D.2 P.i).length : ℤ) + 1) =
            zr_heads (zr_lstart (P.i - 1)) P.s := by
        rw [zr_heads_set0, hl, ← hs]
      exact ⟨hp, fun _ => le_rfl, fun i => by
        show Function.update (zr_heads (zr_lstart P.i) P.s) 0
          (zr_lstart P.i + ((zr_lfield P.D.2 P.i).length : ℤ) + 1) i ≤ _
        rw [hp]⟩

/-- The descending left pass's lead: skip over left field `P.i` to the next field inward, then
push a count mark. -/
private def zr_p2Lead {k : ℕ} (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_p1V zr_pT (fun P => zr_aT (zr_p1G P)) zr_lH
      (fun P => zr_lA (zr_p1G P)) _ zr_p2L zr_p2U from
  zr_segSeq (zr_seg (zr_lsSeg x zr_p1V fun _ h => h).step (fun _ _ => rfl) fun P hV => by
        obtain ⟨h1, h2, -, -⟩ := zr_p2_facts hV
        exact ⟨rfl, zr_heads_le (show zr_lstart P.i - 2 ≤ zr_lstart P.i by omega) le_rfl,
          zr_heads_le (show zr_lstart (P.i - 1) ≤
            zr_lstart (P.i - 1 - 1) + (zr_hh (zr_p1G P) : ℤ) + 1 by omega)
            (show P.s ≤ P.s + 6 * (zr_hh (zr_p1G P) : ℤ) + 4 by omega)⟩)
    (zr_seg (zr_pinCell_step (x := x) zr_p1V 1 1 (some (some (.inl false))) zr_pT
        fun P => zr_heads (zr_lstart (P.i - 1)) P.s)
      (T₂' := fun P => zr_aT (zr_p1G P)) (p₂' := fun P => zr_lA (zr_p1G P)) (L' := zr_p2L)
      (U' := zr_p2U) (fun P hV => by
        show Function.update (zr_pT P) 1 (Function.update (zr_pT P 1) P.s _) = _
        rw [zr_tapes_write, zr_stk_push _ hV.1.2.1]) fun P hV => by
        obtain ⟨h1, h2, hs, -⟩ := zr_p2_facts hV
        refine ⟨?_, fun i => ?_, fun i => ?_⟩
        · show Function.update (zr_heads (zr_lstart (P.i - 1)) P.s) 1
            (P.s + ((1 : SignType) : ℤ)) = _
          rw [zr_heads_set1, SignType.coe_one]
        · show zr_p2L P i ≤ min (zr_heads (zr_lstart (P.i - 1)) P.s i)
            (Function.update (zr_heads (zr_lstart (P.i - 1)) P.s) 1 (P.s + ((1 : SignType) : ℤ)) i)
          rw [zr_heads_set1, SignType.coe_one]
          revert i
          exact zr_heads_le (show zr_lstart P.i - 2 ≤ min (zr_lstart (P.i - 1))
            (zr_lstart (P.i - 1)) by omega) (show P.s ≤ min P.s (P.s + 1) by omega)
        · show max (zr_heads (zr_lstart (P.i - 1)) P.s i)
            (Function.update (zr_heads (zr_lstart (P.i - 1)) P.s) 1
              (P.s + ((1 : SignType) : ℤ)) i) ≤ zr_p2U P i
          rw [zr_heads_set1, SignType.coe_one]
          revert i
          exact zr_heads_le (show max (zr_lstart (P.i - 1)) (zr_lstart (P.i - 1)) ≤
            zr_lstart (P.i - 1 - 1) + (zr_hh (zr_p1G P) : ℤ) + 1 by omega)
            (show max P.s (P.s + 1) ≤ P.s + 6 * (zr_hh (zr_p1G P) : ℤ) + 4 by omega))

/-- The descending left pass's home test verdict, one cell after left field `P.i - 1`'s outermost
cell. -/
private abbrev zr_p2Home {k : ℕ} (P : zr_Px k) : Bool := zr_dnHome zr_lA P

/-- The descending left pass's guard: a descending index away from the home. -/
private abbrev zr_p2On {k : ℕ} (P : zr_Px k) : Prop := zr_p1V P ∧ zr_p2Home P = false

/-- The home test's verdict is whether left field `P.i - 1` is the home. -/
private lemma zr_p2Home_eq {k : ℕ} {P : zr_Px k} (hV : zr_pxV P) :
    zr_p2Home P = decide (P.i - 1 = 0) :=
  zr_home_eq zr_lstart (zr_lhome_iff _) (Nat.sub_le _ _) hV

/-- **The descending left pass's next index**: left field `P.i - 1`, whose level is shifted
outward (the identity at the home), one count mark pushed. -/
private abbrev zr_p2Nxt {k : ℕ} (t : Fin k) : zr_Px k → zr_Px k :=
  zr_dnF t fun _ i w => zoneShiftOut false (i - 1) w

/-- Past the home, the descending left pass's shift index meets the shift's requirements. -/
private lemma zr_p2G_pre {k : ℕ} {P : zr_Px k} (h : zr_p1V P ∧ zr_p2Home P = false) :
    zr_shPre (zr_p1G P) :=
  zr_dnG_pre h (zr_p2Home_eq h.1.1)

/-- The descending left pass's guarded shift, in the round box. -/
private lemma zr_p2Grd_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_grdOut t x zr_p1G (fun P => zr_p1V P ∧ zr_p2Home P = false)
        fun _ h => zr_p2G_pre h) (fun P => zr_p1V P ∧ zr_p2Home P = false)
      (fun P => zr_aT (zr_p1G P)) (fun P => zr_pT (zr_p2Nxt t P)) (fun P => zr_lA (zr_p1G P))
      (fun P => zr_lH (zr_p2Nxt t P))
      (fun P => 1 + 1 + if zr_out1Off t (zr_p1G P) then 0 else
        11 * zr_hh (zr_p1G P) + 20 + 1 + (1 + 1 + if zr_out2Off t (zr_p1G P) then
          6 * zr_hh (zr_p1G P) + 11 else
          6 * zr_hh (zr_p1G P) + 11 + 1 + (76 * zr_hh (zr_p1G P) + 107))) zr_p2L zr_p2U :=
  zr_PinStep_congr (zr_grdOut_step t x _ _ _) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun P hP => by
      have h1 := (zr_p2G_pre hP).1
      have hh : P.i - 1 + 1 = P.i := by
        have : 1 ≤ P.i - 1 := h1
        omega
      show ∀ i, zr_p2L P i ≤ zr_heads (zr_lstart (P.i - 1 + 1) - 2) (P.s + 1 - 1) i
      rw [hh]
      exact zr_heads_le le_rfl (show P.s ≤ P.s + 1 - 1 by omega))
    fun P hP => zr_heads_le le_rfl (show P.s + 1 + 6 * (zr_hh (zr_p1G P) : ℤ) + 3 ≤
      P.s + 6 * (zr_hh (zr_p1G P) : ℤ) + 4 by omega)

/-- The descending left pass's home test, a peek one cell right, in the round box. -/
private lemma zr_p2Peek_step {k : ℕ} (x : List (ZoneSym k)) :
    zr_PinStep (zr_pinPeekContract x zr_p1V 0 1 Option.isNone (fun P => zr_aT (zr_p1G P))
        fun P => zr_lA (zr_p1G P)) zr_p1V (fun P => zr_aT (zr_p1G P))
      (fun P => zr_aT (zr_p1G P)) (fun P => zr_lA (zr_p1G P)) (fun P => zr_lA (zr_p1G P))
      (fun _ => 3) zr_p2L zr_p2U :=
  zr_PinStep_congr (zr_pinPeek_step _ 0 1 Option.isNone _ _) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun P hV i => by
      have := zr_p2_facts hV
      fin_cases i
      · show zr_lstart P.i - 2 ≤ zr_lstart (P.i - 1) - 1
        omega
      · show P.s ≤ P.s + 1 - 1
        omega)
    (fun P hV i => by
      have := zr_p2_facts hV
      fin_cases i
      · show zr_lstart (P.i - 1) + 1 ≤ zr_lstart (P.i - 1 - 1) + (zr_hh (zr_p1G P) : ℤ) + 1
        omega
      · show P.s + 1 + 1 ≤ P.s + 6 * (zr_hh (zr_p1G P) : ℤ) + 4
        omega)

/-- **The descending left pass's branch**: at the home stop; otherwise run the guarded outward
shift. -/
private def zr_p2Br {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_peekBranch (zr_p2Peek_step x) (zr_p2Grd_step t x) fun _ => rfl

/-- The descending left pass's branch is a pinned step to the next index's anchor pin. -/
private lemma zr_p2Br_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p2Br t x) zr_p1V (fun P => zr_aT (zr_p1G P)) (fun P => zr_pT (zr_p2Nxt t P))
      (fun P => zr_lA (zr_p1G P)) (fun P => zr_lH (zr_p2Nxt t P))
      (fun P => 3 + 1 + if zr_p2Home P then 0 else
        1 + 1 + if zr_out1Off t (zr_p1G P) then 0 else
          11 * zr_hh (zr_p1G P) + 20 + 1 + (1 + 1 + if zr_out2Off t (zr_p1G P) then
            6 * zr_hh (zr_p1G P) + 11 else
            6 * zr_hh (zr_p1G P) + 11 + 1 + (76 * zr_hh (zr_p1G P) + 107))) zr_p2L zr_p2U :=
  zr_peekBranch_step _ _ _ (fun P hV hh => by
      rw [zr_p2Home_eq hV.1, decide_eq_true_iff] at hh
      refine ⟨?_, rfl⟩
      show zr_tapes (zonedTape (Function.update P.D.2 t (zoneShiftOut false (P.i - 1) (P.D.2 t))))
        _ = _
      rw [hh, zr_shiftOut_zero, Function.update_eq_self]) fun P hV i => by
    have := zr_p2_facts hV
    fin_cases i
    · exact ⟨show zr_lstart P.i - 2 ≤ zr_lstart (P.i - 1) by omega,
        show zr_lstart (P.i - 1) ≤ zr_lstart (P.i - 1 - 1) + (zr_hh (zr_p1G P) : ℤ) + 1 by omega⟩
    · exact ⟨show P.s ≤ P.s + 1 by omega,
        show P.s + 1 ≤ P.s + 6 * (zr_hh (zr_p1G P) : ℤ) + 4 by omega⟩

/-- **The descending left pass's round body**: skip over a left field inward and push a count
mark, then stop at the home or run the guarded outward shift at that field's level. -/
private def zr_p2Body {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  (zr_p2Lead x).C.seq (zr_p2Br t x) (fun P => P)
    (zr_pin_hlink (zr_p2Lead x).step (zr_p2Br_step t x))

/-- The descending left pass's round time. -/
private abbrev zr_p2Tau {k : ℕ} (t : Fin k) (P : zr_Px k) : ℕ :=
  (zr_lfield P.D.2 P.i).length + 1 + 1 + 1 + 1 +
    (3 + 1 + if zr_p2Home P then 0 else
      1 + 1 + if zr_out1Off t (zr_p1G P) then 0 else
        11 * zr_hh (zr_p1G P) + 20 + 1 + (1 + 1 + if zr_out2Off t (zr_p1G P) then
          6 * zr_hh (zr_p1G P) + 11 else
          6 * zr_hh (zr_p1G P) + 11 + 1 + (76 * zr_hh (zr_p1G P) + 107)))

/-- **The descending left pass's round** is a pinned step from the anchor to the next index's
anchor. -/
private lemma zr_p2Body_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_p2Body t x) zr_p1V zr_pT (fun P => zr_pT (zr_p2Nxt t P)) zr_lH
      (fun P => zr_lH (zr_p2Nxt t P))
      (zr_p2Tau t) zr_p2L zr_p2U :=
  zr_PinStep_seq' (zr_p2Lead x).step (zr_p2Br_step t x) _

/-- The descending left pass's way back: the home exit escapes, the guarded shift's exits return
to the anchor. -/
private noncomputable def zr_p2Back {k : ℕ} (t : Fin k) :
    zr_stOf (zr_p2Body t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_seqBack (zr_branchBack (zr_oneBack (some false) true) (zr_grdOutBack t))

/-- The descending left pass's round escapes exactly at the home. -/
private lemma zr_p2Body_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_p2Body t x) (zr_p2Back t) zr_p2Home :=
  zr_BackIs_seq (zr_BackIs_congr (zr_peekBranch_back _ _ _ (zr_grdOut_back t x _ _ _) true)
    fun P => by cases zr_p2Home P <;> rfl)

/-- The descending left pass's round's exits are its way back's domain. -/
private lemma zr_p2Body_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_p2Body t x) ↔ zr_p2Back t s ≠ none :=
  zr_seqBack_hX (zr_branchBack_hX (zr_oneBack_hX _ _) (zr_grdOut_hX t x zr_p1G
    (fun P => zr_p1V P ∧ zr_p2Home P = false) fun _ h => zr_p2G_pre h))

/-- The descending left pass's round never halts. -/
private lemma zr_p2Body_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_p2Body t x) :=
  zr_none_dn (zr_grdOut_none t x zr_p1G zr_p2On fun _ => zr_p2G_pre)

/-- Round `m` of the descending left pass is at the home exactly when it is the last. -/
private lemma zr_p2_home {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_p1V P) (m : ℕ)
    (hm : m < P.i) : zr_p2Home ((zr_p2Nxt t)^[m] P) = decide (P.i - m - 1 = 0) := by
  rw [zr_p2Home_eq (zr_dn_valid t _ hV m hm).1, (zr_dn_iter t _ P m).2.1]

/-- The descending left pass's head box: the zoned head from two cells past the start's field to
just right of the home, scratch over the marks and the shifts' work areas. -/
private abbrev zr_p2Lo {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i - 2) P.s

/-- The descending left pass's head box, its upper corner. -/
private abbrev zr_p2Hi {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads 2 (P.s + P.i + 6 * ((2 ^ P.i : ℕ) : ℤ) + 4)

/-- Each round's box lies in the descending left pass's box. -/
private lemma zr_p2_round_box {k : ℕ} (t : Fin k) {P : zr_Px k} (m : ℕ) (hm : m < P.i) :
    ∀ i, zr_p2Lo P i ≤ zr_p2L ((zr_p2Nxt t)^[m] P) i ∧
      zr_p2U ((zr_p2Nxt t)^[m] P) i ≤ zr_p2Hi P i := by
  obtain ⟨-, h2, -, -, h5⟩ := zr_dn_iter t (fun _ i w => zoneShiftOut false (i - 1) w) P m
  set Q := (zr_p2Nxt t)^[m] P with hQ
  have ha := zr_lstart_anti (show Q.i ≤ P.i by rw [h2]; omega)
  have hpa := zr_lstart_pow_anti (Nat.zero_le (Q.i - 1 - 1))
  rw [zr_lstart_zero] at hpa
  have hh : zr_hh (zr_p1G Q) ≤ 2 ^ P.i := by
    show 2 ^ (Q.i - 1 - 1) ≤ 2 ^ P.i
    exact Nat.pow_le_pow_right (by norm_num) (by rw [h2]; omega)
  have hh' : (zr_hh (zr_p1G Q) : ℤ) ≤ ((2 ^ P.i : ℕ) : ℤ) := by exact_mod_cast hh
  have hmi : (m : ℤ) ≤ P.i := by exact_mod_cast hm.le
  intro i
  fin_cases i
  · exact ⟨show zr_lstart P.i - 2 ≤ zr_lstart Q.i - 2 by omega,
      show zr_lstart (Q.i - 1 - 1) + (zr_hh (zr_p1G Q) : ℤ) + 1 ≤ 2 by
        have : zr_hh (zr_p1G Q) = 2 ^ (Q.i - 1 - 1) := rfl
        rw [this]
        norm_num at hpa ⊢
        omega⟩
  · exact ⟨show P.s ≤ Q.s by rw [h5]; omega,
      show Q.s + 6 * (zr_hh (zr_p1G Q) : ℤ) + 4 ≤ P.s + P.i + 6 * ((2 ^ P.i : ℕ) : ℤ) + 4 by
        rw [h5]
        omega⟩

/-- An anchor lies in the descending left pass's round box. -/
private lemma zr_p2_anchor {k : ℕ} (P : zr_Px k) :
    ∀ i, zr_p2L P i ≤ zr_lH P i ∧ zr_lH P i ≤ zr_p2U P i := by
  have := zr_lstart_anti (show P.i - 1 - 1 ≤ P.i by omega)
  intro i
  fin_cases i
  · exact ⟨show zr_lstart P.i - 2 ≤ zr_lstart P.i by omega,
      show zr_lstart P.i ≤ zr_lstart (P.i - 1 - 1) + (zr_hh (zr_p1G P) : ℤ) + 1 by omega⟩
  · exact ⟨le_refl P.s, show P.s ≤ P.s + 6 * (zr_hh (zr_p1G P) : ℤ) + 4 by omega⟩

/-- **The descending left pass**, as a pinned segment on its loop: from the anchor at left field
`P.i`'s outermost cell, `P.i` rounds shift track `t` outward at levels `P.i - 1, …, 1` (the last
round, at the home, shifts nothing), push `P.i` count marks, and stop at the home. -/
private noncomputable def zr_p2Pass {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_passSeg (zr_p2Back t) (zr_p2Body t x) (zr_p2Body_none t x) (zr_p2Body_hX t x)
    (zr_p2Body_step t x) (zr_p2Body_back t x)
    (fun P hV hh => by
      rw [zr_p2Home_eq hV.1, decide_eq_false_iff_not] at hh
      exact zr_dn_valid t (fun _ i w => zoneShiftOut false (i - 1) w) hV 1 (by omega))
    (sa := .inr (.inr (.inl (.inr (some false))))) (sb := .inr (.inl (.inr (some false))))
    (by
      show zr_oneBack (some false) false (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (by
      show zr_oneBack (some false) true (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (fun P => P.i - 1)
    (fun P hV => by
      have := hV.2
      show zr_p2Home ((zr_p2Nxt t)^[P.i - 1] P) = true
      rw [zr_p2_home t hV _ (by omega)]
      exact decide_eq_true (by omega))
    (fun P hV m hm => by
      have hm' : m < P.i - 1 := hm
      rw [zr_p2_home t hV _ (by omega)]
      exact decide_eq_false (by omega))
    zr_p2Lo zr_p2Hi (fun P hV m hm => by
      have := hV.2
      have hm' : m ≤ P.i - 1 := hm
      exact zr_p2_round_box t m (by omega))
    zr_p2_anchor

/-- The right return's home verdict, one cell after the anchor's field start. -/
private abbrev zr_rbHome {k : ℕ} (P : zr_Px k) : Bool :=
  Option.isNone (zr_pT P 0 (zr_rstart P.i + ((1 : SignType) : ℤ)))

/-- The right return's verdict is whether the anchor is the home. -/
private lemma zr_rbHome_eq {k : ℕ} {P : zr_Px k} (hV : zr_pxV P) :
    zr_rbHome P = decide (P.i = 0) :=
  zr_home_eq zr_rstart (zr_rhome_iff _) le_rfl hV

/-- Away from the home, a right return's index meets the descending lead's requirements. -/
private lemma zr_rb_lead {k : ℕ} {P : zr_Px k} (h : zr_pxV P ∧ zr_rbHome P = false) :
    zr_p1V P := by
  obtain ⟨hV, hh⟩ := h
  rw [zr_rbHome_eq hV, decide_eq_false_iff_not] at hh
  exact ⟨hV, by omega⟩

/-- **The right return's next index**: one right field in and one mark pushed, unless at the
home. -/
private abbrev zr_rbNxt {k : ℕ} (t : Fin k) : zr_Px k → zr_Px k :=
  zr_cNxt (fun P => P.i = 0) (zr_dnF t fun _ _ w => w)

/-- The right return's round box, its lower corner. -/
private abbrev zr_rbL {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if zr_rbHome P then zr_rstart P.i - 1 else zr_rstart (P.i - 1 - 1) - 1) (P.s - 1)

/-- The right return's round box, its upper corner. -/
private abbrev zr_rbU {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if zr_rbHome P then zr_rstart P.i + 1 else zr_rstart P.i + 4 * zr_hh (zr_p1G P))
    (P.s + 8 * zr_hh (zr_p1G P) + 3)

/-- The right return's arm: the descending right lead, from the anchor to the next index's
anchor, in the round box. -/
private lemma zr_rbArm_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_segRe (zr_p1Lead x) (fun P => P) (fun P => zr_pxV P ∧ zr_rbHome P = false)
        fun _ h => zr_rb_lead h).C (fun P => zr_pxV P ∧ zr_rbHome P = false) zr_pT
      (fun P => zr_pT (zr_rbNxt t P)) zr_rH (fun P => zr_rH (zr_rbNxt t P))
      (fun P => (zr_rfield P.D.2 (P.i - 1)).length + 3 + 1 + 1) zr_rbL zr_rbU := by
  refine zr_PinStep_congr (zr_segRe (zr_p1Lead x) _ _ _).step (fun P hP => ?_) (fun P hP => ?_)
    (fun _ _ => rfl) (fun P hP i => ?_) (fun P hP i => ?_)
  · have hi := (zr_rb_lead hP).2
    show _ = zr_pT (if P.i = 0 then P else _)
    rw [if_neg (by omega)]
    show _ = zr_tapes (zonedTape (Function.update P.D.2 t (P.D.2 t))) (zr_stk P.β P.b (P.s + 1))
    rw [Function.update_eq_self]
  · have hi := (zr_rb_lead hP).2
    show _ = zr_rH (if P.i = 0 then P else _)
    rw [if_neg (by omega)]
  · fin_cases i
    · show (if zr_rbHome P then zr_rstart P.i - 1 else zr_rstart (P.i - 1 - 1) - 1) ≤
        zr_rstart (P.i - 1 - 1) - 1
      rw [hP.2, if_neg Bool.false_ne_true]
    · show P.s - 1 ≤ P.s
      omega
  · fin_cases i
    · show (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) ≤
        (if zr_rbHome P then zr_rstart P.i + 1 else zr_rstart P.i + 4 * zr_hh (zr_p1G P))
      rw [hP.2, if_neg Bool.false_ne_true]
      split_ifs <;> omega
    · exact le_refl _

/-- **The right return's round body**: at the home stop; otherwise skip back over a field and
push a count mark. -/
private def zr_rbBody {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_peekRound x zr_pxV 0 1 zr_rbHome (fun P => zr_rstart P.i) (fun _ => rfl) zr_rbL zr_rbU
    (fun P _ i => by
      have := zr_rstart_mono (show P.i - 1 - 1 ≤ P.i by omega)
      fin_cases i
      · show (if zr_rbHome P then zr_rstart P.i - 1 else zr_rstart (P.i - 1 - 1) - 1) ≤
          zr_rstart P.i - 1
        split_ifs <;> omega
      · exact le_refl (P.s - 1))
    (fun P _ i => by
      have : 0 < zr_hh (zr_p1G P) := Nat.two_pow_pos _
      fin_cases i
      · show zr_rstart P.i + 1 ≤
          (if zr_rbHome P then zr_rstart P.i + 1 else zr_rstart P.i + 4 * zr_hh (zr_p1G P))
        split_ifs <;> omega
      · show P.s + 1 ≤ P.s + 8 * zr_hh (zr_p1G P) + 3
        omega) (zr_rbArm_step t x)

/-- The right return's round time. -/
private abbrev zr_rbTau {k : ℕ} (P : zr_Px k) : ℕ :=
  3 + 1 + if zr_rbHome P then 0 else (zr_rfield P.D.2 (P.i - 1)).length + 3 + 1 + 1

/-- **The right return's round** is a pinned step from the anchor to the next index's
anchor. -/
private lemma zr_rbBody_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_rbBody t x) zr_pxV zr_pT (fun P => zr_pT (zr_rbNxt t P)) zr_rH
      (fun P => zr_rH (zr_rbNxt t P))
      zr_rbTau zr_rbL zr_rbU :=
  zr_peekRound_step _ _ _ _ _ _ _ _ _ _ _ _ fun _ hV hh =>
    zr_homeEsc _ zr_rH hh (zr_rbHome_eq hV)

/-- The right return's way back: the home escapes, the lead returns to the anchor. -/
private noncomputable def zr_rbBack {k : ℕ} (t : Fin k) :
    zr_stOf (zr_rbBody t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_brBack true (zr_exitOf (zr_p1Lead ([] : List (ZoneSym k))).C)

/-- The right return's round escapes exactly at the home. -/
private lemma zr_rbBody_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_rbBody t x) (zr_rbBack t) zr_rbHome :=
  zr_peekRound_back _ _ _ _ _ _ _ _ _ _ _ _ (zr_BackIs_one _ false)

/-- The right return's round's exits are its way back's domain. -/
private lemma zr_rbBody_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_rbBody t x) ↔ zr_rbBack t s ≠ none :=
  zr_branchBack_hX (zr_oneBack_hX _ _) (zr_oneBack_hX _ _)

/-- The right return's round never halts. -/
private lemma zr_rbBody_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_rbBody t x) :=
  zr_none_one

/-- Before the home, the right return's rounds are the descending ones. -/
private lemma zr_rb_iter {k : ℕ} (t : Fin k) (P : zr_Px k) (m : ℕ) (hm : m ≤ P.i) :
    (zr_rbNxt t)^[m] P = (zr_dnF t fun _ _ w => w)^[m] P :=
  zr_cNxt_iter _ _ P m fun r hr => by
    rw [(zr_dn_iter t _ P r).2.1]
    omega

/-- The right return stays valid. -/
private lemma zr_rb_valid {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_pxV P) (m : ℕ) :
    zr_pxV ((zr_dnF t fun _ _ w => w)^[m] P) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := zr_dn_iter t (fun _ _ w => w) P m
  obtain ⟨hi, hbs, hβ⟩ := hV
  refine ⟨by rw [h2, h1]; omega, by rw [h4, h5]; omega, fun r hr => ?_⟩
  rw [h3]
  exact hβ r (by rw [h4] at hr; exact hr)

/-- Round `m` of the right return is at the home exactly when it is the last. -/
private lemma zr_rb_home {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_pxV P) (m : ℕ)
    (hm : m ≤ P.i) : zr_rbHome ((zr_rbNxt t)^[m] P) = decide (P.i - m = 0) := by
  rw [zr_rb_iter t P m hm, zr_rbHome_eq (zr_rb_valid t hV m), (zr_dn_iter t _ P m).2.1]

/-- The right return's head box: the zoned head from one cell left of the home to the start's
lead reach, scratch over the marks. -/
private abbrev zr_rbLo {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (-1) (P.s - 1)

/-- The right return's head box, its upper corner. -/
private abbrev zr_rbHi {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (if P.i = 0 then 1 else zr_rstart P.i + 4 * ((2 ^ (P.i - 1 - 1) : ℕ) : ℤ))
    (P.s + P.i + 8 * ((2 ^ P.i : ℕ) : ℤ) + 3)

/-- Each round's box lies in the right return's box. -/
private lemma zr_rb_round_box {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_pxV P) (m : ℕ)
    (hm : m ≤ P.i) :
    ∀ i, zr_rbLo P i ≤ zr_rbL ((zr_rbNxt t)^[m] P) i ∧
      zr_rbU ((zr_rbNxt t)^[m] P) i ≤ zr_rbHi P i := by
  have hh := zr_rb_home t hV m hm
  rw [zr_rb_iter t P m hm] at hh ⊢
  obtain ⟨-, h2, -, -, h5⟩ := zr_dn_iter t (fun _ _ w => w) P m
  set Q := (zr_dnF t fun _ _ w => w)^[m] P with hQ
  have hr0 : 0 ≤ zr_rstart (Q.i - 1 - 1) := by
    have := zr_rstart_mono (Nat.zero_le (Q.i - 1 - 1))
    rwa [zr_rstart, if_pos rfl] at this
  have hr0' : 0 ≤ zr_rstart Q.i := by
    have := zr_rstart_mono (Nat.zero_le Q.i)
    rwa [zr_rstart, if_pos rfl] at this
  have hpw : zr_hh (zr_p1G Q) ≤ 2 ^ P.i := by
    show 2 ^ (Q.i - 1 - 1) ≤ 2 ^ P.i
    exact Nat.pow_le_pow_right (by norm_num) (by rw [h2]; omega)
  have hpw' : (zr_hh (zr_p1G Q) : ℤ) ≤ ((2 ^ P.i : ℕ) : ℤ) := by exact_mod_cast hpw
  have hmi : (m : ℤ) ≤ P.i := by exact_mod_cast hm
  intro i
  fin_cases i
  · refine ⟨?_, ?_⟩
    · show (-1 : ℤ) ≤
        (if zr_rbHome Q then zr_rstart Q.i - 1 else zr_rstart (Q.i - 1 - 1) - 1)
      split_ifs <;> omega
    · show (if zr_rbHome Q then zr_rstart Q.i + 1 else zr_rstart Q.i + 4 * zr_hh (zr_p1G Q)) ≤
        (if P.i = 0 then 1 else zr_rstart P.i + 4 * ((2 ^ (P.i - 1 - 1) : ℕ) : ℤ))
      rw [hh]
      by_cases he : P.i - m = 0
      · rw [decide_eq_true he, if_pos rfl, h2, he]
        have : zr_rstart 0 = 0 := by rw [zr_rstart, if_pos rfl]
        rw [this]
        have : (0 : ℤ) ≤ ((2 ^ (P.i - 1 - 1) : ℕ) : ℤ) := by positivity
        split_ifs with h0
        · omega
        · have := zr_rstart_mono (show 1 ≤ P.i by omega)
          rw [show zr_rstart 1 = 2 by rw [zr_rstart, if_neg (by omega)]; norm_num [zoneStart_eq]]
            at this
          omega
      · rw [decide_eq_false he, if_neg Bool.false_ne_true, if_neg (by omega)]
        have := zr_rstart_mono (show Q.i ≤ P.i by rw [h2]; omega)
        have : zr_hh (zr_p1G Q) ≤ 2 ^ (P.i - 1 - 1) := by
          show 2 ^ (Q.i - 1 - 1) ≤ _
          exact Nat.pow_le_pow_right (by norm_num) (by rw [h2]; omega)
        have : (zr_hh (zr_p1G Q) : ℤ) ≤ ((2 ^ (P.i - 1 - 1) : ℕ) : ℤ) := by exact_mod_cast this
        omega
  · refine ⟨show P.s - 1 ≤ Q.s - 1 by rw [h5]; omega, ?_⟩
    show Q.s + 8 * (zr_hh (zr_p1G Q) : ℤ) + 3 ≤ P.s + P.i + 8 * ((2 ^ P.i : ℕ) : ℤ) + 3
    rw [h5]
    omega

/-- An anchor lies in the right return's round box. -/
private lemma zr_rb_anchor {k : ℕ} (P : zr_Px k) :
    ∀ i, zr_rbL P i ≤ zr_rH P i ∧ zr_rH P i ≤ zr_rbU P i := by
  have := zr_rstart_mono (show P.i - 1 - 1 ≤ P.i by omega)
  have : 0 < zr_hh (zr_p1G P) := Nat.two_pow_pos _
  intro i
  fin_cases i
  · constructor
    · show (if zr_rbHome P then zr_rstart P.i - 1 else zr_rstart (P.i - 1 - 1) - 1) ≤
        zr_rstart P.i
      split_ifs <;> omega
    · show zr_rstart P.i ≤
        (if zr_rbHome P then zr_rstart P.i + 1 else zr_rstart P.i + 4 * zr_hh (zr_p1G P))
      split_ifs <;> omega
  · exact ⟨show P.s - 1 ≤ P.s by omega, show P.s ≤ P.s + 8 * zr_hh (zr_p1G P) + 3 by omega⟩

/-- **The right return**, as a pinned segment on its loop: from the anchor at right field `P.i`'s
start, `P.i` rounds skip back to the home, pushing a count mark for each field crossed. -/
private noncomputable def zr_rbPass {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_passSeg (zr_rbBack t) (zr_rbBody t x) (zr_rbBody_none t x) (zr_rbBody_hX t x)
    (zr_rbBody_step t x) (zr_rbBody_back t x)
    (fun P hV hh => by
      rw [zr_rbHome_eq hV, decide_eq_false_iff_not] at hh
      show zr_pxV (if P.i = 0 then P else _)
      rw [if_neg hh]
      exact zr_rb_valid t hV 1)
    (sa := .inr (zr_exitOf (zr_p1Lead ([] : List (ZoneSym k))).C)) (sb := .inl (.inr (some false)))
    (by
      show zr_oneBack _ false _ = _
      rw [zr_oneBack, if_pos rfl])
    (by
      show zr_oneBack (some false) true (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (fun P => P.i)
    (fun P hV => by
      show zr_rbHome ((zr_rbNxt t)^[P.i] P) = true
      rw [zr_rb_home t hV _ le_rfl]
      exact decide_eq_true (by omega))
    (fun P hV m hm => by
      have hm' : m < P.i := hm
      rw [zr_rb_home t hV _ (by omega)]
      exact decide_eq_false (by omega))
    zr_rbLo zr_rbHi (fun P hV m hm => zr_rb_round_box t hV m hm) zr_rb_anchor

/-- The left return's home verdict, one cell after the anchor's outermost cell. -/
private abbrev zr_lbHome {k : ℕ} (P : zr_Px k) : Bool :=
  Option.isNone (zr_pT P 0 (zr_lstart P.i + ((1 : SignType) : ℤ)))

/-- The left return's verdict is whether the anchor is the home. -/
private lemma zr_lbHome_eq {k : ℕ} {P : zr_Px k} (hV : zr_pxV P) :
    zr_lbHome P = decide (P.i = 0) :=
  zr_home_eq zr_lstart (zr_lhome_iff _) le_rfl hV

/-- Away from the home, a left return's index meets the inward skip's requirements. -/
private lemma zr_lb_lead {k : ℕ} {P : zr_Px k} (h : zr_pxV P ∧ zr_lbHome P = false) :
    zr_pxV P ∧ 1 ≤ P.i := by
  obtain ⟨hV, hh⟩ := h
  rw [zr_lbHome_eq hV, decide_eq_false_iff_not] at hh
  exact ⟨hV, by omega⟩

/-- **The left return's next index**: one left field in, unless at the home. -/
private abbrev zr_lbNxt {k : ℕ} (t : Fin k) : zr_Px k → zr_Px k :=
  zr_cNxt (fun P => P.i = 0) (zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)

/-- The left return's round box, its lower corner. -/
private abbrev zr_lbL {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i - 1) (P.s - 1)

/-- The left return's round box, its upper corner. -/
private abbrev zr_lbU {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zr_lstart (P.i - 1) + 1) (P.s + 1)

/-- The left return's arm: the inward skip, from the anchor to the next index's anchor, in the
round box. -/
private lemma zr_lbArm_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_lsSeg x (fun P => zr_pxV P ∧ zr_lbHome P = false) fun _ h => zr_lb_lead h).C
      (fun P => zr_pxV P ∧ zr_lbHome P = false) zr_pT (fun P => zr_pT (zr_lbNxt t P)) zr_lH
      (fun P => zr_lH (zr_lbNxt t P)) (fun P => (zr_lfield P.D.2 P.i).length + 1) zr_lbL
      zr_lbU := by
  refine zr_PinStep_congr (zr_lsSeg x _ _).step (fun P hP => ?_) (fun P hP => ?_)
    (fun _ _ => rfl) (fun P hP i => ?_) (fun P hP i => ?_)
  · have hi := (zr_lb_lead hP).2
    show _ = zr_pT (if P.i = 0 then P else _)
    rw [if_neg (by omega)]
    show _ = zr_tapes (zonedTape (Function.update P.D.2 t (P.D.2 t))) (zr_stk P.β P.b (P.s + 0))
    rw [Function.update_eq_self, add_zero]
  · have hi := (zr_lb_lead hP).2
    show _ = zr_lH (if P.i = 0 then P else _)
    rw [if_neg (by omega)]
    show _ = zr_heads (zr_lstart (P.i - 1)) (P.s + 0)
    rw [add_zero]
  · fin_cases i
    · show zr_lstart P.i - 1 ≤ zr_lstart P.i
      omega
    · show P.s - 1 ≤ P.s
      omega
  · fin_cases i
    · show zr_lstart (P.i - 1) ≤ zr_lstart (P.i - 1) + 1
      omega
    · show P.s ≤ P.s + 1
      omega

/-- **The left return's round body**: at the home stop; otherwise skip over a left field
inward. -/
private def zr_lbBody {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_peekRound x zr_pxV 0 1 zr_lbHome (fun P => zr_lstart P.i) (fun _ => rfl) zr_lbL zr_lbU
    (fun P _ i => by fin_cases i <;> exact le_refl _)
    (fun P _ i => by
      have := zr_lstart_anti (show P.i - 1 ≤ P.i by omega)
      fin_cases i
      · show zr_lstart P.i + 1 ≤ zr_lstart (P.i - 1) + 1
        omega
      · exact le_refl (P.s + 1)) (zr_lbArm_step t x)

/-- The left return's round time. -/
private abbrev zr_lbTau {k : ℕ} (P : zr_Px k) : ℕ :=
  3 + 1 + if zr_lbHome P then 0 else (zr_lfield P.D.2 P.i).length + 1

/-- **The left return's round** is a pinned step from the anchor to the next index's anchor. -/
private lemma zr_lbBody_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_lbBody t x) zr_pxV zr_pT (fun P => zr_pT (zr_lbNxt t P)) zr_lH
      (fun P => zr_lH (zr_lbNxt t P))
      zr_lbTau zr_lbL zr_lbU :=
  zr_peekRound_step _ _ _ _ _ _ _ _ _ _ _ _ fun _ hV hh =>
    zr_homeEsc _ zr_lH hh (zr_lbHome_eq hV)

/-- The left return's way back: the home escapes, the skip returns to the anchor. -/
private noncomputable def zr_lbBack {k : ℕ} (t : Fin k) :
    zr_stOf (zr_lbBody t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_branchBack (zr_oneBack (some false) true)
    (zr_oneBack (zr_exitOf (zr_lsSeg ([] : List (ZoneSym k))
      (fun P => zr_pxV P ∧ zr_lbHome P = false) fun _ h => zr_lb_lead h).C) false)

/-- The left return's round escapes exactly at the home. -/
private lemma zr_lbBody_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_lbBody t x) (zr_lbBack t) zr_lbHome :=
  zr_peekRound_back _ _ _ _ _ _ _ _ _ _ _ _ (zr_BackIs_one _ false)

/-- The left return's round's exits are its way back's domain. -/
private lemma zr_lbBody_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_lbBody t x) ↔ zr_lbBack t s ≠ none :=
  zr_branchBack_hX (zr_oneBack_hX _ _) (zr_oneBack_hX _ _)

/-- The left return's round never halts. -/
private lemma zr_lbBody_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_lbBody t x) :=
  zr_none_one

/-- The left return after `m` rounds before the home: `m` fields in, scratch kept. -/
private lemma zr_lb_iter {k : ℕ} (t : Fin k) (P : zr_Px k) (m : ℕ) (hm : m ≤ P.i) :
    (zr_lbNxt t)^[m] P = (zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)^[m] P ∧
      ((zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)^[m] P).D.1 = P.D.1 ∧
      ((zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)^[m] P).i = P.i - m ∧
      ((zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)^[m] P).β = P.β ∧
      ((zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)^[m] P).b = P.b ∧
      ((zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)^[m] P).s = P.s := by
  have hit := zr_px_iter t (fun _ _ w => w) (fun i => i - 1) 0 P
  refine ⟨zr_cNxt_iter _ _ P m fun r hr => ?_, ?_⟩
  · rw [(hit r).2.1, zr_iterate_pred]
    omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hit m
    exact ⟨by rw [h1], by rw [h2, zr_iterate_pred], h3, h4, by rw [h5]; ring⟩

/-- Round `m` of the left return is at the home exactly when it is the last. -/
private lemma zr_lb_home {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_pxV P) (m : ℕ)
    (hm : m ≤ P.i) : zr_lbHome ((zr_lbNxt t)^[m] P) = decide (P.i - m = 0) := by
  obtain ⟨he, h1, h2, h3, h4, h5⟩ := zr_lb_iter t P m hm
  obtain ⟨hi, hbs, hβ⟩ := hV
  rw [he, zr_lbHome_eq ⟨by rw [h2, h1]; omega, by rw [h4, h5]; omega, fun r hr => by
    rw [h3]
    exact hβ r (by rw [h4] at hr; exact hr)⟩, h2]

/-- The left return's head box: the zoned head from one cell left of the start's field to just
right of the home. -/
private abbrev zr_lbLo {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads (zr_lstart P.i - 1) (P.s - 1)

/-- The left return's head box, its upper corner. -/
private abbrev zr_lbHi {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ := zr_heads 1 (P.s + 1)

/-- Each round's box lies in the left return's box. -/
private lemma zr_lb_round_box {k : ℕ} (t : Fin k) {P : zr_Px k} (m : ℕ) (hm : m ≤ P.i) :
    ∀ i, zr_lbLo P i ≤ zr_lbL ((zr_lbNxt t)^[m] P) i ∧
      zr_lbU ((zr_lbNxt t)^[m] P) i ≤ zr_lbHi P i := by
  obtain ⟨he, -, h2, -, -, h5⟩ := zr_lb_iter t P m hm
  rw [he]
  set Q := (zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 0)^[m] P with hQ
  have ha := zr_lstart_anti (show Q.i ≤ P.i by rw [h2]; omega)
  have hz := zr_lstart_anti (Nat.zero_le (Q.i - 1))
  rw [zr_lstart_zero] at hz
  intro i
  fin_cases i
  · exact ⟨show zr_lstart P.i - 1 ≤ zr_lstart Q.i - 1 by omega,
      show zr_lstart (Q.i - 1) + 1 ≤ 1 by omega⟩
  · exact ⟨show P.s - 1 ≤ Q.s - 1 by rw [h5], show Q.s + 1 ≤ P.s + 1 by rw [h5]⟩

/-- An anchor lies in the left return's round box. -/
private lemma zr_lb_anchor {k : ℕ} (P : zr_Px k) :
    ∀ i, zr_lbL P i ≤ zr_lH P i ∧ zr_lH P i ≤ zr_lbU P i := by
  have := zr_lstart_anti (show P.i - 1 ≤ P.i by omega)
  intro i
  fin_cases i
  · exact ⟨show zr_lstart P.i - 1 ≤ zr_lstart P.i by omega,
      show zr_lstart P.i ≤ zr_lstart (P.i - 1) + 1 by omega⟩
  · exact ⟨show P.s - 1 ≤ P.s by omega, show P.s ≤ P.s + 1 by omega⟩

/-- **The left return**, as a pinned segment on its loop: from the anchor at left field `P.i`'s
outermost cell, `P.i` rounds skip inward to the home. -/
private noncomputable def zr_lbPass {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_passSeg (zr_lbBack t) (zr_lbBody t x) (zr_lbBody_none t x) (zr_lbBody_hX t x)
    (zr_lbBody_step t x) (zr_lbBody_back t x)
    (fun P hV hh => by
      rw [zr_lbHome_eq hV, decide_eq_false_iff_not] at hh
      obtain ⟨-, -, h2, h3, h4, h5⟩ := zr_lb_iter t P 1 (by omega)
      obtain ⟨hi, hbs, hβ⟩ := hV
      show zr_pxV (if P.i = 0 then P else _)
      rw [if_neg hh]
      have h2' : P.i - 1 = P.i - 1 := rfl
      refine ⟨by
        show P.i - 1 ≤ P.D.1
        omega, by
        show P.b ≤ P.s + 0
        omega, fun r hr => hβ r hr⟩)
    (sa := .inr (zr_exitOf (zr_lsSeg ([] : List (ZoneSym k))
      (fun P => zr_pxV P ∧ zr_lbHome P = false) fun _ h => zr_lb_lead h).C))
    (sb := .inl (.inr (some false)))
    (by
      show zr_oneBack _ false _ = _
      rw [zr_oneBack, if_pos rfl])
    (by
      show zr_oneBack (some false) true (some false) = _
      rw [zr_oneBack, if_pos rfl])
    (fun P => P.i)
    (fun P hV => by
      show zr_lbHome ((zr_lbNxt t)^[P.i] P) = true
      rw [zr_lb_home t hV _ le_rfl]
      exact decide_eq_true (by omega))
    (fun P hV m hm => by
      have hm' : m < P.i := hm
      rw [zr_lb_home t hV _ (by omega)]
      exact decide_eq_false (by omega))
    zr_lbLo zr_lbHi (fun P _ m hm => zr_lb_round_box t m hm) zr_lb_anchor

/-- **The home move's validity**: a pass index with at least one level laid out. -/
private def zr_hmV {k : ℕ} (J : zr_Px k) : Prop := zr_pxV J ∧ 0 < J.D.1

/-- Left zone `0`'s track-`t` column, as scratch cells. -/
private abbrev zr_hmCL {k : ℕ} (t : Fin k) (J : zr_Px k) : List (ZoneSym k) :=
  zr_col t (zr_lfield J.D.2 1)

/-- Left zone `0`'s inner slot, as a scratch cell. -/
private abbrev zr_hmB {k : ℕ} (t : Fin k) (J : zr_Px k) : List (ZoneSym k) := (zr_hmCL t J).drop 1

/-- The home's track-`t` slot, as a scratch cell. -/
private abbrev zr_hmH {k : ℕ} (t : Fin k) (J : zr_Px k) : List (ZoneSym k) :=
  zr_col t (zr_rfield J.D.2 0)

/-- Right zone `0`'s track-`t` column, as scratch cells. -/
private abbrev zr_hmR {k : ℕ} (t : Fin k) (J : zr_Px k) : List (ZoneSym k) :=
  zr_col t (zr_rfield J.D.2 1)

/-- Right zone `0`'s outer slot, as a scratch cell. -/
private abbrev zr_hmE {k : ℕ} (t : Fin k) (J : zr_Px k) : List (ZoneSym k) := (zr_hmR t J).drop 1

/-- Right zone `0`'s inner slot, as a scratch cell. -/
private abbrev zr_hmC {k : ℕ} (t : Fin k) (J : zr_Px k) : List (ZoneSym k) := (zr_hmR t J).take 1

/-- The home move's layout facts: the fields around the home and their columns' pieces. -/
private lemma zr_hmLen {k : ℕ} (t : Fin k) {J : zr_Px k} (hV : zr_hmV J) :
    (zr_lfield J.D.2 1).length = 2 ∧ (zr_rfield J.D.2 1).length = 2 ∧
      (zr_rfield J.D.2 0).length = 1 ∧ zr_lstart 1 = -3 ∧ zr_rstart 1 = 2 ∧ zr_rstart 0 = 0 ∧
      (zr_hmCL t J).length = 2 ∧ (zr_hmB t J).length = 1 ∧ (zr_hmH t J).length = 1 ∧
      (zr_hmR t J).length = 2 ∧ (zr_hmE t J).length = 1 ∧ (zr_hmC t J).length = 1 ∧
      ([] : List (ZoneSym k)).length = 0 := by
  have h1 : 1 ≤ J.D.1 := hV.2
  have e1 := zr_lfield_length J.D.2 1 h1
  have e2 := zr_rfield_length J.D.2 1 h1
  have e3 := zr_rfield_length J.D.2 0 (Nat.zero_le _)
  have r1 : zr_rstart 1 = 2 := by
    rw [zr_rstart, if_neg (by omega)]
    norm_num [zoneStart_eq]
  have r0 : zr_rstart 0 = 0 := by rw [zr_rstart, if_pos rfl]
  have l1 : zr_lstart 1 = -3 := by
    rw [zr_lstart, r1]
    norm_num
  rw [pow_one] at e1 e2
  rw [pow_zero] at e3
  simp only [zr_hmCL, zr_hmB, zr_hmH, zr_hmR, zr_hmE, zr_hmC, zr_col, List.length_map,
    List.length_drop, List.length_take, List.length_nil, e1, e2, e3, l1, r1, r0]
  norm_num

/-- The home move's head box: the zoned head within four cells of home, scratch over its work
area. -/
private abbrev zr_hmL {k : ℕ} (J : zr_Px k) : Fin 2 → ℤ := zr_heads (-4) (J.s - 1)

/-- The home move's head box, its upper corner. -/
private abbrev zr_hmU {k : ℕ} (J : zr_Px k) : Fin 2 → ℤ := zr_heads 4 (J.s + 11)

/-- The home move's tape stages: tape `0`, and the scratch layout `L` over the count stack. -/
private abbrev zr_hmT {k : ℕ} (J : zr_Px k) (A : ℤ → Option (ZoneSym k))
    (L : List (List (ZoneSym k))) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes A (zr_scr (zr_pσ J) J.s L)

/-- Tape `0` after the new home's write: right zone `0`'s first slot, a blank virtual cell
when it is empty. -/
private abbrev zr_hmA1 {k : ℕ} (t : Fin k) (J : zr_Px k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (fun c v => zoneSlotSet t c (some (v.getD none)))
    (zr_hmC t J) (zonedTape J.D.2) 0

/-- Tape `0` after right zone `0`'s first slot is set to its second. -/
private abbrev zr_hmA2 {k : ℕ} (t : Fin k) (J : zr_Px k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (zoneSlotSet t) (zr_hmE t J) (zr_hmA1 t J) 2

/-- Tape `0` after right zone `0`'s second slot is cleared. -/
private abbrev zr_hmA3 {k : ℕ} (t : Fin k) (J : zr_Px k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (fun c _ => zoneSlotSet t c none) (zr_hmE t J) (zr_hmA2 t J) 3

/-- Tape `0` after left zone `0`'s first slot is set to the old home. -/
private abbrev zr_hmA4 {k : ℕ} (t : Fin k) (J : zr_Px k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (zoneSlotSet t) (zr_hmH t J) (zr_hmA3 t J) (-2)

/-- Tape `0` after the home move: left zone `0`'s second slot set to its first. -/
private abbrev zr_hmZ {k : ℕ} (t : Fin k) (J : zr_Px k) : ℤ → Option (ZoneSym k) :=
  zr_wr0 (zoneSlotOf t) (zoneSlotSet t) (zr_hmB t J) (zr_hmA4 t J) (-3)

/-- An empty last field of a scratch layout is no field. -/
private lemma zr_scr_nilLast {k : ℕ} (A σ : ℤ → Option (ZoneSym k)) (s : ℤ)
    (pre : List (List (ZoneSym k))) :
    zr_tapes A (zr_scr σ s (pre ++ [[]])) = zr_tapes A (zr_scr σ s pre) := by
  rw [← zr_scr_clear A σ s pre [] _ rfl]
  funext i q
  rw [if_neg fun h => by simp only [List.length_nil, Nat.cast_zero, add_zero] at h; omega]

/-- **A blank written on a field's last cell shortens it**, the last field of the layout. -/
private lemma zr_scr_splitLast {k : ℕ} (A σ : ℤ → Option (ZoneSym k)) (s b : ℤ)
    (pre : List (List (ZoneSym k))) (w : List (ZoneSym k)) (n : ℕ) (hn : w.length = n + 1)
    (hb : b = s + 1 + fieldOffset pre pre.length + n) :
    Function.update (zr_tapes A (zr_scr σ s (pre ++ [w]))) 1
        (Function.update (zr_tapes A (zr_scr σ s (pre ++ [w])) 1) b none) =
      zr_tapes A (zr_scr σ s (pre ++ [w.take n])) := by
  have h := zr_scr_split A σ s b pre [] w n (n + 1) (by omega) rfl hb
  simp only [List.append_nil] at h
  rw [h, List.drop_eq_nil_of_le (by omega),
    show pre ++ [w.take n, []] = (pre ++ [w.take n]) ++ [[]] by simp, zr_scr_nilLast]
/-- **The home move's gather**: lay out on scratch, as one-cell fields, left zone `0`'s inner
slot, the home and right zone `0`'s two slots, track `t`'s column. -/
private def zr_hmGat {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_hmV
      (fun J => zr_hmT J (zonedTape J.D.2) [])
      (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J])
      (fun J => zr_heads (-3) J.s)
      (fun J => zr_heads 2 (J.s + 9)) _ zr_hmL zr_hmU from
  -- step 1: scratch right, past the count
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2) [])
        (fun J => zr_heads (-3) J.s))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 2: copy left zone `0`'s column
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_lfield J.D.2 1)
        (fun J => zr_hmT J (zonedTape J.D.2) [])
        (fun J => zr_heads (-3) (J.s + 1))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          have := hV.2
          show (zonedTape J.D.2) (-3 + q) = _
          exact zr_lfield_at J.D.2 1 (by omega) _ (by omega) _ h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_copy _ _ _ _ [] _ _ _ _
          (by rw [List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 3: cut the column's outer slot
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (some none)
        (fun J => zr_hmT J (zonedTape J.D.2) [zr_hmCL t J])
        (fun J => zr_heads (-3) (J.s + 1)))
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_split _ _ _ _ [] [] (zr_hmCL t J) (0) (1)
          (by omega) (by omega)
          (by rw [zr_heads_one, List.length_nil, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 4: scratch right
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J])
        (fun J => zr_heads (-3) (J.s + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 5: scratch right, to the next field
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J])
        (fun J => zr_heads (-3) (J.s + 3)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 6: skip left zone `0`, to the home
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_lfield J.D.2 1)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J])
        (fun J => zr_heads (-3) (J.s + 4))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          have := hV.2
          show (zonedTape J.D.2) (-3 + q) = _
          exact zr_lfield_at J.D.2 1 (by omega) _ (by omega) _ (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 7: copy the home's column
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_rfield J.D.2 0)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J])
        (fun J => zr_heads 0 (J.s + 4))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          have := hV.2
          show (zonedTape J.D.2) (0 + q) = _
          exact zr_rfield_at J.D.2 0 (by omega) _ (by omega) _ h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_copy _ _ _ _ [[], zr_hmB t J] _ _ _ _
          (by rw [List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 8: skip the home, to right zone `0`
  zr_segSeq (zr_seg (zr_pinSkip_step _ 0 (fun J => zr_rfield J.D.2 0)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 0 (J.s + 4))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          have := hV.2
          show (zonedTape J.D.2) (0 + q) = _
          exact zr_rfield_at J.D.2 0 (by omega) _ (by omega) _ (by omega) h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 9: scratch right
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 2 (J.s + 4)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 10: scratch right, to the next field
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 2 (J.s + 5)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 11: copy right zone `0`'s column
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_rfield J.D.2 1)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 2 (J.s + 6))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          have := hV.2
          show (zonedTape J.D.2) (2 + q) = _
          exact zr_rfield_at J.D.2 1 (by omega) _ (by omega) _ h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_copy _ _ _ _ [[], zr_hmB t J, zr_hmH t J] _ _ _ _
          (by rw [List.length_cons, List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 12: cut the column's first slot
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (some none)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J, zr_hmR t J])
        (fun J => zr_heads 2 (J.s + 6)))
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_split _ _ _ _ [[], zr_hmB t J, zr_hmH t J] [] (zr_hmR t J) (0) (1)
          (by omega) (by omega)
          (by rw [zr_heads_one, List.length_cons, List.length_cons, List.length_singleton,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 13: scratch right
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 2 (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 14: scratch right, to the next field
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 2 (J.s + 8)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 15: copy right zone `0`'s column again
  zr_segSeq (zr_seg (zr_pinCopy_step _ 0 1 (by decide) (zoneSlotOf t)
        (fun _ v => zr_enc v)
        (fun J => zr_rfield J.D.2 1)
        (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 2 (J.s + 9))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          have := hV.2
          show (zonedTape J.D.2) (2 + q) = _
          exact zr_rfield_at J.D.2 1 (by omega) _ (by omega) _ h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_copy _ _ _ _ [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J] _ _ _ _
          (by rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons,
              List.length_singleton, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 16: scratch right
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (1) (none)
        (fun J => zr_hmT J (zonedTape J.D.2)
          [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmR t J])
        (fun J => zr_heads 2 (J.s + 9)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 17: cut the column's second slot
  (zr_seg (zr_pinCell_step _ 1 (-1) (some none)
        (fun J => zr_hmT J (zonedTape J.D.2)
          [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmR t J])
        (fun J => zr_heads 2 (J.s + 10)))
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_splitLast _ _ _ _ [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J]
          (zr_hmR t J) (1) (by omega)
          (by rw [zr_heads_one, List.length_cons, List.length_cons, List.length_cons,
              List.length_cons, List.length_singleton, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega))
/-- **The home move's first scatter**: write the new home and right zone `0`'s shifted slots. -/
private def zr_hmSc1 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_hmV
      (fun J => zr_hmT J (zonedTape J.D.2) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J])
      (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
      (fun J => zr_heads 2 (J.s + 9))
      (fun J => zr_heads 3 (J.s + 7)) _ zr_hmL zr_hmU from
  -- step 18: back over the home
  zr_segSeq (zr_seg (zr_pinBack_step _ 0 (fun J => zr_rfield J.D.2 0)
        (fun J => zr_hmT J (zonedTape J.D.2)
          [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J])
        (fun J => zr_heads 2 (J.s + 9))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          have := hV.2
          show (zonedTape J.D.2) (2 - ((zr_rfield J.D.2 0).length : ℤ) - 1 + q) = _
          exact zr_rfield_at J.D.2 0 (by omega) _ (by omega) _ h0 h1)
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false]
        all_goals omega)) <|
  -- step 19: write the new home
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (fun c v => zoneSlotSet t c (some (v.getD none)))
        (fun J => zr_hmC t J)
        (fun J => zr_hmT J (zonedTape J.D.2)
          [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J])
        (fun J => zr_heads 0 (J.s + 9))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J]
            (J.s + 9 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J] 5 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 20: clear its column
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_hmC t J)
        (fun J => zr_hmT J (zr_hmA1 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J])
        (fun J => zr_heads 0 (J.s + 9))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J]
            (J.s + 9 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J, zr_hmC t J] 5 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_clear _ _ _ [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J] _ _
          (by rw [zr_heads_one, List.length_cons, List.length_cons, List.length_cons,
              List.length_cons, List.length_singleton, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 21: zoned head right
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (1) (none)
        (fun J => zr_hmT J (zr_hmA1 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 0 (J.s + 9)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 22: zoned head right, to right zone `0`
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (1) (none)
        (fun J => zr_hmT J (zr_hmA1 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 1 (J.s + 9)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 23: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmA1 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 2 (J.s + 9)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 24: scratch left, to the second slot
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmA1 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 2 (J.s + 8)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 25: set right zone `0`'s first slot
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (zoneSlotSet t)
        (fun J => zr_hmE t J)
        (fun J => zr_hmT J (zr_hmA1 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 2 (J.s + 7))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J]
            (J.s + 7 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J] 4 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 26: zoned head right
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (1) (none)
        (fun J => zr_hmT J (zr_hmA2 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 2 (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 27: clear right zone `0`'s second slot
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (fun c _ => zoneSlotSet t c none)
        (fun J => zr_hmE t J)
        (fun J => zr_hmT J (zr_hmA2 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 3 (J.s + 7))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J]
            (J.s + 7 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J] 4 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 28: clear the second slot's column
  (zr_seg (zr_pinClear_step _ 1 (fun J => zr_hmE t J)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J])
        (fun J => zr_heads 3 (J.s + 7))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J]
            (J.s + 7 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J, zr_hmH t J, [], zr_hmE t J] 4 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_cons_succ,
                fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact (zr_scr_clear _ _ _ [[], zr_hmB t J, zr_hmH t J, []] _ _
          (by rw [zr_heads_one, List.length_cons, List.length_cons, List.length_cons,
              List.length_singleton, fieldOffset_cons_succ, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega)).trans
          (zr_scr_nilLast _ _ _ [[], zr_hmB t J, zr_hmH t J]))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega))
/-- **The home move's second scatter**: write left zone `0`'s shifted slots and restore the
heads. -/
private def zr_hmSc2 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_hmV
      (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
      (fun J => zr_hmT J (zr_hmZ t J) [])
      (fun J => zr_heads 3 (J.s + 7))
      (fun J => zr_heads 0 J.s) _ zr_hmL zr_hmU from
  -- step 29: zoned head left
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 3 (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 30: zoned head left
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 2 (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 31: zoned head left
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 1 (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 32: zoned head left
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads 0 (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 33: zoned head left
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads (-1) (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 34: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads (-2) (J.s + 7)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 35: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads (-2) (J.s + 6)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 36: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads (-2) (J.s + 5)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 37: set left zone `0`'s first slot
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (zoneSlotSet t)
        (fun J => zr_hmH t J)
        (fun J => zr_hmT J (zr_hmA3 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads (-2) (J.s + 4))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J, zr_hmH t J]
            (J.s + 4 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J, zr_hmH t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 38: clear the old home's column
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_hmH t J)
        (fun J => zr_hmT J (zr_hmA4 t J) [[], zr_hmB t J, zr_hmH t J])
        (fun J => zr_heads (-2) (J.s + 4))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J, zr_hmH t J]
            (J.s + 4 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J, zr_hmH t J] 2 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact zr_scr_clear _ _ _ [[], zr_hmB t J] _ _
          (by rw [zr_heads_one, List.length_cons, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_cons_succ, fieldOffset_zero]; omega))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 39: zoned head left
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (-1) (none)
        (fun J => zr_hmT J (zr_hmA4 t J) [[], zr_hmB t J])
        (fun J => zr_heads (-2) (J.s + 4)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 40: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmA4 t J) [[], zr_hmB t J])
        (fun J => zr_heads (-3) (J.s + 4)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 41: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmA4 t J) [[], zr_hmB t J])
        (fun J => zr_heads (-3) (J.s + 3)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 42: set left zone `0`'s second slot
  zr_segSeq (zr_seg (zr_pinCopy_step _ 1 0 (by decide) (zoneSlotOf t)
        (zoneSlotSet t)
        (fun J => zr_hmB t J)
        (fun J => zr_hmT J (zr_hmA4 t J) [[], zr_hmB t J])
        (fun J => zr_heads (-3) (J.s + 2))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J]
            (J.s + 2 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun _ _ => zr_copy0 _ _ _ _ _ _ _)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 43: clear its column
  zr_segSeq (zr_seg (zr_pinClear_step _ 1 (fun J => zr_hmB t J)
        (fun J => zr_hmT J (zr_hmZ t J) [[], zr_hmB t J])
        (fun J => zr_heads (-3) (J.s + 2))
        fun J hV q h0 h1 => by
          have := zr_hmLen t hV
          show zr_scr (zr_pσ J) J.s [[], zr_hmB t J]
            (J.s + 2 + q) = _
          exact zr_scr_at (zr_stk_blank hV.1 _ le_rfl)
            [[], zr_hmB t J] 1 (by simp) _
            (by rw [fieldOffset_cons_succ, fieldOffset_zero]; omega) q h0 h1)
      (fun J hV => by
        have := zr_hmLen t hV
        exact (zr_scr_clear _ _ _ [[]] _ _
          (by rw [zr_heads_one, List.length_singleton, fieldOffset_cons_succ,
              fieldOffset_zero]; omega)).trans
          (zr_scr_nilLast _ _ _ []))
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [zr_heads, zr_hmL, zr_hmU, if_true, show (1 : Fin 2) ≠ 0 by decide,
          if_false]
        all_goals omega)) <|
  -- step 44: zoned head right
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (1) (none)
        (fun J => zr_hmT J (zr_hmZ t J) [])
        (fun J => zr_heads (-3) (J.s + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 45: zoned head right
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (1) (none)
        (fun J => zr_hmT J (zr_hmZ t J) [])
        (fun J => zr_heads (-2) (J.s + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 46: zoned head right
  zr_segSeq (zr_seg (zr_pinCell_step _ 0 (1) (none)
        (fun J => zr_hmT J (zr_hmZ t J) [])
        (fun J => zr_heads (-1) (J.s + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_one]
        all_goals omega)) <|
  -- step 47: scratch left
  zr_segSeq (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmZ t J) [])
        (fun J => zr_heads 0 (J.s + 2)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega)) <|
  -- step 48: scratch left
  (zr_seg (zr_pinCell_step _ 1 (-1) (none)
        (fun J => zr_hmT J (zr_hmZ t J) [])
        (fun J => zr_heads 0 (J.s + 1)))
      (fun _ _ => rfl)
      (fun J hV => by
        have := zr_hmLen t hV
        refine ⟨zr_heads_ext ?_ ?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
        all_goals simp only [Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), zr_heads, zr_hmL, zr_hmU, if_true,
          show (1 : Fin 2) ≠ 0 by decide, if_false, SignType.coe_neg_one]
        all_goals omega))

/-- **The home move's column operation**, as one pinned segment: the gather and the two
scatters. -/
private def zr_hmSeg {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  letI : DecidableEq (zr_stOf (zr_hmGat t x).C) := by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance)
  letI : DecidableEq (zr_stOf (zr_hmSc1 t x).C) := by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance)
  zr_segSeq (zr_hmGat t x) (zr_segSeq (zr_hmSc1 t x) (zr_hmSc2 t x))

/-- The home move's column operation, from left zone `0`'s outer cell back to the home in
`146` steps. -/
private lemma zr_hmSeg_spec {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_hmSeg t x).C zr_hmV (fun J => zr_hmT J (zonedTape J.D.2) [])
      (fun J => zr_hmT J (zr_hmZ t J) []) (fun J => zr_heads (-3) J.s)
      (fun J => zr_heads 0 J.s) (fun _ => 146) zr_hmL zr_hmU :=
  zr_PinStep_congr (zr_hmSeg t x).step (fun _ _ => rfl) (fun _ _ => rfl)
    (fun J hV => by
      have := zr_hmLen t hV
      omega) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)

/-- The home move's slot positions: zone `0`'s two cells on each side. -/
private lemma zr_hm_pos :
    zr_zonePos false 0 1 = -3 ∧ zr_zonePos false 0 0 = -2 ∧ zr_zonePos true 0 0 = 2 ∧
      zr_zonePos true 0 1 = 3 ∧ zoneCapacity 0 = 2 := by
  have hs : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  simp only [zr_zonePos, if_true, Bool.false_eq_true, if_false, hs, zoneCapacity_eq]
  norm_num

/-- A cell of the zoned tape whose track-`t` slot is `v` gives the scratch cell of `v`. -/
private lemma zr_enc_of_slot {k : ℕ} (t : Fin k) {o : Option (ZoneSym k)}
    {v : Option (Option Bool)} (h : o.map (zoneSlotOf t) = some v) :
    o.map (fun γ => zr_enc (zoneSlotOf t γ)) = some (zr_enc v : ZoneSym k) := by
  cases o with
  | none => cases h
  | some γ =>
    rw [Option.map_some, Option.some.injEq] at h
    rw [Option.map_some, h]

/-- The home move's scratch cells: track `t`'s slots of left zone `0`'s inner cell, the home,
and right zone `0`'s two cells. -/
private lemma zr_hm_cells {k : ℕ} (t : Fin k) {J : zr_Px k} (hV : zr_hmV J) :
    FinTM.bufferTape (zr_hmB t J) 0 = some (zr_enc ((J.D.2 t).left ⟨0, hV.2⟩)[0]?) ∧
      FinTM.bufferTape (zr_hmH t J) 0 = some (zr_enc (some (J.D.2 t).home)) ∧
      FinTM.bufferTape (zr_hmC t J) 0 = some (zr_enc ((J.D.2 t).right ⟨0, hV.2⟩)[0]?) ∧
      FinTM.bufferTape (zr_hmE t J) 0 = some (zr_enc ((J.D.2 t).right ⟨0, hV.2⟩)[1]?) := by
  obtain ⟨e1, e2, e3, l1, r1, r0, -⟩ := zr_hmLen t hV
  obtain ⟨p1, p2, p3, p4, hc⟩ := zr_hm_pos
  have h1 : 1 ≤ J.D.1 := hV.2
  have hc' : zoneCapacity ((⟨0, hV.2⟩ : Fin J.D.1) : ℕ) = 2 := hc
  have rd := fun (side : Bool) (p : ℕ) (hp : p < 2) =>
    zr_read_slot side J.D.2 ⟨0, hV.2⟩ t p (by rw [hc']; exact hp)
  have fl := fun (q : ℤ) (h0 : -1 ≤ q) (h2 : q ≤ 2) =>
    zr_lfield_at J.D.2 1 h1 (-3) l1.symm q h0 (by rw [e1]; exact_mod_cast h2)
  have fr := fun (q : ℤ) (h0 : -1 ≤ q) (h2 : q ≤ 2) =>
    zr_rfield_at J.D.2 1 h1 2 r1.symm q h0 (by rw [e2]; exact_mod_cast h2)
  have fh := zr_rfield_at J.D.2 0 (Nat.zero_le _) 0 r0.symm 0 (by norm_num) (by rw [e3]; norm_num)
  have g1 := fl 1 (by norm_num) (by norm_num)
  have g2 := fr 0 (by norm_num) (by norm_num)
  have g3 := fr 1 (by norm_num) (by norm_num)
  rw [FinTM.bufferTape_eq, if_pos (by norm_num)] at g1 g2 g3 fh
  norm_num at g1 g2 g3 fh
  have s1 := rd false 0 (by norm_num)
  have s2 := rd true 0 (by norm_num)
  have s3 := rd true 1 (by norm_num)
  simp only [p2, p3, p4, ZoneContents.words_false, ZoneContents.words_true] at s1 s2 s3
  simp only [FinTM.bufferTape_eq, le_refl, if_true, Int.toNat_zero, zr_hmB, zr_hmH, zr_hmC,
    zr_hmE, zr_hmCL, zr_hmR, zr_col, List.getElem?_drop, List.getElem?_take, List.getElem?_map,
    Nat.add_zero, show (0 : ℕ) < 1 from Nat.one_pos, if_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← g1]
    exact zr_enc_of_slot t s1
  · rw [← fh, Option.map_some, zoneSlotOf_inr]
  · rw [← g2]
    exact zr_enc_of_slot t s2
  · rw [← g3]
    exact zr_enc_of_slot t s3

/-- **The home move on the zoned tape**, its guard enabled: when track `t`'s left zone `0` has
room (its outer slot `⊠`), the column operation's tape is the zoned tape of the moved track. -/
private lemma zr_hmZ_eq {k : ℕ} (t : Fin k) {J : zr_Px k} (hV : zr_hmV J)
    (hg : (zonedTape J.D.2 (-3)).map (zoneSlotOf t) = some none) :
    zr_hmZ t J = zonedTape (Function.update J.D.2 t (zoneMove true (J.D.2 t))) := by
  obtain ⟨-, -, -, -, -, -, -, eB, eH, -, eE, eC, -⟩ := zr_hmLen t hV
  obtain ⟨cB, cH, cC, cE⟩ := zr_hm_cells t hV
  obtain ⟨p1, p2, p3, p4, hc⟩ := zr_hm_pos
  have hℓ : 0 < J.D.1 := hV.2
  have hs0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
  have hc' : zoneCapacity ((⟨0, hℓ⟩ : Fin J.D.1) : ℕ) = 2 := hc
  have hroom : ((J.D.2 t).left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 := by
    have h := (zr_room_iff false J.D.2 ⟨0, hℓ⟩ t 1 Nat.one_pos (by rw [hc']; norm_num)).mp
    rw [ZoneContents.words_false, hc'] at h
    rw [hc]
    exact h (by
      rw [show zr_zonePos false ((⟨0, hℓ⟩ : Fin J.D.1) : ℕ) (2 - 1) = -3 from p1]
      exact hg)
  rw [zoneMove_true, dif_pos hℓ, dif_pos hroom]
  set u := zoneMoveRight hℓ (J.D.2 t) hroom with hu
  have rd := fun (side : Bool) (p : ℕ) (hp : p < 2) =>
    zr_read_slot side (fun _ => u) ⟨0, hℓ⟩ t p (by rw [hc']; exact hp)
  have n1 := rd false 1 (by norm_num)
  have n2 := rd false 0 (by norm_num)
  have n3 := rd true 0 (by norm_num)
  have n4 := rd true 1 (by norm_num)
  simp only [p1, p2, p3, p4, ZoneContents.words_false, ZoneContents.words_true, hu,
    zoneMoveRight_left, zoneMoveRight_right, if_true] at n1 n2 n3 n4
  have hlen : ((J.D.2 t).right ⟨0, hℓ⟩).length ≤ 2 := by
    have := (J.D.2 t).right_le ⟨0, hℓ⟩
    rwa [hc'] at this
  funext q
  simp only [zr_hmZ, zr_hmA4, zr_hmA3, zr_hmA2, zr_hmA1, zr_wr0, eB, eH, eE, eC, Nat.cast_one]
  split_ifs with h5 h4 h3 h2 h1
  all_goals first
    | (exfalso; omega)
    | skip
  · obtain rfl : q = -3 := by omega
    rw [show (-3 : ℤ) - -3 = 0 by norm_num, cB, Option.map_some, zoneSlotOf_inr,
      zr_zonedTape_update _ t u _ _ n1]
    simp only [List.getElem?_cons_succ]
  · obtain rfl : q = -2 := by omega
    rw [show (-2 : ℤ) - -2 = 0 by norm_num, cH, Option.map_some, zoneSlotOf_inr,
      zr_zonedTape_update _ t u _ _ n2]
    simp only [List.getElem?_cons_zero]
  · obtain rfl : q = 3 := by omega
    rw [show (3 : ℤ) - 3 = 0 by norm_num, cE, Option.map_some,
      zr_zonedTape_update _ t u _ _ n4, List.getElem?_tail,
      List.getElem?_eq_none (show ((J.D.2 t).right ⟨0, hℓ⟩).length ≤ 1 + 1 by omega)]
  · obtain rfl : q = 2 := by omega
    rw [show (2 : ℤ) - 2 = 0 by norm_num, cE, Option.map_some, zoneSlotOf_inr,
      zr_zonedTape_update _ t u _ _ n3, List.getElem?_tail]
  · obtain rfl : q = 0 := by omega
    rw [show (0 : ℤ) - 0 = 0 by norm_num, cC, Option.map_some, zoneSlotOf_inr,
      zr_zonedTape_update _ t u 0 (some u.home) (by rw [zonedTape_zero, Option.map_some,
        zoneSlotOf_inr])]
    rw [hu, zoneMoveRight_home]
    cases ((J.D.2 t).right ⟨0, hℓ⟩) <;> rfl
  · symm
    apply zr_zonedTape_update_same
    rw [zr_slot_track (z := J.D.2) (z' := fun _ => J.D.2 t) rfl q]
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · rw [zonedTape_of_neg _ hq, zonedTape_of_neg _ hq, zoneCellAt_eq, zoneCellAt_eq]
      cases ho : zoneOwner J.D.1 (-q).toNat with
      | none => rfl
      | some o =>
        have hm := (Fin.find_eq_some_iff.mp ((zoneOwner_eq J.D.1 (-q).toNat).symm.trans ho)).1
        simp only [Option.map_some, zoneSlotOf_inr, ZoneContents.words_false, hu,
          zoneMoveRight_left]
        rw [if_neg]
        intro ho0
        rw [ho0, hs0, hc] at hm
        omega
    · omega
    · rw [zonedTape_of_pos _ hq, zonedTape_of_pos _ hq, zoneCellAt_eq, zoneCellAt_eq]
      cases ho : zoneOwner J.D.1 q.toNat with
      | none => rfl
      | some o =>
        have hm := (Fin.find_eq_some_iff.mp ((zoneOwner_eq J.D.1 q.toNat).symm.trans ho)).1
        simp only [Option.map_some, zoneSlotOf_inr, ZoneContents.words_true, hu,
          zoneMoveRight_right]
        rw [if_neg]
        intro ho0
        rw [ho0, hs0, hc] at hm
        omega

/-- With the guard off, left zone `0` full, the home move is the identity. -/
private lemma zr_hm_off {k : ℕ} (t : Fin k) {J : zr_Px k} (hV : zr_hmV J)
    (hg : (zonedTape J.D.2 (-3)).map (zoneSlotOf t) ≠ some none) :
    zonedTape (Function.update J.D.2 t (zoneMove true (J.D.2 t))) = zonedTape J.D.2 := by
  obtain ⟨p1, -, -, -, hc⟩ := zr_hm_pos
  have hℓ : 0 < J.D.1 := hV.2
  have hc' : zoneCapacity ((⟨0, hℓ⟩ : Fin J.D.1) : ℕ) = 2 := hc
  have hno : ¬ ((J.D.2 t).left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 := by
    intro h
    have h' := (zr_room_iff false J.D.2 ⟨0, hℓ⟩ t 1 Nat.one_pos (by rw [hc']; norm_num)).mpr
    rw [ZoneContents.words_false, hc'] at h'
    rw [hc] at h
    exact hg (by rw [← p1]; exact h' h)
  rw [zoneMove_true, dif_pos hℓ, dif_neg hno, Function.update_eq_self]

/-- **A joined body**: a body run inside a loop host from its entry, every exit of which the way
back sends to the escape, as a contract with that one exit. -/
private def zr_joinContract {k : ℕ} {B J : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X J x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) (hall : ∀ s, some s ∈ X → back s = some (some true))
    (hne : ∃ s, some s ∈ X) :
    Contract (zr_hostTM MB e back) ⟨true, e⟩ {some ⟨false, some true⟩} J x :=
  zr_exitsContract (zr_hostBodyContract back C hnone hX) _ (by
    ext q
    constructor
    · rintro ⟨s, hs, rfl⟩
      show (back s).map _ = _
      rw [hall s hs]
      rfl
    · intro hq
      obtain ⟨s, hs⟩ := hne
      refine ⟨s, hs, ?_⟩
      rw [Set.mem_singleton_iff.mp hq]
      show _ = (back s).map _
      rw [hall s hs]
      rfl)

/-- A joined body is a pinned step when the body is, one dispatch step longer. -/
private lemma zr_join_step {k : ℕ} {B J : Type} {x : List (ZoneSym k)}
    {MB : MultiTapeTM 2 (ZoneSym k) B} {e : B} {X : Set (Option B)}
    (back : B → Option (Option Bool)) (C : Contract MB e X J x) (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ back s ≠ none) (hall : ∀ s, some s ∈ X → back s = some (some true))
    (hne : ∃ s, some s ∈ X) {V : J → Prop} {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)}
    {p₁ p₂ : J → Fin 2 → ℤ} {τ : J → ℕ} {L U : J → Fin 2 → ℤ}
    (h : zr_PinStep C V T₁ T₂ p₁ p₂ τ L U) :
    zr_PinStep (zr_joinContract back C hnone hX hall hne) V T₁ T₂ p₁ p₂ (fun j => τ j + 1) L U := by
  unfold zr_joinContract
  refine zr_PinStep_exits ⟨fun j d hd => ?_, fun j d hV hd => ?_⟩
  · rw [zr_hostBodyContract, Contract.inPhase_pre] at hd
    obtain ⟨hV, hd'⟩ := h.1 j _ hd
    exact ⟨hV, (zr_pinned_mapState_iff _).mp hd'⟩
  obtain ⟨hp, hq, hi, ho, ht, hb⟩ := h.2 j _ hV ((zr_pinned_mapState_iff _).mpr hd)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zr_hostBodyContract, Contract.inPhase_pre]
    exact hp
  · rw [zr_hostBodyContract, Contract.inPhase_post]
    exact ⟨funext fun i => funext fun q =>
        (Cfg.bindState_workTapes _ _ i q).trans (congrFun (congrFun hq.1 i) q),
      funext fun i => (Cfg.bindState_workTapePos _ _ i).trans (congrFun hq.2 i)⟩
  · rw [zr_hostBodyContract, Contract.inPhase_post, Cfg.bindState_inputPos, hi,
      Cfg.mapState_inputPos]
  · rw [zr_hostBodyContract, Contract.inPhase_post, Cfg.bindState_output, ho, Cfg.mapState_output]
  · rw [zr_hostBodyContract, Contract.inPhase_time, ht]
  · intro i
    rw [zr_hostBodyContract, Contract.inPhase_lo, Contract.inPhase_hi]
    exact hb i

/-- **The home move's next index**: track `t` moved one cell right by the guarded home move. -/
private abbrev zr_hmNxt {k : ℕ} (t : Fin k) (J : zr_Px k) : zr_Px k :=
  ⟨⟨J.D.1, Function.update J.D.2 t (zoneMove true (J.D.2 t))⟩, J.i, J.β, J.b, J.s⟩

/-- The home move's guard verdict: `true` when the guard is off, left zone `0`'s outer slot
occupied. -/
private abbrev zr_hmOff {k : ℕ} (t : Fin k) (J : zr_Px k) : Bool :=
  (fun c => !zr_slotEmpty t c) (zr_pT J 0 (zr_heads (-3) J.s 0))

/-- The guard verdict read on the zoned tape. -/
private lemma zr_hmOff_iff {k : ℕ} (t : Fin k) {J : zr_Px k} (hV : zr_hmV J) :
    zr_hmOff t J = false ↔ (zonedTape J.D.2 (-3)).map (zoneSlotOf t) = some none := by
  obtain ⟨-, -, -, l1, -⟩ := zr_hmLen t hV
  have hs := zr_lstart_isSome J.D.2 1 hV.2
  rw [l1] at hs
  show (!zr_slotEmpty t (zonedTape J.D.2 (-3))) = false ↔ _
  rw [Bool.not_eq_false', zr_slotEmpty_iff t hs]

/-- The home move's lead: back over left zone `0`, to its outer cell. -/
private def zr_hmLead {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_pinBackContract x zr_hmV 0 (fun J => zr_lfield J.D.2 1) zr_pT (fun J => zr_heads 0 J.s)
    fun J hV q h0 h1 => by
      have := zr_hmLen t hV
      have := hV.2
      show zonedTape J.D.2 (0 - ((zr_lfield J.D.2 1).length : ℤ) - 1 + q) = _
      exact zr_lfield_at J.D.2 1 (by omega) _ (by omega) _ h0 h1

/-- The home move's lead is a pinned step from the home to left zone `0`'s outer cell. -/
private lemma zr_hmLead_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_hmLead t x) zr_hmV zr_pT zr_pT (fun J => zr_heads 0 J.s)
      (fun J => zr_heads (-3) J.s) (fun _ => 5) zr_hmL zr_hmU :=
  zr_PinStep_congr (zr_pinBack_step _ 0 _ _ _ _) (fun _ _ => rfl)
    (fun J hV => by
      have := zr_hmLen t hV
      rw [zr_heads_set0]
      exact congrArg (zr_heads · J.s) (by show (0 : ℤ) - _ - 1 = -3; omega))
    (fun J hV => by
      have := zr_hmLen t hV
      omega)
    (fun J hV => by
      have := zr_hmLen t hV
      rw [zr_heads_set0]
      exact zr_heads_le (by show (-4 : ℤ) ≤ 0 - _ - 2; omega) (by show J.s - 1 ≤ J.s; omega))
    (fun J _ => zr_heads_le (by show (0 : ℤ) ≤ 4; norm_num) (by show J.s ≤ J.s + 11; omega))

/-- The home move's guard test, stationary at left zone `0`'s outer cell. -/
private lemma zr_hmTest_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_pinTestContract x zr_hmV 0 (fun c => !zr_slotEmpty t c) 0 zr_pT
        fun J => zr_heads (-3) J.s) zr_hmV zr_pT zr_pT (fun J => zr_heads (-3) J.s)
      (fun J => zr_heads (-3) J.s) (fun _ => 1) zr_hmL zr_hmU :=
  zr_PinStep_congr (zr_pinTest_step _ 0 _ 0 _ _) (fun _ _ => rfl)
    (fun _ _ => by rw [SignType.coe_zero, add_zero, Function.update_eq_self]) (fun _ _ => rfl)
    (fun J _ => by
      rw [SignType.coe_zero, add_zero, Function.update_eq_self]
      exact zr_heads_le (by show (-4 : ℤ) ≤ min (-3) (-3); norm_num)
        (by show J.s - 1 ≤ min J.s J.s; omega))
    (fun J _ => by
      rw [SignType.coe_zero, add_zero, Function.update_eq_self]
      exact zr_heads_le (by show max (-3) (-3) ≤ (4 : ℤ); norm_num)
        (by show max J.s J.s ≤ J.s + 11; omega))

/-- The home move's off arm: skip left zone `0` back to the home. -/
private def zr_hmSkip {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_pinSkipContract x (fun J => zr_hmV J ∧ zr_hmOff t J = true) 0 (fun J => zr_lfield J.D.2 1)
    zr_pT (fun J => zr_heads (-3) J.s) fun J hV q h0 h1 => by
      have := zr_hmLen t hV.1
      have := hV.1.2
      show zonedTape J.D.2 (-3 + q) = _
      exact zr_lfield_at J.D.2 1 (by omega) _ (by omega) _ (by omega) h1

/-- With the guard off, the skip back is the home move's pinned step. -/
private lemma zr_hmSkip_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_hmSkip t x) (fun J => zr_hmV J ∧ zr_hmOff t J = true) zr_pT
      (fun J => zr_pT (zr_hmNxt t J)) (fun J => zr_heads (-3) J.s) (fun J => zr_heads 0 J.s)
      (fun _ => 3) zr_hmL zr_hmU :=
  zr_PinStep_congr (zr_pinSkip_step _ 0 _ _ _ _)
    (fun J hV => by
      show zr_tapes (zonedTape J.D.2) (zr_pσ J) =
        zr_tapes (zonedTape (Function.update J.D.2 t (zoneMove true (J.D.2 t)))) (zr_pσ J)
      rw [zr_hm_off t hV.1 fun h => absurd (hV.2.symm.trans ((zr_hmOff_iff t hV.1).mpr h))
        (by decide)])
    (fun J hV => by
      have := zr_hmLen t hV.1
      rw [zr_heads_set0]
      exact congrArg (zr_heads · J.s) (by show (-3 : ℤ) + _ + 1 = 0; omega))
    (fun J hV => by
      have := zr_hmLen t hV.1
      omega)
    (fun J _ => zr_heads_le (by show (-4 : ℤ) ≤ -3; norm_num) (by show J.s - 1 ≤ J.s; omega))
    (fun J hV => by
      have := zr_hmLen t hV.1
      rw [zr_heads_set0]
      exact zr_heads_le (by show -3 + _ + 1 ≤ (4 : ℤ); omega) (by show J.s ≤ J.s + 11; omega))

/-- With the guard on, the column operation is the home move's pinned step. -/
private lemma zr_hmArm_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_reindexContract (zr_hmSeg t x).C (fun J => J)
        (fun J d => (zr_hmV J ∧ zr_hmOff t J = false) ∧
          zr_pinned (zr_hmT J (zonedTape J.D.2) []) (zr_heads (-3) J.s) d)
        fun J d hd => ((zr_hmSeg_spec t x).2 J d hd.1.1 hd.2).1)
      (fun J => zr_hmV J ∧ zr_hmOff t J = false) zr_pT (fun J => zr_pT (zr_hmNxt t J))
      (fun J => zr_heads (-3) J.s) (fun J => zr_heads 0 J.s) (fun _ => 146) zr_hmL zr_hmU :=
  zr_PinStep_start (zr_PinStep_congr
    (zr_PinStep_re (zr_hmSeg_spec t x) (fun J => J) (fun J => zr_hmV J ∧ zr_hmOff t J = false)
      fun _ h => h.1)
    (fun J hV => by
      show zr_tapes (zr_hmZ t J) (zr_scr (zr_pσ J) J.s []) =
        zr_tapes (zonedTape (Function.update J.D.2 t (zoneMove true (J.D.2 t)))) (zr_pσ J)
      rw [zr_scr_nil (zr_stk_blank hV.1.1), zr_hmZ_eq t hV.1 ((zr_hmOff_iff t hV.1).mp hV.2)])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl))
    fun J hV => by
      show zr_tapes (zonedTape J.D.2) (zr_scr (zr_pσ J) J.s []) = zr_tapes _ (zr_pσ J)
      rw [zr_scr_nil (zr_stk_blank hV.1.1)]

/-- **The guarded home move**: test left zone `0`'s outer slot; off, skip back home; on, run
the column operation. -/
private def zr_hmBr {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  Contract.branch (by decide : (some true : Option Bool) ≠ some false) _ (zr_hmSkip t x)
    _ (fun J => J) (fun J => J)
    (zr_pin_blink true (by decide : (some true : Option Bool) ≠ some false) (zr_hmTest_step t x)
      (fun J d _ hd => by
        rw [zr_pinTest_state _ _ _ _ _ _ J d hd]
        exact zr_verdict_ite some _) rfl (zr_hmSkip_step t x))
    (zr_pin_blink false (by decide : (some true : Option Bool) ≠ some false) (zr_hmTest_step t x)
      (fun J d _ hd => by
        rw [zr_pinTest_state _ _ _ _ _ _ J d hd]
        exact zr_verdict_ite some _) rfl (zr_hmArm_step t x))

/-- The guarded home move is a pinned step to the moved index. -/
private lemma zr_hmBr_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_hmBr t x) zr_hmV zr_pT (fun J => zr_pT (zr_hmNxt t J))
      (fun J => zr_heads (-3) J.s) (fun J => zr_heads 0 J.s)
      (fun J => 1 + 1 + if zr_hmOff t J then 3 else 146) zr_hmL zr_hmU :=
  zr_PinStep_branch _ (zr_hmTest_step t x)
    (fun J d _ hd => by
      rw [zr_pinTest_state _ _ _ _ _ _ J d hd]
      exact zr_verdict_ite some _) (zr_hmSkip_step t x) (zr_hmArm_step t x) _ _

/-- The home move's body: the lead to left zone `0`'s outer cell, then the guarded move. -/
private def zr_hmBody {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  (zr_hmLead t x).seq (zr_hmBr t x) (fun J => J)
    (zr_pin_hlink (zr_hmLead_step t x) (zr_hmBr_step t x))

/-- The home move's body is a pinned step from the home to the moved index's home. -/
private lemma zr_hmBody_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_hmBody t x) zr_hmV zr_pT (fun J => zr_pT (zr_hmNxt t J))
      (fun J => zr_heads 0 J.s) (fun J => zr_heads 0 J.s)
      (fun J => 5 + 1 + (1 + 1 + if zr_hmOff t J then 3 else 146)) zr_hmL zr_hmU :=
  zr_PinStep_seq' (zr_hmLead_step t x) (zr_hmBr_step t x) _

/-- The home move's way back: both of its exits escape. -/
private noncomputable def zr_hmBack {k : ℕ} (t : Fin k) :
    zr_stOf (zr_hmBody t ([] : List (ZoneSym k))) → Option (Option Bool) :=
  zr_seqBack (zr_branchBack (zr_oneBack (zr_exitOf (zr_hmSkip t ([] : List (ZoneSym k)))) true)
    (zr_oneBack (zr_exitOf (zr_hmSeg t ([] : List (ZoneSym k))).C) true))

/-- The home move's exits are its way back's domain. -/
private lemma zr_hmBody_hX {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ s, some s ∈ zr_exitsOf (zr_hmBody t x) ↔ zr_hmBack t s ≠ none :=
  zr_seqBack_hX (zr_branchBack_hX (zr_oneBack_hX _ _) (zr_oneBack_hX _ _))

/-- The home move never halts. -/
private lemma zr_hmBody_none {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    none ∉ zr_exitsOf (zr_hmBody t x) :=
  zr_none_not_mem_image _ zr_none_one

/-- Every return of the home move's way back is the escape. -/
private lemma zr_hmBack_true {k : ℕ} (t : Fin k) (s : zr_stOf (zr_hmBody t ([] : List (ZoneSym k))))
    (h : zr_hmBack t s ≠ none) : zr_hmBack t s = some (some true) := by
  rcases s with s | ((s | s) | s)
  · exact absurd rfl h
  · exact absurd rfl h
  · simp only [zr_hmBack, zr_seqBack, zr_branchBack, zr_oneBack] at h ⊢
    split_ifs at h ⊢
    · rfl
    · exact absurd rfl h
  · simp only [zr_hmBack, zr_seqBack, zr_branchBack, zr_oneBack] at h ⊢
    split_ifs at h ⊢
    · rfl
    · exact absurd rfl h

/-- **The home move**, as a contract with one exit: inside a loop host, the lead, the guard
test and the guarded move, both of whose exits escape. -/
private noncomputable def zr_hmContract {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_joinContract (zr_hmBack t) (zr_hmBody t x) (zr_hmBody_none t x) (zr_hmBody_hX t x)
    (fun s hs => zr_hmBack_true t s ((zr_hmBody_hX t x s).mp hs))
    ⟨.inr (.inr (zr_exitOf (zr_hmSeg t ([] : List (ZoneSym k))).C)), (zr_hmBody_hX t x _).mpr
      (by simp only [zr_hmBack, zr_seqBack, zr_branchBack, zr_oneBack]; simp)⟩

/-- **The home move's pinned step**: from the home, track `t` moved by the guarded home move,
the heads back, in `12` steps with the guard off and `155` with it on. -/
private lemma zr_hmContract_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_hmContract t x) zr_hmV zr_pT (fun J => zr_pT (zr_hmNxt t J))
      (fun J => zr_heads 0 J.s) (fun J => zr_heads 0 J.s)
      (fun J => if zr_hmOff t J then 12 else 155) zr_hmL zr_hmU :=
  zr_PinStep_congr (zr_join_step _ _ _ _ _ _ (zr_hmBody_step t x)) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun J _ => by split_ifs <;> rfl) (fun _ _ _ => le_rfl)
    (fun _ _ _ => le_rfl)

/-- A descending pass's levels, read off its rounds, are the cascade's descending levels: the
rounds at fields `j + 1, …, 1` act at levels `j, …, 0`, and level `0` acts as the identity. -/
private lemma zr_fold_desc {ℓ : ℕ} (g : ℕ → ZoneContents ℓ → ZoneContents ℓ) (hg : ∀ w, g 0 w = w)
    (j : ℕ) (z : ZoneContents ℓ) :
    (List.range (j + 1)).foldl (fun w r => g (j + 1 - r - 1) w) z =
      (List.range j).reverse.foldl (fun a i => g (i + 1) a) z := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    show j + 1 - j - 1 = 0 by omega, hg]
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
    conv_lhs => rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    conv_rhs => rw [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    rw [show j + 1 + 1 - 0 - 1 = j + 1 by omega, ← ih]
    congr 1
    funext w r
    congr 1
    omega

/-- An ascending pass's levels, read off its rounds, are the cascade's ascending levels. -/
private lemma zr_fold_asc {ℓ : ℕ} (g : ℕ → ZoneContents ℓ → ZoneContents ℓ) (j : ℕ)
    (z : ZoneContents ℓ) :
    (List.range j).foldl (fun w r => g ((fun i => i + 1)^[r] 0 + 1) w) z =
      (List.range j).foldl (fun a i => g (i + 1) a) z := by
  congr 1
  funext w r
  rw [zr_iterate_succ, zero_add]

/-- Pass indices agree when their fields do. -/
private lemma zr_Px_ext {k : ℕ} {P Q : zr_Px k} (hD : P.D = Q.D) (hi : P.i = Q.i) (hβ : P.β = Q.β)
    (hb : P.b = Q.b) (hs : P.s = Q.s) : P = Q := by
  cases P
  cases Q
  simp only at hD hi hβ hb hs
  subst hD hi hβ hb hs
  rfl

/-- **The found path's start**: the anchor at the scanned zone's field `P.i = i₀ + 1`, inside
the layout, and an empty count stack over a base whose cell below is blank. -/
private def zr_fpV {k : ℕ} (P : zr_Px k) : Prop :=
  zr_pxV P ∧ P.β (P.b - 1) = none ∧ P.s = P.b ∧ 1 ≤ P.i ∧ P.i ≤ P.D.1

/-- A found-path stage: track `t` set to `z`, the anchor's field `i`, the stack's top `s`. -/
private abbrev zr_fpC {k : ℕ} (t : Fin k) (P : zr_Px k) (z : ZoneContents P.D.1) (i : ℕ)
    (s : ℤ) : zr_Px k :=
  ⟨⟨P.D.1, Function.update P.D.2 t z⟩, i, P.β, P.b, s⟩

/-- Track `t` after the descending right pass: inward shifts at levels `i₀, …, 1`. -/
private abbrev zr_fpZ1 {k : ℕ} (t : Fin k) (P : zr_Px k) : ZoneContents P.D.1 :=
  (List.range (P.i - 1)).reverse.foldl (fun a i => zoneShiftIn true (i + 1) a) (P.D.2 t)

/-- Track `t` after the descending left pass: outward shifts at levels `i₀, …, 1`. -/
private abbrev zr_fpZ2 {k : ℕ} (t : Fin k) (P : zr_Px k) : ZoneContents P.D.1 :=
  (List.range (P.i - 1)).reverse.foldl (fun a i => zoneShiftOut false (i + 1) a) (zr_fpZ1 t P)

/-- Track `t` after the home move. -/
private abbrev zr_fpZ3 {k : ℕ} (t : Fin k) (P : zr_Px k) : ZoneContents P.D.1 :=
  zoneMove true (zr_fpZ2 t P)

/-- Track `t` after the ascending right pass: inward shifts at levels `1, …, i₀`. -/
private abbrev zr_fpZ4 {k : ℕ} (t : Fin k) (P : zr_Px k) : ZoneContents P.D.1 :=
  (List.range (P.i - 1)).foldl (fun a i => zoneShiftIn true (i + 1) a) (zr_fpZ3 t P)

/-- Track `t` after the ascending left pass: outward shifts at levels `1, …, i₀`. -/
private abbrev zr_fpZ5 {k : ℕ} (t : Fin k) (P : zr_Px k) : ZoneContents P.D.1 :=
  (List.range (P.i - 1)).foldl (fun a i => zoneShiftOut false (i + 1) a) (zr_fpZ4 t P)

/-- A pass whose rounds keep every track ends at the start's data. -/
private lemma zr_pxFold_id {k : ℕ} (t : Fin k) (G : ℕ → ℕ) (P : zr_Px k) (m : ℕ) :
    zr_pxFold t (fun _ _ w => w) G P m = P.D.2 t := by
  unfold zr_pxFold
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]

/-- **A descending pass's end**: from field `Q.i ≥ 1`, its `Q.i` rounds act at levels
`Q.i - 1, …, 0`, the last as the identity; it ends at the home with `Q.i` marks pushed. -/
private lemma zr_dnPass_end {k : ℕ} (t : Fin k)
    (g : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) (hg : ∀ ℓ w, g ℓ 0 w = w) (Q : zr_Px k)
    (h1 : 1 ≤ Q.i) :
    (zr_dnF t fun ℓ i w => g ℓ (i - 1) w)^[Q.i - 1 + 1] Q =
      ⟨⟨Q.D.1, Function.update Q.D.2 t
        ((List.range (Q.i - 1)).reverse.foldl (fun a i => g Q.D.1 (i + 1) a) (Q.D.2 t))⟩,
        0, Q.β, Q.b, Q.s + Q.i⟩ := by
  obtain ⟨hD, hi, hβ, hb, hs⟩ := zr_px_iter t (fun ℓ i w => g ℓ (i - 1) w) (fun i => i - 1) 1 Q
    (Q.i - 1 + 1)
  refine zr_Px_ext ?_ ?_ hβ hb ?_
  · rw [hD]
    congr 2
    unfold zr_pxFold
    obtain ⟨j, hj⟩ : ∃ j, Q.i = j + 1 := ⟨Q.i - 1, by omega⟩
    simp only [zr_iterate_pred, hj, Nat.add_sub_cancel]
    exact zr_fold_desc (g Q.D.1) (hg Q.D.1) j (Q.D.2 t)
  · rw [hi, zr_iterate_pred]
    show Q.i - (Q.i - 1 + 1) = 0
    omega
  · rw [hs]
    show Q.s + ((Q.i - 1 + 1 : ℕ) : ℤ) * 1 = Q.s + Q.i
    push_cast
    omega

/-- **The descending right pass ends at stage one**: at the home, `i₀ + 1` marks pushed. -/
private lemma zr_fp1 {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_fpV P) :
    (zr_p1Nxt t)^[P.i - 1 + 1] P = zr_fpC t P (zr_fpZ1 t P) 0 (P.b + P.i) := by
  have h := zr_dnPass_end t (fun _ i w => zoneShiftIn true i w) (fun _ => zr_shiftIn_zero) P
    hV.2.2.2.1
  rw [hV.2.2.1] at h
  exact h

/-- A pop pass ends, one stopping round after its marks run out, where its pops leave it. -/
private lemma zr_popPass_end {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) (Q : zr_Px k) (hbs : Q.b ≤ Q.s) :
    (zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t F))^[(Q.s - Q.b).toNat + 1] Q =
      (zr_popF t F)^[(Q.s - Q.b).toNat] Q := by
  obtain ⟨he, -, -, -, hb, hs⟩ := zr_pop_iter t F Q (Q.s - Q.b).toNat (by omega)
  rw [Function.iterate_succ_apply', he]
  exact if_pos (show ((zr_popF t F)^[(Q.s - Q.b).toNat] Q).s ≤
    ((zr_popF t F)^[(Q.s - Q.b).toNat] Q).b by rw [hs, hb]; omega)

/-- A pass that stops at the home ends, one stopping round after its fields run out, where its
rounds leave it. -/
private lemma zr_homePass_end {k : ℕ} (f : zr_Px k → zr_Px k) (Q : zr_Px k)
    (hi : ∀ m ≤ Q.i, (f^[m] Q).i = Q.i - m) :
    (zr_cNxt (fun P => P.i = 0) f)^[Q.i + 1] Q = f^[Q.i] Q := by
  rw [Function.iterate_succ_apply', zr_cNxt_iter _ f Q Q.i fun r hr => by rw [hi r hr.le]; omega]
  exact if_pos (show (f^[Q.i] Q).i = 0 by rw [hi _ le_rfl]; omega)

/-- The found path's stage after the descending right pass. -/
private abbrev zr_fpS1 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ1 t P) 0 (P.b + P.i)

/-- The found path's stage after the walk out: the outermost scanned field, the stack empty. -/
private abbrev zr_fpS2 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ1 t P) P.i P.b

/-- The found path's stage after the descending left pass. -/
private abbrev zr_fpS3 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ2 t P) 0 (P.b + P.i)

/-- The found path's stage after the home move. -/
private abbrev zr_fpS4 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ3 t P) 0 (P.b + P.i)

/-- The found path's stage after one mark popped. -/
private abbrev zr_fpS5 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ3 t P) 0 (P.b + P.i - 1)

/-- The found path's stage after the ascending right pass. -/
private abbrev zr_fpS6 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ4 t P) (P.i - 1) P.b

/-- The found path's stage after the right return. -/
private abbrev zr_fpS7 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ4 t P) 0 (P.b + P.i - 1)

/-- The found path's stage after the ascending left pass. -/
private abbrev zr_fpS8 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ5 t P) (P.i - 1) P.b

/-- The found path's stage after the left return. -/
private abbrev zr_fpS9 {k : ℕ} (t : Fin k) (P : zr_Px k) : zr_Px k :=
  zr_fpC t P (zr_fpZ5 t P) 0 P.b

/-- **The walk out ends at stage two**: `i₀ + 1` fields out, the marks popped. -/
private lemma zr_fp2 {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_fpV P) :
    (zr_woNxt t)^[((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat + 1] (zr_fpS1 t P) = zr_fpS2 t P := by
  obtain ⟨-, -, -, h1, -⟩ := hV
  rw [zr_popPass_end t (fun _ _ w => w) _ (by show P.b ≤ P.b + P.i; omega)]
  have hn : ((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat = P.i := by
    show (P.b + P.i - P.b).toNat = P.i
    omega
  obtain ⟨-, -, hi, hβ, hb, hs⟩ := zr_pop_iter t (fun _ _ w => w) (zr_fpS1 t P)
    ((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat (by omega)
  obtain ⟨hD, -⟩ := zr_px_iter t (fun _ _ w => w) (fun i => i + 1) (-1) (zr_fpS1 t P)
    ((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat
  refine zr_Px_ext ?_ ?_ hβ hb ?_
  · rw [show zr_popF t (fun _ _ w => w) = zr_pxNxt t (fun _ _ w => w) (fun i => i + 1) (-1)
      from rfl, hD, zr_pxFold_id, Function.update_eq_self]
  · rw [hi, hn]
    show 0 + P.i = P.i
    omega
  · rw [hs, hn]
    show P.b + P.i - P.i = P.b
    ring

/-- **The descending left pass ends at stage three**: back at the home, `i₀ + 1` marks pushed. -/
private lemma zr_fp3 {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_fpV P) :
    (zr_p2Nxt t)^[(zr_fpS2 t P).i - 1 + 1] (zr_fpS2 t P) = zr_fpS3 t P :=
  (zr_dnPass_end t (fun _ i w => zoneShiftOut false i w) (fun _ => zr_shiftOut_zero)
    (zr_fpS2 t P) hV.2.2.2.1).trans (zr_Px_ext (by
      show (⟨P.D.1, Function.update (Function.update P.D.2 t (zr_fpZ1 t P)) t
        ((List.range (P.i - 1)).reverse.foldl (fun a i => zoneShiftOut false (i + 1) a)
          (Function.update P.D.2 t (zr_fpZ1 t P) t))⟩ : ZoneData k) = _
      rw [Function.update_idem, Function.update_self]) rfl rfl rfl rfl)

/-- **The home move ends at stage four.** -/
private lemma zr_fp4 {k : ℕ} (t : Fin k) (P : zr_Px k) :
    zr_hmNxt t (zr_fpS3 t P) = zr_fpS4 t P := by
  refine zr_Px_ext ?_ rfl rfl rfl rfl
  show (⟨P.D.1, Function.update (Function.update P.D.2 t (zr_fpZ2 t P)) t
    (zoneMove true (Function.update P.D.2 t (zr_fpZ2 t P) t))⟩ : ZoneData k) = _
  rw [Function.update_idem, Function.update_self]

/-- **An ascending pass's end**: from the home with `n` marks, its rounds act at levels
`1, …, n` and end `n` fields out with the marks popped. -/
private lemma zr_upPass_end {k : ℕ} (t : Fin k)
    (g : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) (Q : zr_Px k) (hi : Q.i = 0)
    (hbs : Q.b ≤ Q.s) :
    (zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t fun ℓ i w => g ℓ (i + 1) w))^[(Q.s - Q.b).toNat + 1]
        Q =
      ⟨⟨Q.D.1, Function.update Q.D.2 t
        ((List.range (Q.s - Q.b).toNat).foldl (fun a i => g Q.D.1 (i + 1) a) (Q.D.2 t))⟩,
        (Q.s - Q.b).toNat, Q.β, Q.b, Q.b⟩ := by
  rw [zr_popPass_end t _ _ hbs]
  obtain ⟨-, -, hi', hβ, hb, hs⟩ := zr_pop_iter t (fun ℓ i w => g ℓ (i + 1) w) Q
    (Q.s - Q.b).toNat (by omega)
  obtain ⟨hD, -⟩ := zr_px_iter t (fun ℓ i w => g ℓ (i + 1) w) (fun i => i + 1) (-1) Q
    (Q.s - Q.b).toNat
  refine zr_Px_ext ?_ ?_ hβ hb ?_
  · rw [show zr_popF t (fun ℓ i w => g ℓ (i + 1) w) =
      zr_pxNxt t (fun ℓ i w => g ℓ (i + 1) w) (fun i => i + 1) (-1) from rfl, hD]
    congr 2
    unfold zr_pxFold
    rw [hi]
    exact zr_fold_asc (g Q.D.1) _ (Q.D.2 t)
  · rw [hi', hi, zero_add]
  · show _ = Q.b
    rw [hs]
    omega

/-- **The ascending right pass ends at stage six**: `i₀` fields out, the marks popped. -/
private lemma zr_fp6 {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_fpV P) :
    (zr_p3Nxt t)^[((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat + 1] (zr_fpS5 t P) = zr_fpS6 t P := by
  have hn : ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat = P.i - 1 := by
    show (P.b + P.i - 1 - P.b).toNat = P.i - 1
    have := hV.2.2.2.1
    omega
  refine (zr_upPass_end t (fun _ i w => zoneShiftIn true i w) _ rfl
    (by show P.b ≤ P.b + P.i - 1; have := hV.2.2.2.1; omega)).trans (zr_Px_ext ?_ hn rfl rfl rfl)
  show (⟨P.D.1, Function.update (Function.update P.D.2 t (zr_fpZ3 t P)) t
    ((List.range ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat).foldl
      (fun a i => zoneShiftIn true (i + 1) a) (Function.update P.D.2 t (zr_fpZ3 t P) t))⟩ :
      ZoneData k) = _
  rw [Function.update_idem, Function.update_self, hn]

/-- **The right return ends at stage seven**: at the home, `i₀` marks pushed. -/
private lemma zr_fp7 {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_fpV P) :
    (zr_rbNxt t)^[(zr_fpS6 t P).i + 1] (zr_fpS6 t P) = zr_fpS7 t P := by
  obtain ⟨-, -, -, h1, -⟩ := hV
  rw [zr_homePass_end _ _ fun m _ => (zr_dn_iter t _ _ m).2.1]
  obtain ⟨-, hi, hβ, hb, hs⟩ := zr_dn_iter t (fun _ _ w => w) (zr_fpS6 t P) (zr_fpS6 t P).i
  obtain ⟨hD, -⟩ := zr_px_iter t (fun _ _ w => w) (fun i => i - 1) 1 (zr_fpS6 t P)
    (zr_fpS6 t P).i
  refine zr_Px_ext ?_ ?_ hβ hb ?_
  · rw [show zr_dnF t (fun _ _ w => w) = zr_pxNxt t (fun _ _ w => w) (fun i => i - 1) 1 from rfl,
      hD, zr_pxFold_id, Function.update_eq_self]
  · rw [hi]
    show P.i - 1 - (P.i - 1) = 0
    omega
  · rw [hs]
    show P.b + ((P.i - 1 : ℕ) : ℤ) = P.b + P.i - 1
    omega

/-- **The ascending left pass ends at stage eight**: `i₀` fields out, the marks popped. -/
private lemma zr_fp8 {k : ℕ} (t : Fin k) {P : zr_Px k} (hV : zr_fpV P) :
    (zr_p4Nxt t)^[((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat + 1] (zr_fpS7 t P) = zr_fpS8 t P := by
  have hn : ((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat = P.i - 1 := by
    show (P.b + P.i - 1 - P.b).toNat = P.i - 1
    have := hV.2.2.2.1
    omega
  refine (zr_upPass_end t (fun _ i w => zoneShiftOut false i w) _ rfl
    (by show P.b ≤ P.b + P.i - 1; have := hV.2.2.2.1; omega)).trans (zr_Px_ext ?_ hn rfl rfl rfl)
  show (⟨P.D.1, Function.update (Function.update P.D.2 t (zr_fpZ4 t P)) t
    ((List.range ((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat).foldl
      (fun a i => zoneShiftOut false (i + 1) a) (Function.update P.D.2 t (zr_fpZ4 t P) t))⟩ :
      ZoneData k) = _
  rw [Function.update_idem, Function.update_self, hn]

/-- **The left return ends at stage nine**: at the home, the stack as the found path found it. -/
private lemma zr_fp9 {k : ℕ} (t : Fin k) (P : zr_Px k) :
    (zr_lbNxt t)^[(zr_fpS8 t P).i + 1] (zr_fpS8 t P) = zr_fpS9 t P := by
  obtain ⟨he, -, hi, hβ, hb, hs⟩ := zr_lb_iter t (zr_fpS8 t P) (zr_fpS8 t P).i le_rfl
  rw [zr_homePass_end _ _ fun m hm => (zr_lb_iter t _ m hm).2.2.1]
  obtain ⟨hD, -⟩ := zr_px_iter t (fun _ _ w => w) (fun i => i - 1) 0 (zr_fpS8 t P)
    (zr_fpS8 t P).i
  refine zr_Px_ext ?_ ?_ hβ hb ?_
  · rw [hD, zr_pxFold_id, Function.update_eq_self]
  · rw [hi]
    show P.i - 1 - (P.i - 1) = 0
    omega
  · exact hs

/-- Decidable equality of a loop host's states from its body's. -/
private def zr_decHost {B : Type} (h : DecidableEq B) : DecidableEq (Σ b, zr_hostPh B b) := by
  letI : ∀ b, DecidableEq (zr_hostPh B b) := fun b => match b with
    | false => inferInstanceAs (DecidableEq (Option Bool))
    | true => h
  exact inferInstance

/-- **The found path's head box**: the zoned head within `zoneStart (i₀ + 1)` of home, scratch
from two cells below the stack's base to `9 · 2^(i₀ + 1) + 11` above it. -/
private abbrev zr_fpL {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (-(zoneStart P.i : ℤ)) (P.b - 2)

/-- The found path's head box, its upper corner. -/
private abbrev zr_fpU {k : ℕ} (P : zr_Px k) : Fin 2 → ℤ :=
  zr_heads (zoneStart P.i) (P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11)

/-- The found path's layout facts: the scanned zone's field and its neighbours, and the sizes
the passes' boxes are stated in. -/
private lemma zr_fp_facts {k : ℕ} {P : zr_Px k} (hV : zr_fpV P) :
    zr_rstart 0 = 0 ∧ zr_lstart 0 = 0 ∧ zr_rstart P.i = zoneStart (P.i - 1) ∧
      (zoneStart P.i : ℤ) = zoneStart (P.i - 1) + ((2 ^ P.i : ℕ) : ℤ) + 1 ∧
      zr_lstart P.i = -((zoneStart P.i : ℤ) - 2) ∧ (5 : ℤ) ≤ zoneStart P.i ∧
      (P.i : ℤ) ≤ ((2 ^ P.i : ℕ) : ℤ) ∧ ((2 ^ P.i : ℕ) : ℤ) = 2 * ((2 ^ (P.i - 1) : ℕ) : ℤ) ∧
      (1 ≤ P.i - 1 → ((2 ^ (P.i - 1) : ℕ) : ℤ) = 2 * ((2 ^ (P.i - 1 - 1) : ℕ) : ℤ)) ∧
      0 ≤ zr_rstart (P.i - 1) ∧ zr_rstart (P.i - 1) ≤ zr_rstart P.i ∧
      zr_lstart P.i ≤ zr_lstart (P.i - 1) := by
  obtain ⟨-, -, -, h1, -⟩ := hV
  have r0 : zr_rstart 0 = 0 := by rw [zr_rstart, if_pos rfl]
  have rP : zr_rstart P.i = zoneStart (P.i - 1) := by rw [zr_rstart, if_neg (by omega)]
  have p1 : (2 : ℕ) ^ P.i = 2 * 2 ^ (P.i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have zs : zoneStart P.i = zoneStart (P.i - 1) + 2 ^ P.i + 1 := by
    have := zoneStart_succ (P.i - 1)
    rw [show P.i - 1 + 1 = P.i by omega, zoneCapacity_eq, ← p1] at this
    exact this
  have z1 := zoneStart_mono (show 1 ≤ P.i from h1)
  have z1' : zoneStart 1 = 5 := by norm_num [zoneStart_eq]
  refine ⟨r0, zr_lstart_zero, rP, by rw [zs]; push_cast; ring, ?_, by
    rw [z1'] at z1
    exact_mod_cast z1, by exact_mod_cast (Nat.lt_two_pow_self).le, by rw [p1]; push_cast; ring,
    fun h => by
      rw [show (2 : ℕ) ^ (P.i - 1) = 2 * 2 ^ (P.i - 1 - 1) by rw [← pow_succ']; congr 1; omega]
      push_cast
      ring, ?_, zr_rstart_mono (by omega), zr_lstart_anti (by omega)⟩
  · rw [zr_lstart, rP, zs]
    push_cast
    ring
  · have := zr_rstart_mono (Nat.zero_le (P.i - 1))
    rwa [r0] at this

/-- The found path's opening gap: scratch one cell right, past the scan's count, to the stack's
base. -/
private def zr_fpG0 {k : ℕ} (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV zr_pT zr_pT (fun P => zr_heads (zr_rstart P.i) (P.b - 1)) zr_rH _
    zr_fpL zr_fpU from
  zr_seg (zr_pinCell_step (x := x) zr_fpV 1 1 none zr_pT fun P =>
      zr_heads (zr_rstart P.i) (P.b - 1)) (fun _ _ => rfl) fun P hV => by
    obtain ⟨-, -, rP, zs, -, -, hi2, -, -, -, -, -⟩ := zr_fp_facts hV
    have hs := hV.2.2.1
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · rw [zr_heads_set1, SignType.coe_one]
      show zr_heads _ (P.b - 1 + 1) = zr_heads _ P.s
      rw [sub_add_cancel, hs]
    all_goals simp only [zr_heads, zr_fpL, zr_fpU, Function.update_self, if_true,
      show (1 : Fin 2) ≠ 0 by decide, if_false,
      Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), SignType.coe_one]
    all_goals omega

/-- The found path's descending right pass, from the start to stage one. -/
private noncomputable def zr_fpG1 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV zr_pT (fun P => zr_pT (zr_fpS1 t P)) zr_rH
    (fun P => zr_lH (zr_fpS1 t P)) _ zr_fpL zr_fpU from
  zr_seg (zr_PinStep_re (zr_p1Pass t x).step (fun P => P) zr_fpV fun _ h => ⟨h.1, h.2.2.2.1⟩)
    (fun P hV => by
      show zr_pT ((zr_p1Nxt t)^[P.i - 1 + 1] P) = _
      rw [zr_fp1 t hV]) fun P hV => by
    obtain ⟨r0, l0, rP, zs, -, -, hi2, p2, p3, -, -, -⟩ := zr_fp_facts hV
    have hs := hV.2.2.1
    have h1 := hV.2.2.2.1
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_rH ((zr_p1Nxt t)^[P.i - 1 + 1] P) = _
      rw [zr_fp1 t hV]
      show zr_heads (zr_rstart 0) _ = zr_heads (zr_lstart 0) _
      rw [r0, l0]
    · show -(zoneStart P.i : ℤ) ≤ -1
      omega
    · show P.b - 2 ≤ P.s
      omega
    · show (if P.i = 1 then zr_rstart P.i else zr_rstart P.i + 4 * (zr_hh (zr_p1G P) : ℤ)) ≤
        zoneStart P.i
      have hh : (zr_hh (zr_p1G P) : ℤ) = ((2 ^ (P.i - 1 - 1) : ℕ) : ℤ) := rfl
      split_ifs with h
      · omega
      · have := p3 (by omega)
        omega
    · show P.s + P.i + 8 * ((2 ^ P.i : ℕ) : ℤ) + 3 ≤ P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      omega

/-- The found path's walk out, from stage one to stage two. -/
private noncomputable def zr_fpG2 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS1 t P)) (fun P => zr_pT (zr_fpS2 t P))
    (fun P => zr_lH (zr_fpS1 t P)) (fun P => zr_lH (zr_fpS2 t P)) _ zr_fpL zr_fpU from
  zr_seg (zr_PinStep_re (zr_woPass t x).step (zr_fpS1 t) zr_fpV fun P h => by
      obtain ⟨⟨hi, -, hβ⟩, hβ1, -, h1, hl⟩ := h
      refine ⟨⟨Nat.zero_le _, show P.b ≤ P.b + P.i by omega, hβ⟩, hβ1, ?_⟩
      show (0 : ℤ) + (P.b + P.i - P.b) + 0 ≤ P.D.1
      omega)
    (fun P hV => by
      show zr_pT ((zr_woNxt t)^[((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat + 1] (zr_fpS1 t P)) = _
      rw [zr_fp2 t hV]) fun P hV => by
    obtain ⟨r0, l0, rP, zs, lP, z5, hi2, p2, p3, -, -, -⟩ := zr_fp_facts hV
    have hn : ((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat = P.i := by
      show (P.b + P.i - P.b).toNat = P.i
      omega
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_lH ((zr_woNxt t)^[((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat + 1] (zr_fpS1 t P)) = _
      rw [zr_fp2 t hV]
    · show -(zoneStart P.i : ℤ) ≤ zr_lstart (0 + ((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat) - 1
      rw [hn, zero_add]
      omega
    · show P.b - 2 ≤ P.b - 2
      exact le_rfl
    · show zr_lstart 0 + 1 ≤ zoneStart P.i
      omega
    · show P.b + P.i + 1 ≤ P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      omega

/-- The found path's descending left pass, from stage two to stage three. -/
private noncomputable def zr_fpG3 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS2 t P)) (fun P => zr_pT (zr_fpS3 t P))
    (fun P => zr_lH (zr_fpS2 t P)) (fun P => zr_heads 0 (zr_fpS3 t P).s) _ zr_fpL zr_fpU from
  zr_seg (zr_PinStep_re (zr_p2Pass t x).step (zr_fpS2 t) zr_fpV fun P h => by
      obtain ⟨⟨hi, -, hβ⟩, -, -, h1, hl⟩ := h
      exact ⟨⟨hl, le_refl P.b, hβ⟩, h1⟩)
    (fun P hV => by
      show zr_pT ((zr_p2Nxt t)^[(zr_fpS2 t P).i - 1 + 1] (zr_fpS2 t P)) = _
      rw [zr_fp3 t hV]) fun P hV => by
    obtain ⟨r0, l0, rP, zs, lP, z5, hi2, p2, p3, -, -, -⟩ := zr_fp_facts hV
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_lH ((zr_p2Nxt t)^[(zr_fpS2 t P).i - 1 + 1] (zr_fpS2 t P)) = _
      rw [zr_fp3 t hV]
      show zr_heads (zr_lstart 0) _ = _
      rw [l0]
    · show -(zoneStart P.i : ℤ) ≤ zr_lstart P.i - 2
      omega
    · show P.b - 2 ≤ P.b
      omega
    · show (2 : ℤ) ≤ zoneStart P.i
      omega
    · show P.b + P.i + 6 * ((2 ^ P.i : ℕ) : ℤ) + 4 ≤ P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      omega

/-- The found path's home move, from stage three to stage four. -/
private noncomputable def zr_fpG4 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS3 t P)) (fun P => zr_pT (zr_fpS4 t P))
    (fun P => zr_heads 0 (zr_fpS3 t P).s) (fun P => zr_heads 0 (zr_fpS4 t P).s) _ zr_fpL
    zr_fpU from
  zr_seg (zr_PinStep_re (zr_hmContract_step t x) (zr_fpS3 t) zr_fpV fun P h => by
      obtain ⟨⟨hi, -, hβ⟩, -, -, h1, hl⟩ := h
      exact ⟨⟨Nat.zero_le _, show P.b ≤ P.b + P.i by omega, hβ⟩, show 0 < P.D.1 by omega⟩)
    (fun P _ => by
      show zr_pT (zr_hmNxt t (zr_fpS3 t P)) = _
      rw [zr_fp4]) fun P hV => by
    obtain ⟨-, -, -, -, -, z5, hi2, -, -, -, -, -⟩ := zr_fp_facts hV
    refine ⟨rfl, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show -(zoneStart P.i : ℤ) ≤ -4
      omega
    · show P.b - 2 ≤ P.b + P.i - 1
      omega
    · show (4 : ℤ) ≤ zoneStart P.i
      omega
    · show P.b + P.i + 11 ≤ P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      omega

/-- The found path's single pop, from stage four to stage five. -/
private def zr_fpG5 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS4 t P)) (fun P => zr_pT (zr_fpS5 t P))
    (fun P => zr_heads 0 (zr_fpS4 t P).s) (fun P => zr_rH (zr_fpS5 t P)) _ zr_fpL zr_fpU from
  zr_seg (zr_segRe (zr_popSeg x (fun P => zr_pxV P ∧ P.b < P.s) (fun _ => 0) fun _ h => h)
      (zr_fpS4 t) zr_fpV fun P h => by
        obtain ⟨⟨hi, -, hβ⟩, -, -, h1, hl⟩ := h
        exact ⟨⟨Nat.zero_le _, show P.b ≤ P.b + P.i by omega, hβ⟩,
          show P.b < P.b + P.i by omega⟩).step
    (fun _ _ => rfl) fun P hV => by
    obtain ⟨r0, -, -, -, -, z5, hi2, -, -, -, -, -⟩ := zr_fp_facts hV
    have h1 := hV.2.2.2.1
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_heads 0 (P.b + P.i - 1) = zr_heads (zr_rstart 0) (P.b + P.i - 1)
      rw [r0]
    · show -(zoneStart P.i : ℤ) ≤ 0
      omega
    · show P.b - 2 ≤ P.b + P.i - 1
      omega
    · show (0 : ℤ) ≤ zoneStart P.i
      omega
    · show P.b + P.i ≤ P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      omega

/-- The found path's ascending right pass, from stage five to stage six. -/
private noncomputable def zr_fpG6 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS5 t P)) (fun P => zr_pT (zr_fpS6 t P))
    (fun P => zr_rH (zr_fpS5 t P)) (fun P => zr_rH (zr_fpS6 t P)) _ zr_fpL zr_fpU from
  zr_seg (zr_PinStep_re (zr_p3Pass t x).step (zr_fpS5 t) zr_fpV fun P h => by
      obtain ⟨⟨hi, -, hβ⟩, hβ1, -, h1, hl⟩ := h
      refine ⟨⟨Nat.zero_le _, show P.b ≤ P.b + P.i - 1 by omega, hβ⟩, hβ1, ?_⟩
      show (0 : ℤ) + (P.b + P.i - 1 - P.b) + 1 ≤ P.D.1
      omega)
    (fun P hV => by
      show zr_pT ((zr_p3Nxt t)^[((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat + 1] (zr_fpS5 t P)) = _
      rw [zr_fp6 t hV]) fun P hV => by
    obtain ⟨r0, l0, rP, zs, lP, z5, hi2, p2, p3, -, -, -⟩ := zr_fp_facts hV
    have h1 := hV.2.2.2.1
    have hn : ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat = P.i - 1 := by
      show (P.b + P.i - 1 - P.b).toNat = P.i - 1
      omega
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_rH ((zr_p3Nxt t)^[((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat + 1] (zr_fpS5 t P)) = _
      rw [zr_fp6 t hV]
    · show -(zoneStart P.i : ℤ) ≤ zr_rstart 0 - 1
      omega
    · show P.b - 2 ≤ P.b - 2
      exact le_rfl
    · show (if ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat = 0 then zr_rstart 0 + 1 else
        zr_rstart (0 + ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat + 1) +
          4 * ((2 ^ (0 + ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat - 1) : ℕ) : ℤ)) ≤
        zoneStart P.i
      rw [hn, zero_add, show P.i - 1 + 1 = P.i by omega]
      split_ifs with h
      · omega
      · have := p3 (by omega)
        omega
    · show P.b + P.i - 1 + 8 * ((2 ^ (0 + ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat) : ℕ) : ℤ) + 1 ≤
        P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      rw [hn, zero_add]
      omega

/-- The found path's right return, from stage six to stage seven. -/
private noncomputable def zr_fpG7 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS6 t P)) (fun P => zr_pT (zr_fpS7 t P))
    (fun P => zr_rH (zr_fpS6 t P)) (fun P => zr_lH (zr_fpS7 t P)) _ zr_fpL zr_fpU from
  zr_seg (zr_PinStep_re (zr_rbPass t x).step (zr_fpS6 t) zr_fpV fun P h => by
      obtain ⟨⟨hi, -, hβ⟩, -, -, h1, hl⟩ := h
      exact ⟨show P.i - 1 ≤ P.D.1 by omega, le_refl P.b, hβ⟩)
    (fun P hV => by
      show zr_pT ((zr_rbNxt t)^[(zr_fpS6 t P).i + 1] (zr_fpS6 t P)) = _
      rw [zr_fp7 t hV]) fun P hV => by
    obtain ⟨r0, l0, rP, zs, lP, z5, hi2, p2, p3, r1, rm, -⟩ := zr_fp_facts hV
    have h1 := hV.2.2.2.1
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_rH ((zr_rbNxt t)^[(zr_fpS6 t P).i + 1] (zr_fpS6 t P)) = _
      rw [zr_fp7 t hV]
      show zr_heads (zr_rstart 0) _ = zr_heads (zr_lstart 0) _
      rw [r0, l0]
    · show -(zoneStart P.i : ℤ) ≤ -1
      omega
    · show P.b - 2 ≤ P.b - 1
      omega
    · show (if P.i - 1 = 0 then (1 : ℤ) else
        zr_rstart (P.i - 1) + 4 * ((2 ^ (P.i - 1 - 1 - 1) : ℕ) : ℤ)) ≤ zoneStart P.i
      split_ifs with h
      · omega
      · have h3 := p3 (by omega)
        have h4 : ((2 ^ (P.i - 1 - 1 - 1) : ℕ) : ℤ) ≤ ((2 ^ (P.i - 1 - 1) : ℕ) : ℤ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · show P.b + (P.i - 1 : ℕ) + 8 * ((2 ^ (P.i - 1) : ℕ) : ℤ) + 3 ≤
        P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      omega

/-- The found path's ascending left pass, from stage seven to stage eight. -/
private noncomputable def zr_fpG8 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS7 t P)) (fun P => zr_pT (zr_fpS8 t P))
    (fun P => zr_lH (zr_fpS7 t P)) (fun P => zr_lH (zr_fpS8 t P)) _ zr_fpL zr_fpU from
  zr_seg (zr_PinStep_re (zr_p4Pass t x).step (zr_fpS7 t) zr_fpV fun P h => by
      obtain ⟨⟨hi, -, hβ⟩, hβ1, -, h1, hl⟩ := h
      refine ⟨⟨Nat.zero_le _, show P.b ≤ P.b + P.i - 1 by omega, hβ⟩, hβ1, ?_⟩
      show (0 : ℤ) + (P.b + P.i - 1 - P.b) + 1 ≤ P.D.1
      omega)
    (fun P hV => by
      show zr_pT ((zr_p4Nxt t)^[((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat + 1] (zr_fpS7 t P)) = _
      rw [zr_fp8 t hV]) fun P hV => by
    obtain ⟨r0, l0, rP, zs, lP, z5, hi2, p2, p3, -, -, -⟩ := zr_fp_facts hV
    have h1 := hV.2.2.2.1
    have hn : ((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat = P.i - 1 := by
      show (P.b + P.i - 1 - P.b).toNat = P.i - 1
      omega
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_lH ((zr_p4Nxt t)^[((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat + 1] (zr_fpS7 t P)) = _
      rw [zr_fp8 t hV]
    · show -(zoneStart P.i : ℤ) ≤ zr_lstart (0 + ((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat + 1) - 2
      rw [hn, zero_add, show P.i - 1 + 1 = P.i by omega]
      omega
    · show P.b - 2 ≤ P.b - 2
      exact le_rfl
    · show zr_lstart 0 + ((2 ^ 0 : ℕ) : ℤ) + 1 ≤ zoneStart P.i
      rw [l0]
      norm_num
      omega
    · show P.b + P.i - 1 + 6 * ((2 ^ (0 + ((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat) : ℕ) : ℤ) + 3 ≤
        P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      rw [hn, zero_add]
      omega

/-- The found path's left return, from stage eight to stage nine. -/
private noncomputable def zr_fpG9 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS8 t P)) (fun P => zr_pT (zr_fpS9 t P))
    (fun P => zr_lH (zr_fpS8 t P)) (fun P => zr_heads 0 P.b) _ zr_fpL zr_fpU from
  zr_seg (zr_PinStep_re (zr_lbPass t x).step (zr_fpS8 t) zr_fpV fun P h => by
      obtain ⟨⟨hi, -, hβ⟩, -, -, h1, hl⟩ := h
      exact ⟨show P.i - 1 ≤ P.D.1 by omega, le_refl P.b, hβ⟩)
    (fun P _ => by
      show zr_pT ((zr_lbNxt t)^[(zr_fpS8 t P).i + 1] (zr_fpS8 t P)) = _
      rw [zr_fp9 t P]) fun P hV => by
    obtain ⟨r0, l0, rP, zs, lP, z5, hi2, p2, p3, -, -, lm⟩ := zr_fp_facts hV
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · show zr_lH ((zr_lbNxt t)^[(zr_fpS8 t P).i + 1] (zr_fpS8 t P)) = _
      rw [zr_fp9 t P]
      show zr_heads (zr_lstart 0) _ = _
      rw [l0]
    · show -(zoneStart P.i : ℤ) ≤ zr_lstart (P.i - 1) - 1
      omega
    · show P.b - 2 ≤ P.b - 1
      omega
    · show (1 : ℤ) ≤ zoneStart P.i
      omega
    · show P.b + 1 ≤ P.b + 9 * ((2 ^ P.i : ℕ) : ℤ) + 11
      omega

/-- The found path's closing gap: scratch one cell left, back to the scan's count's end. -/
private def zr_fpG10 {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ zr_fpV (fun P => zr_pT (zr_fpS9 t P)) (fun P => zr_pT (zr_fpS9 t P))
    (fun P => zr_heads 0 P.b) (fun P => zr_heads 0 (P.b - 1)) _ zr_fpL zr_fpU from
  zr_seg (zr_pinCell_step (x := x) zr_fpV 1 (-1) none (fun P => zr_pT (zr_fpS9 t P))
      fun P => zr_heads 0 P.b) (fun _ _ => rfl) fun P hV => by
    obtain ⟨-, -, -, -, -, z5, hi2, -, -, -, -, -⟩ := zr_fp_facts hV
    refine ⟨?_, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · rw [zr_heads_set1, SignType.coe_neg_one, ← sub_eq_add_neg]
      rfl
    all_goals simp only [zr_heads, zr_fpL, zr_fpU, Function.update_self, if_true,
      show (1 : Fin 2) ≠ 0 by decide, if_false,
      Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), SignType.coe_neg_one]
    all_goals omega

/-- **The found path**, as one pinned segment: the opening gap, the descending passes on both
sides, the home move, a pop, the ascending passes on both sides with their returns, and the
closing gap, from the scanned zone's field and the scan's count to the home and the count's
end, track `t` cascaded. -/
private noncomputable def zr_fpSeg {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  letI : DecidableEq (zr_stOf (zr_p1Pass t x).C) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  letI : DecidableEq (zr_stOf (zr_woPass t x).C) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  letI : DecidableEq (zr_stOf (zr_p2Pass t x).C) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  letI : DecidableEq (zr_stOf (zr_hmContract t x)) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  letI : DecidableEq (zr_stOf (zr_p3Pass t x).C) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  letI : DecidableEq (zr_stOf (zr_rbPass t x).C) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  letI : DecidableEq (zr_stOf (zr_p4Pass t x).C) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  letI : DecidableEq (zr_stOf (zr_lbPass t x).C) := zr_decHost (by
    repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | exact inferInstance))
  zr_segSeq (zr_fpG0 x) <| zr_segSeq (zr_fpG1 t x) <| zr_segSeq (zr_fpG2 t x) <|
    zr_segSeq (zr_fpG3 t x) <| zr_segSeq (zr_fpG4 t x) <| zr_segSeq (zr_fpG5 t x) <|
    zr_segSeq (zr_fpG6 t x) <| zr_segSeq (zr_fpG7 t x) <| zr_segSeq (zr_fpG8 t x) <|
    zr_segSeq (zr_fpG9 t x) (zr_fpG10 t x)

/-- **The found path computes the cascade**: its last stage holds track `t` cascaded to the right
at the scanned index `P.i - 1`, every other track kept. -/
private lemma zr_fp_data {k : ℕ} (t : Fin k) (P : zr_Px k) :
    (zr_fpS9 t P).D.2 = Function.update P.D.2 t (zoneCascadeRight (P.i - 1) (P.D.2 t)) := by
  show Function.update P.D.2 t (zr_fpZ5 t P) = _
  rw [zr_cascade_passes]

/-- A pinned segment's time, read off its type. -/
private abbrev zr_tauOf {k : ℕ} {S J : Type} {x : List (ZoneSym k)}
    {M : MultiTapeTM 2 (ZoneSym k) S} {e d : S} {V : J → Prop}
    {T₁ T₂ : J → Fin 2 → ℤ → Option (ZoneSym k)} {p₁ p₂ : J → Fin 2 → ℤ} {τ : J → ℕ}
    {L U : J → Fin 2 → ℤ} (_ : zr_PinSeg x M e d V T₁ T₂ p₁ p₂ τ L U) : J → ℕ :=
  τ

/-- Rounds bounded by `a · 2^(N - m) + b`, from the top down: their bounds sum, with the last
round's power, to `a · 2^(N + 1) + b (n + 1)`. -/
private lemma zr_sum_desc_eq (a b N n : ℕ) (hn : n ≤ N) :
    ∑ m ∈ Finset.range (n + 1), (a * 2 ^ (N - m) + b) + a * 2 ^ (N - n) =
      a * 2 ^ (N + 1) + b * (n + 1) := by
  induction n with
  | zero =>
    rw [zero_add, Finset.sum_range_one, Nat.sub_zero, pow_succ]
    ring
  | succ n ih =>
    have h := ih (by omega)
    have e : 2 ^ (N - n) = 2 * 2 ^ (N - (n + 1)) := by
      rw [show N - n = N - (n + 1) + 1 by omega, pow_succ]
      ring
    rw [e] at h
    rw [Finset.sum_range_succ]
    linarith

/-- Rounds bounded by `a · 2^(m + c) + b`, from the bottom up: their bounds sum, with `a · 2^c`,
to `a · 2^(n + 1 + c) + b (n + 1)`. -/
private lemma zr_sum_asc_eq (a b c n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (a * 2 ^ (m + c) + b) + a * 2 ^ c =
      a * 2 ^ (n + 1 + c) + b * (n + 1) := by
  induction n with
  | zero =>
    rw [zero_add, Finset.sum_range_one, zero_add, pow_add, pow_one]
    ring
  | succ n ih =>
    have e : 2 ^ (n + 1 + 1 + c) = 2 * 2 ^ (n + 1 + c) := by
      rw [show n + 1 + 1 + c = n + 1 + c + 1 by ring, pow_succ]
      ring
    rw [Finset.sum_range_succ, e]
    linarith

/-- **A descending pass's time**: rounds bounded by `a · 2^(N - m) + b` sum to at most
`2a · 2^N + b (n + 1)`. -/
private lemma zr_time_desc (f : ℕ → ℕ) (a b N n : ℕ) (hn : n ≤ N)
    (hf : ∀ m ≤ n, f m ≤ a * 2 ^ (N - m) + b) :
    ∑ m ∈ Finset.range (n + 1), f m ≤ 2 * a * 2 ^ N + b * (n + 1) := by
  have h := zr_sum_desc_eq a b N n hn
  have h2 : a * 2 ^ (N + 1) = 2 * a * 2 ^ N := by ring
  have hs : ∑ m ∈ Finset.range (n + 1), f m ≤ ∑ m ∈ Finset.range (n + 1), (a * 2 ^ (N - m) + b) :=
    Finset.sum_le_sum fun m hm => hf m (by rw [Finset.mem_range] at hm; omega)
  omega

/-- **An ascending pass's time**: rounds bounded by `a · 2^(m + c) + b` sum to at most
`2a · 2^(n + c) + b (n + 1)`. -/
private lemma zr_time_asc (f : ℕ → ℕ) (a b c n : ℕ)
    (hf : ∀ m ≤ n, f m ≤ a * 2 ^ (m + c) + b) :
    ∑ m ∈ Finset.range (n + 1), f m ≤ 2 * a * 2 ^ (n + c) + b * (n + 1) := by
  have h := zr_sum_asc_eq a b c n
  have h2 : a * 2 ^ (n + 1 + c) = 2 * a * 2 ^ (n + c) := by ring
  have hs : ∑ m ∈ Finset.range (n + 1), f m ≤ ∑ m ∈ Finset.range (n + 1), (a * 2 ^ (m + c) + b) :=
    Finset.sum_le_sum fun m hm => hf m (by rw [Finset.mem_range] at hm; omega)
  omega

/-- Every right field has at most `2^m` cells. -/
private lemma zr_rfield_le {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) :
    (zr_rfield z m).length ≤ 2 ^ m := by
  by_cases hm : m ≤ ℓ
  · rw [zr_rfield_length z m hm]
  · rw [zr_rfield, if_neg (by omega), dif_neg (by omega), List.length_nil]
    exact Nat.zero_le _

/-- Every left field has at most `2^m` cells. -/
private lemma zr_lfield_le {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) (m : ℕ) :
    (zr_lfield z m).length ≤ 2 ^ m := by
  rw [zr_lfield, List.length_reverse]
  exact zr_rfield_le _ m

/-- The shift half-capacity one level below a field: at most a quarter of the field's power,
plus one. -/
private lemma zr_hh_le (i : ℕ) : 4 * 2 ^ (i - 1 - 1) ≤ 2 ^ i + 4 := by
  rcases Nat.lt_or_ge i 2 with h | h
  · rw [show i - 1 - 1 = 0 by omega, pow_zero]
    have := Nat.two_pow_pos i
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rw [show j + 2 - 1 - 1 = j by omega, pow_succ, pow_succ]
    omega

/-- The descending right pass's round time is at most `20 · 2^i + 170`. -/
private lemma zr_p1Tau_le {k : ℕ} (t : Fin k) (P : zr_Px k) :
    zr_p1Tau t P ≤ 20 * 2 ^ P.i + 170 := by
  have h1 := zr_rfield_le P.D.2 (P.i - 1)
  have h2 : 2 ^ (P.i - 1) ≤ 2 ^ P.i := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := zr_hh_le P.i
  have hh : zr_hh (zr_p1G P) = 2 ^ (P.i - 1 - 1) := rfl
  simp only [zr_p1Tau, hh]
  split_ifs <;> omega

/-- The walk out's round time is at most `2 · 2^i + 11`. -/
private lemma zr_woTau_le {k : ℕ} (P : zr_Px k) : zr_woTau P ≤ 2 * 2 ^ P.i + 11 := by
  have h1 := zr_lfield_le P.D.2 (P.i + 1)
  rw [pow_succ] at h1
  simp only [zr_woTau, zr_woRun]
  split_ifs <;> omega

/-- The descending left pass's round time is at most `25 · 2^i + 260`. -/
private lemma zr_p2Tau_le {k : ℕ} (t : Fin k) (P : zr_Px k) :
    zr_p2Tau t P ≤ 25 * 2 ^ P.i + 260 := by
  have h1 := zr_lfield_le P.D.2 P.i
  have h3 := zr_hh_le P.i
  have hh : zr_hh (zr_p1G P) = 2 ^ (P.i - 1 - 1) := rfl
  simp only [zr_p2Tau, hh]
  split_ifs <;> omega

/-- The ascending right pass's round time is at most `77 · 2^i + 89`. -/
private lemma zr_p3Tau_le {k : ℕ} (t : Fin k) (P : zr_Px k) :
    zr_p3Tau t P ≤ 77 * 2 ^ P.i + 89 := by
  have h1 := zr_rfield_le P.D.2 P.i
  have hh : zr_hh (zr_popG P) = 2 ^ P.i := by
    show 2 ^ (P.i + 1 - 1) = 2 ^ P.i
    rw [Nat.add_sub_cancel]
  simp only [zr_p3Tau, hh]
  split_ifs <;> omega

/-- The ascending left pass's round time is at most `95 · 2^i + 170`. -/
private lemma zr_p4Tau_le {k : ℕ} (t : Fin k) (P : zr_Px k) :
    zr_p4Tau t P ≤ 95 * 2 ^ P.i + 170 := by
  have h1 := zr_lfield_le P.D.2 (P.i + 1)
  rw [pow_succ] at h1
  have hh : zr_hh (zr_popG P) = 2 ^ P.i := by
    show 2 ^ (P.i + 1 - 1) = 2 ^ P.i
    rw [Nat.add_sub_cancel]
  simp only [zr_p4Tau, zr_woRun, hh]
  split_ifs <;> omega

/-- The right return's round time is at most `2^i + 9`. -/
private lemma zr_rbTau_le {k : ℕ} (P : zr_Px k) : zr_rbTau P ≤ 2 ^ P.i + 9 := by
  have h1 := zr_rfield_le P.D.2 (P.i - 1)
  have h2 : 2 ^ (P.i - 1) ≤ 2 ^ P.i := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [zr_rbTau]
  split_ifs <;> omega

/-- The left return's round time is at most `2^i + 5`. -/
private lemma zr_lbTau_le {k : ℕ} (P : zr_Px k) : zr_lbTau P ≤ 2 ^ P.i + 5 := by
  have h1 := zr_lfield_le P.D.2 P.i
  simp only [zr_lbTau]
  split_ifs <;> omega

/-- **A descending pass's time**: rounds at fields `Q.i, Q.i - 1, …`, each at most
`a · 2^i + b` plus the round's two dispatch steps. -/
private lemma zr_pass_time_desc {k : ℕ} (τ : zr_Px k → ℕ) (nxt : zr_Px k → zr_Px k)
    (Q : zr_Px k) (a b n : ℕ) (hn : n ≤ Q.i) (hτ : ∀ R, τ R ≤ a * 2 ^ R.i + b)
    (hi : ∀ m ≤ n, (nxt^[m] Q).i = Q.i - m) :
    ∑ m ∈ Finset.range (n + 1), (τ (nxt^[m] Q) + 2) ≤ 2 * a * 2 ^ Q.i + (b + 2) * (n + 1) :=
  zr_time_desc _ a (b + 2) Q.i n hn fun m hm => by
    have h := hτ (nxt^[m] Q)
    rw [hi m hm] at h
    omega

/-- **An ascending pass's time**: rounds at fields `Q.i, Q.i + 1, …`, each at most
`a · 2^i + b` plus the round's two dispatch steps. -/
private lemma zr_pass_time_asc {k : ℕ} (τ : zr_Px k → ℕ) (nxt : zr_Px k → zr_Px k)
    (Q : zr_Px k) (a b n : ℕ) (hτ : ∀ R, τ R ≤ a * 2 ^ R.i + b)
    (hi : ∀ m ≤ n, (nxt^[m] Q).i = Q.i + m) :
    ∑ m ∈ Finset.range (n + 1), (τ (nxt^[m] Q) + 2) ≤ 2 * a * 2 ^ (n + Q.i) + (b + 2) * (n + 1) :=
  zr_time_asc _ a (b + 2) Q.i n fun m hm => by
    have h := hτ (nxt^[m] Q)
    rw [hi m hm, Nat.add_comm Q.i m] at h
    omega

/-- A pop pass's rounds, while marks remain, step one field out each. -/
private lemma zr_pop_fields {k : ℕ} (t : Fin k)
    (F : (ℓ : ℕ) → ℕ → ZoneContents ℓ → ZoneContents ℓ) (Q : zr_Px k) (hbs : Q.b ≤ Q.s) :
    ∀ m ≤ (Q.s - Q.b).toNat,
      ((zr_cNxt (fun P => P.s ≤ P.b) (zr_popF t F))^[m] Q).i = Q.i + m := fun m hm => by
  obtain ⟨he, -, hi, -⟩ := zr_pop_iter t F Q m (by omega)
  rw [he, hi]

/-- **The found path's time**: at most `1000 · 2^(i₀ + 1) + 200` steps. -/
private lemma zr_fpSeg_time {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) {P : zr_Px k}
    (hV : zr_fpV P) : zr_tauOf (zr_fpSeg t x) P ≤ 1000 * 2 ^ P.i + 200 := by
  have h1i := hV.2.2.2.1
  have hP : P.i < 2 ^ P.i := Nat.lt_two_pow_self
  have hp : 2 ^ P.i = 2 * 2 ^ (P.i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have g1 := zr_pass_time_desc (zr_p1Tau t) (zr_p1Nxt t) P 20 170 (P.i - 1) (by omega)
    (zr_p1Tau_le t) fun m _ => (zr_dn_iter t (fun _ i w => zoneShiftIn true (i - 1) w) P m).2.1
  have g2 := zr_pass_time_asc zr_woTau (zr_woNxt t) (zr_fpS1 t P) 2 11
    ((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat zr_woTau_le
    (zr_pop_fields t _ _ (by show P.b ≤ P.b + P.i; omega))
  have g3 := zr_pass_time_desc (zr_p2Tau t) (zr_p2Nxt t) (zr_fpS2 t P) 25 260
    ((zr_fpS2 t P).i - 1) (by omega) (zr_p2Tau_le t)
    fun m _ => (zr_dn_iter t (fun _ i w => zoneShiftOut false (i - 1) w) _ m).2.1
  have g6 := zr_pass_time_asc (zr_p3Tau t) (zr_p3Nxt t) (zr_fpS5 t P) 77 89
    ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat (zr_p3Tau_le t)
    (zr_pop_fields t _ _ (by show P.b ≤ P.b + P.i - 1; omega))
  have g7 := zr_pass_time_desc zr_rbTau (zr_rbNxt t) (zr_fpS6 t P) 1 9 (zr_fpS6 t P).i le_rfl
    (fun R => by have := zr_rbTau_le R; omega) fun m hm => by
      rw [zr_rb_iter t _ m hm]
      exact (zr_dn_iter t _ _ m).2.1
  have g8 := zr_pass_time_asc (zr_p4Tau t) (zr_p4Nxt t) (zr_fpS7 t P) 95 170
    ((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat (zr_p4Tau_le t)
    (zr_pop_fields t _ _ (by show P.b ≤ P.b + P.i - 1; omega))
  have g9 := zr_pass_time_desc zr_lbTau (zr_lbNxt t) (zr_fpS8 t P) 1 5 (zr_fpS8 t P).i le_rfl
    (fun R => by have := zr_lbTau_le R; omega) fun m hm => by
      rw [(zr_lb_iter t _ m hm).1]
      exact (zr_lb_iter t _ m hm).2.2.1
  have n2 : ((zr_fpS1 t P).s - (zr_fpS1 t P).b).toNat = P.i := by
    show (P.b + P.i - P.b).toNat = P.i
    omega
  have n6 : ((zr_fpS5 t P).s - (zr_fpS5 t P).b).toNat = P.i - 1 := by
    show (P.b + P.i - 1 - P.b).toNat = P.i - 1
    omega
  have n8 : ((zr_fpS7 t P).s - (zr_fpS7 t P).b).toNat = P.i - 1 := by
    show (P.b + P.i - 1 - P.b).toNat = P.i - 1
    omega
  have k1 : zr_tauOf (zr_fpG1 t x) P ≤ 40 * 2 ^ P.i + 172 * P.i :=
    g1.trans (by rw [show P.i - 1 + 1 = P.i by omega])
  have k2 : zr_tauOf (zr_fpG2 t x) P ≤ 4 * 2 ^ P.i + 13 * (P.i + 1) :=
    g2.trans (by rw [n2]; exact le_refl _)
  have k3 : zr_tauOf (zr_fpG3 t x) P ≤ 50 * 2 ^ P.i + 262 * P.i :=
    g3.trans (by show _ + _ * (P.i - 1 + 1) ≤ _; rw [show P.i - 1 + 1 = P.i by omega])
  have k4 : zr_tauOf (zr_fpG4 t x) P ≤ 155 := by
    show (if zr_hmOff t (zr_fpS3 t P) then 12 else 155) ≤ 155
    split_ifs <;> omega
  have k6 : zr_tauOf (zr_fpG6 t x) P ≤ 154 * 2 ^ (P.i - 1) + 91 * P.i :=
    g6.trans (by
      rw [n6]
      show 2 * 77 * 2 ^ (P.i - 1 + 0) + 91 * (P.i - 1 + 1) ≤ _
      rw [add_zero, show P.i - 1 + 1 = P.i by omega])
  have k7 : zr_tauOf (zr_fpG7 t x) P ≤ 2 * 2 ^ (P.i - 1) + 11 * P.i :=
    g7.trans (by
      show 2 * 1 * 2 ^ (P.i - 1) + (9 + 2) * (P.i - 1 + 1) ≤ _
      rw [show P.i - 1 + 1 = P.i by omega])
  have k8 : zr_tauOf (zr_fpG8 t x) P ≤ 190 * 2 ^ (P.i - 1) + 172 * P.i :=
    g8.trans (by
      rw [n8]
      show 2 * 95 * 2 ^ (P.i - 1 + 0) + 172 * (P.i - 1 + 1) ≤ _
      rw [add_zero, show P.i - 1 + 1 = P.i by omega])
  have k9 : zr_tauOf (zr_fpG9 t x) P ≤ 2 * 2 ^ (P.i - 1) + 7 * P.i :=
    g9.trans (by
      show 2 * 1 * 2 ^ (P.i - 1) + (5 + 2) * (P.i - 1 + 1) ≤ _
      rw [show P.i - 1 + 1 = P.i by omega])
  show 1 + 1 + (zr_tauOf (zr_fpG1 t x) P + 1 + (zr_tauOf (zr_fpG2 t x) P + 1 +
    (zr_tauOf (zr_fpG3 t x) P + 1 + (zr_tauOf (zr_fpG4 t x) P + 1 + (1 + 1 + 1 + 1 +
    (zr_tauOf (zr_fpG6 t x) P + 1 + (zr_tauOf (zr_fpG7 t x) P + 1 +
    (zr_tauOf (zr_fpG8 t x) P + 1 + (zr_tauOf (zr_fpG9 t x) P + 1 + 1))))))))) ≤ _
  omega

/-- **The found path's start at the scan's end**: the scanned zone's field `i₀ + 1`, the scan's
count of `i₀ + 1` marks from the scratch start `I.2` as the base tape, the stack empty just past
it. -/
private abbrev zr_rowP0 {k : ℕ} (t : Fin k) (I : ZoneData k × ℤ) : zr_Px k :=
  ⟨I.1, zoneRebalanceIndex true t I.1 + 1, zr_rulerTape (zoneRebalanceIndex true t I.1 + 1) I.2,
    I.2 + zoneRebalanceIndex true t I.1 + 2, I.2 + zoneRebalanceIndex true t I.1 + 2⟩

/-- The rightward row's start pin: the zoned tape of the data, scratch blank. -/
private abbrev zr_rowT0 {k : ℕ} (I : ZoneData k × ℤ) : Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes (zonedTape I.1.2) fun _ => none

/-- The rightward row's endpoint pin: the zoned tape of the rebalanced data, scratch blank. -/
private abbrev zr_rowT2 {k : ℕ} (t : Fin k) (I : ZoneData k × ℤ) :
    Fin 2 → ℤ → Option (ZoneSym k) :=
  zr_tapes (zonedTape (zoneRebalanceData true t I.1).2) fun _ => none

/-- The rightward row's head box, its lower corner: the zoned head at `-zoneStart (i₀ + 1)`,
scratch one cell below its start. -/
private abbrev zr_rowL {k : ℕ} (t : Fin k) (I : ZoneData k × ℤ) : Fin 2 → ℤ :=
  zr_heads (-(zoneStart (zoneRebalanceIndex true t I.1 + 1) : ℤ)) (I.2 - 1)

/-- The rightward row's head box, its upper corner. -/
private abbrev zr_rowU {k : ℕ} (t : Fin k) (I : ZoneData k × ℤ) : Fin 2 → ℤ :=
  zr_heads (zoneStart (zoneRebalanceIndex true t I.1 + 1))
    (I.2 + zoneRebalanceIndex true t I.1 + 13 + 18 * ((2 ^ zoneRebalanceIndex true t I.1 : ℕ) : ℤ))

/-- A found scan's end is a found path index. -/
private lemma zr_rowP0_valid {k : ℕ} (t : Fin k) {I : ZoneData k × ℤ}
    (h : zoneRebalanceIndex true t I.1 < I.1.1) : zr_fpV (zr_rowP0 t I) := by
  refine ⟨⟨show zoneRebalanceIndex true t I.1 + 1 ≤ I.1.1 by omega, le_rfl, fun r hr => ?_⟩, ?_,
    rfl, show 1 ≤ zoneRebalanceIndex true t I.1 + 1 by omega,
    show zoneRebalanceIndex true t I.1 + 1 ≤ I.1.1 by omega⟩
  · have hr' : I.2 + zoneRebalanceIndex true t I.1 + 2 ≤ r := hr
    show zr_rulerTape _ _ r = none
    rw [zr_rulerTape, if_neg (by omega)]
  · show zr_rulerTape _ _ (I.2 + zoneRebalanceIndex true t I.1 + 2 - 1) = none
    rw [zr_rulerTape, if_neg (by omega)]

/-- The scan's two escapes, the found one first. -/
private lemma zr_scan_exits :
    (Option.map Sum.inr '' {some ⟨false, some true⟩, some ⟨false, none⟩} :
      Set (Option (SeekPhase ⊕ Σ b, zr_hostPh zr_scanSt b))) =
      {some (Sum.inr ⟨false, none⟩), some (Sum.inr ⟨false, some true⟩)} :=
  (zr_map_pair _ _ _).trans (Set.pair_comm _ _)

/-- A row start pinned at its scratch start meets the scan's precondition. -/
private lemma zr_scanPin_pre {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) (I : ZoneData k × ℤ)
    (d : Cfg 2 (ZoneSym k) (SeekPhase ⊕ Σ b, zr_hostPh zr_scanSt b) x)
    (hp : True ∧ zr_pinned (zr_rowT0 I) (zr_heads 0 I.2) d) : (zr_scanContract t x).pre I.1 d := by
  obtain ⟨-, h1, h2⟩ := hp
  rw [zr_scanContract, Contract.seq_pre, zr_homeSkipContract, zr_reindexContract,
    Contract.ofSegment_pre]
  refine ⟨funext fun q => ?_, ?_⟩
  · rw [Cfg.mapState_workTapes, h1]
    rfl
  · rw [Cfg.mapState_workTapePos, h2]
    rfl

/-- **The scan as a pinned test**, at an index of the data and the scratch start: from the row's
start pin to the found path's start pin, its two exits the found and the short escapes. -/
private def zr_scanPin {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_reindexContract (zr_exitsContract (zr_scanContract t x) _ zr_scan_exits) Prod.fst
    (fun (I : ZoneData k × ℤ) d => True ∧ zr_pinned (zr_rowT0 I) (zr_heads 0 I.2) d)
    fun I d hp => by
      rw [zr_exitsContract, Contract.ofSegment_pre]
      exact zr_scanPin_pre t x I d hp

/-- **The scan's pinned step**: from the row's start to the scan's count of `i₀ + 1` marks, the
zoned head at zone `i₀`'s start, in the row's box. -/
private lemma zr_scanPin_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_scanPin t x) (fun _ => True) zr_rowT0 (fun I => zr_pT (zr_rowP0 t I))
      (fun I => zr_heads 0 I.2)
      (fun I => zr_heads (zr_rstart (zr_rowP0 t I).i) ((zr_rowP0 t I).b - 1))
      (fun I => zoneStart (zoneRebalanceIndex true t I.1) + 8 * zoneRebalanceIndex true t I.1 +
        (if zoneRebalanceIndex true t I.1 < I.1.1 then 9 else 7)) (zr_rowL t) (zr_rowU t) :=
  zr_pinRe_ofSeg _ _ _ _ (zr_scanPin_pre t x) fun I d _ hd => by
    obtain ⟨ht, hpost, hl0, hh0, hl1, hh1⟩ := zr_scan_fields t I.1 d
    have h0 : d.workTapePos 0 = 0 := by rw [hd.2]; rfl
    have h1 : d.workTapePos 1 = I.2 := by rw [hd.2]; rfl
    have hb : ∀ r, d.workTapes 1 r = none := fun r => by rw [hd.1]; rfl
    have hz : d.workTapes 0 = zonedTape I.1.2 := by rw [hd.1]; rfl
    have hL := two_le_zoneStart (zoneRebalanceIndex true t I.1 + 1)
    have hs0 : zoneStart 0 = 2 := by norm_num [zoneStart_eq]
    have hp := Nat.two_pow_pos (zoneRebalanceIndex true t I.1)
    rw [hpost]
    refine ⟨⟨funext fun j => funext fun r => ?_, funext fun j => ?_⟩, rfl, rfl, ht,
      Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · by_cases hj : j = 0
      · subst hj
        simp only [zr_scanCfg, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), hz,
          zr_pT, zr_tapes, if_true]
      · obtain rfl : j = 1 := by omega
        simp only [zr_scanCfg, Function.update_self, h1, hb, zr_pT, zr_tapes, zr_pσ, zr_stk,
          show (1 : Fin 2) ≠ 0 by decide, if_false, zr_rulerTape]
        split_ifs <;> first | rfl | omega
    · simp only [zr_scanCfg, zr_heads, zr_rstart, h1, Nat.add_sub_cancel, Nat.succ_ne_zero,
        if_false]
      split_ifs <;> push_cast <;> ring
    · rw [hl0, h0, hs0]
      simp only [zr_rowL, zr_heads, if_true]
      omega
    · rw [hh0, h0]
      simp only [zr_rowU, zr_heads, if_true]
      omega
    · rw [hl1, h1]
      simp only [zr_rowL, zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false]
      omega
    · rw [hh1, h1]
      simp only [zr_rowU, zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false]
      omega

/-- The found path from the scan's end, at a found scan, in the rightward row's box. -/
private noncomputable def zr_fpRow {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  show zr_PinSeg x _ _ _ (fun I => True ∧ decide (zoneRebalanceIndex true t I.1 < I.1.1) = true)
    (fun I => zr_pT (zr_rowP0 t I)) (fun I => zr_pT (zr_fpS9 t (zr_rowP0 t I)))
    (fun I => zr_heads (zr_rstart (zr_rowP0 t I).i) ((zr_rowP0 t I).b - 1))
    (fun I => zr_heads 0 ((zr_rowP0 t I).b - 1)) _ (zr_rowL t) (zr_rowU t) from
  zr_seg (zr_segRe (zr_fpSeg t x) (zr_rowP0 t) _ fun _ h =>
      zr_rowP0_valid t (of_decide_eq_true h.2)).step (fun _ _ => rfl) fun I _ => by
    have hp := Nat.two_pow_pos (zoneRebalanceIndex true t I.1)
    refine ⟨rfl, zr_heads_le ?_ ?_, zr_heads_le ?_ ?_⟩
    · exact le_rfl
    · show I.2 - 1 ≤ I.2 + zoneRebalanceIndex true t I.1 + 2 - 2
      omega
    · exact le_rfl
    · show I.2 + zoneRebalanceIndex true t I.1 + 2 +
          9 * ((2 ^ (zoneRebalanceIndex true t I.1 + 1) : ℕ) : ℤ) + 11 ≤
        I.2 + zoneRebalanceIndex true t I.1 + 13 +
          18 * ((2 ^ zoneRebalanceIndex true t I.1 : ℕ) : ℤ)
      rw [pow_succ]
      push_cast
      omega

/-- At the found path's end the scan's count is all of scratch, its head just past the count. -/
private lemma zr_cc_scratch {k : ℕ} {S : Type} {x : List (ZoneSym k)} (t : Fin k)
    (I : ZoneData k × ℤ) (d : Cfg 2 (ZoneSym k) S x)
    (hd : zr_pinned (zr_pT (zr_fpS9 t (zr_rowP0 t I))) (zr_heads 0 ((zr_rowP0 t I).b - 1)) d) :
    zr_scratchAt ((zoneRebalanceIndex true t I.1 + 1 : ℕ) : ℤ)
      (zoneRebalanceIndex true t I.1 + 1) d :=
  ⟨Nat.succ_pos _, fun r => by
    rw [hd.1, hd.2]
    show zr_stk (zr_rowP0 t I).β (zr_rowP0 t I).b (zr_rowP0 t I).b r =
      zr_rulerTape _ (I.2 + zoneRebalanceIndex true t I.1 + 2 - 1 - _) r
    rw [zr_stk, if_neg (by omega)]
    show zr_rulerTape _ I.2 r = _
    congr 1
    push_cast
    ring⟩

/-- **The count's clear at the found path's end**, at an index of the data and the scratch
start. -/
private def zr_ccPin {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_singletonContract (zr_reindexContract (zr_countClearContract x)
    (fun I : ZoneData k × ℤ => zoneRebalanceIndex true t I.1 + 1)
    (fun I d => (True ∧ decide (zoneRebalanceIndex true t I.1 < I.1.1) = true) ∧
      zr_pinned (zr_pT (zr_fpS9 t (zr_rowP0 t I))) (zr_heads 0 ((zr_rowP0 t I).b - 1)) d)
    fun I d hp => by
      rw [zr_countClearContract, Contract.seq_pre, zr_stepContract, Contract.ofSegment_pre]
      exact zr_scratchAt_move _ _ (zr_cc_scratch t I d hp.2)
        (fun r => by rw [Cfg.mapState_workTapes]) (by rw [Cfg.mapState_workTapePos]))
    (Sum.inr (Sum.inr SweepPhase.done))

/-- **The count clear's pinned step**: from the found path's end to the row's endpoint, scratch
blank again and its head back at its start. -/
private lemma zr_ccPin_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_ccPin t x)
      (fun I => True ∧ decide (zoneRebalanceIndex true t I.1 < I.1.1) = true)
      (fun I => zr_pT (zr_fpS9 t (zr_rowP0 t I))) (zr_rowT2 t)
      (fun I => zr_heads 0 ((zr_rowP0 t I).b - 1)) (fun I => zr_heads 0 I.2)
      (fun I => 3 * (zoneRebalanceIndex true t I.1 + 1) + 8) (zr_rowL t) (zr_rowU t) :=
  zr_PinStep_exits (hX := by simp only [Set.image_singleton, Option.map_some])
    (zr_pinRe_step _ _ _ _ _ _ fun I d hV hd => by
    obtain ⟨ht, hpost, hl0, hh0, hl1, hh1⟩ :=
      zr_countClear_fields (zoneRebalanceIndex true t I.1 + 1) d (zr_cc_scratch t I d hd)
    have hi : zoneRebalanceIndex true t I.1 < I.1.1 := of_decide_eq_true hV.2
    have h0 : d.workTapePos 0 = 0 := by rw [hd.2]; rfl
    have h1 : d.workTapePos 1 = I.2 + zoneRebalanceIndex true t I.1 + 2 - 1 := by rw [hd.2]; rfl
    have hL := two_le_zoneStart (zoneRebalanceIndex true t I.1 + 1)
    have hp := Nat.two_pow_pos (zoneRebalanceIndex true t I.1)
    rw [hpost]
    refine ⟨⟨funext fun j => funext fun r => ?_, ?_⟩, rfl, rfl, ht,
      Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · by_cases hj : j = 0
      · subst hj
        show Function.update d.workTapes 1 (fun _ => none) 0 r = _
        rw [Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), hd.1]
        show zonedTape (zr_fpS9 t (zr_rowP0 t I)).D.2 r =
          zonedTape (Function.update I.1.2 t (zoneRebalance true (I.1.2 t))) r
        rw [zr_fp_data, zoneRebalance_of_lt _ _ hi, zoneCascade_true]
        rfl
      · obtain rfl : j = 1 := by omega
        show Function.update d.workTapes 1 (fun _ => none) 1 r = _
        rw [Function.update_self]
        rfl
    · show Function.update d.workTapePos 1 (d.workTapePos 1 - _) = zr_heads 0 I.2
      rw [hd.2, zr_heads_set1, zr_heads_one]
      congr 1
      show I.2 + zoneRebalanceIndex true t I.1 + 2 - 1 -
        ((zoneRebalanceIndex true t I.1 + 1 : ℕ) : ℤ) = I.2
      push_cast
      ring
    · rw [hl0, h0]
      simp only [zr_rowL, zr_heads, if_true]
      omega
    · rw [hh0, h0]
      simp only [zr_rowU, zr_heads, if_true]
      omega
    · rw [hl1, h1]
      simp only [zr_rowL, zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false]
      push_cast
      omega
    · rw [hh1, h1]
      simp only [zr_rowU, zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false]
      omega)

/-- Decidable equality of the scan's and the found path's states. -/
private noncomputable def zr_rowDec {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    DecidableEq (zr_stOf (zr_scanPin t x)) × DecidableEq (zr_stOf (zr_fpRow t x).C) := by
  refine ⟨?_, ?_⟩ <;>
  repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | refine zr_decHost ?_ |
    exact inferInstance)

/-- **The found arm**: the found path, then the count's clear, as one pinned segment from the
scan's end to the row's endpoint. -/
private noncomputable def zr_foundSeg {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  letI := (zr_rowDec t x).2
  zr_segSeq (zr_fpRow t x) ⟨zr_ccPin t x, zr_ccPin_step t x⟩

/-- A short scan's index is the level count. -/
private lemma zr_short_eq {k : ℕ} (t : Fin k) {I : ZoneData k × ℤ}
    (h : ¬ zoneRebalanceIndex true t I.1 < I.1.1) : zoneRebalanceIndex true t I.1 = I.1.1 := by
  have hle : zoneRebalanceIndex true t I.1 ≤ I.1.1 := zoneShiftIndex_le true (I.1.2 t)
  omega

/-- **A short scan's end is the short path's start**: past the layout, the scan's count of
`ℓ + 1` marks all of scratch. -/
private lemma zr_shortPin_pre {k : ℕ} {x : List (ZoneSym k)} (t : Fin k) (I : ZoneData k × ℤ)
    (d : Cfg 2 (ZoneSym k) ((Σ b, zr_loopPh b) ⊕ Option Bool ⊕ SeekPhase ⊕ SweepPhase) x)
    (h : ¬ zoneRebalanceIndex true t I.1 < I.1.1)
    (hd : zr_pinned (zr_pT (zr_rowP0 t I))
      (zr_heads (zr_rstart (zr_rowP0 t I).i) ((zr_rowP0 t I).b - 1)) d) :
    (zr_shortContract x).pre I.1 d := by
  letI := zr_decEqLoopPh
  have hs := zr_short_eq t h
  rw [zr_shortContract, Contract.seq_pre, zr_shortLoopContract, zr_reindexContract,
    Contract.ofSegment_pre]
  refine ⟨⟨?_, fun q _ _ => ?_⟩, Nat.succ_pos _, fun r => ?_⟩
  · rw [Cfg.mapState_workTapePos, hd.2]
    show zr_rstart (zoneRebalanceIndex true t I.1 + 1) = zoneStart I.1.1
    rw [hs, zr_rstart, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
  · rw [Cfg.mapState_workTapes, hd.1]
    rfl
  · rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hd.1, hd.2]
    show zr_stk (zr_rowP0 t I).β (zr_rowP0 t I).b (zr_rowP0 t I).b r =
      zr_rulerTape _ (I.2 + zoneRebalanceIndex true t I.1 + 2 - 1 - _) r
    rw [zr_stk, if_neg (by omega)]
    show zr_rulerTape (zoneRebalanceIndex true t I.1 + 1) I.2 r = _
    rw [hs]
    congr 1
    push_cast
    ring

/-- **The short path at a short scan**, at an index of the data and the scratch start. -/
private def zr_shortPin {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  zr_singletonContract (zr_reindexContract (zr_shortContract x) Prod.fst
    (fun (I : ZoneData k × ℤ) d =>
      (True ∧ decide (zoneRebalanceIndex true t I.1 < I.1.1) = false) ∧
        zr_pinned (zr_pT (zr_rowP0 t I))
          (zr_heads (zr_rstart (zr_rowP0 t I).i) ((zr_rowP0 t I).b - 1)) d)
    fun I d hp => zr_shortPin_pre t I d (of_decide_eq_false hp.1.2) hp.2)
    (Sum.inr (Sum.inr (Sum.inr SweepPhase.done)))

/-- **The short path's pinned step**: from a short scan's end to the row's endpoint, the data
unchanged. -/
private lemma zr_shortPin_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_shortPin t x)
      (fun I => True ∧ decide (zoneRebalanceIndex true t I.1 < I.1.1) = false)
      (fun I => zr_pT (zr_rowP0 t I)) (zr_rowT2 t)
      (fun I => zr_heads (zr_rstart (zr_rowP0 t I).i) ((zr_rowP0 t I).b - 1))
      (fun I => zr_heads 0 I.2) (fun I => zoneStart I.1.1 + 11 * I.1.1 + 20)
      (zr_rowL t) (zr_rowU t) :=
  zr_PinStep_exits (hX := by simp only [Set.image_singleton, Option.map_some])
    (zr_pinRe_step _ _ _ _ _ _ fun I d hV hd => by
    have hn : ¬ zoneRebalanceIndex true t I.1 < I.1.1 := of_decide_eq_false hV.2
    have hs := zr_short_eq t hn
    obtain ⟨ht, hpost, hl0, hh0, hl1, hh1⟩ := zr_short_fields I.1 d (zr_shortPin_pre t I d hn hd)
    have h1 : d.workTapePos 1 = I.2 + zoneRebalanceIndex true t I.1 + 2 - 1 := by rw [hd.2]; rfl
    have hm : zoneStart I.1.1 ≤ zoneStart (zoneRebalanceIndex true t I.1 + 1) := by
      rw [hs]
      exact zoneStart_mono (Nat.le_add_right _ 1)
    have hL := two_le_zoneStart (zoneRebalanceIndex true t I.1 + 1)
    have hp := Nat.two_pow_pos (zoneRebalanceIndex true t I.1)
    rw [hpost]
    refine ⟨⟨funext fun j => funext fun r => ?_, funext fun j => ?_⟩, rfl, rfl, ht,
      Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · by_cases hj : j = 0
      · subst hj
        show Function.update d.workTapes 1 (fun _ => none) 0 r = _
        rw [Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), hd.1]
        show zonedTape I.1.2 r =
          zonedTape (Function.update I.1.2 t (zoneRebalance true (I.1.2 t))) r
        rw [zoneRebalance_of_le _ _ (show I.1.1 ≤ zoneShiftIndex true (I.1.2 t) from hs.ge),
          Function.update_eq_self]
      · obtain rfl : j = 1 := by omega
        show Function.update d.workTapes 1 (fun _ => none) 1 r = _
        rw [Function.update_self]
        rfl
    · show (if j = 0 then 0 else d.workTapePos 1 - (I.1.1 + 1)) = zr_heads 0 I.2 j
      rw [h1]
      simp only [zr_heads]
      split_ifs
      · rfl
      · rw [hs]
        ring
    · rw [hl0]
      simp only [zr_rowL, zr_heads, if_true]
      omega
    · rw [hh0]
      simp only [zr_rowU, zr_heads, if_true]
      exact_mod_cast hm
    · rw [hl1, h1]
      simp only [zr_rowL, zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false]
      rw [hs]
      omega
    · rw [hh1, h1]
      simp only [zr_rowU, zr_heads, show (1 : Fin 2) ≠ 0 by decide, if_false]
      omega)

/-- The scan's two escapes are distinct. -/
private lemma zr_scanNe :
    (Sum.inr ⟨false, none⟩ : SeekPhase ⊕ Σ b, zr_hostPh zr_scanSt b) ≠
      Sum.inr ⟨false, some true⟩ := by
  simp

/-- **The scan's verdict**: the found escape exactly when the scanned index is below `ℓ`. -/
private lemma zr_scan_verdict {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    ∀ (I : ZoneData k × ℤ) d, True → zr_pinned (zr_rowT0 I) (zr_heads 0 I.2) d →
      ((zr_scanPin t x).post I d).state =
        some (if decide (zoneRebalanceIndex true t I.1 < I.1.1) then Sum.inr ⟨false, none⟩
          else Sum.inr ⟨false, some true⟩) := fun I d _ _ => by
  rw [zr_scanPin, zr_reindexContract, Contract.ofSegment_post, zr_exitsContract,
    Contract.ofSegment_post, (zr_scan_fields t I.1 d).2.1, (zr_scanCfg_fields _ _ _ _).1]
  by_cases h : zoneRebalanceIndex true t I.1 < I.1.1 <;> simp [h]

/-- **The rightward row**: the scan, then at a found scan the found arm, at a short scan the
short path. -/
private noncomputable def zr_rowC {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :=
  letI := (zr_rowDec t x).1
  letI := (zr_rowDec t x).2
  Contract.branch zr_scanNe (zr_scanPin t x) (zr_foundSeg t x).C (zr_shortPin t x) (fun I => I)
    (fun I => I)
    (zr_pin_blink true zr_scanNe (zr_scanPin_step t x) (zr_scan_verdict t x) rfl
      (zr_foundSeg t x).step)
    (zr_pin_blink false zr_scanNe (zr_scanPin_step t x) (zr_scan_verdict t x) rfl
      (zr_shortPin_step t x))

/-- **The rightward row's pinned step**: from the zoned tape of the data and a blank scratch to
the zoned tape of the rebalanced data and a blank scratch, the heads back, in the row's box. -/
private lemma zr_rowC_step {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_PinStep (zr_rowC t x) (fun _ => True) zr_rowT0 (zr_rowT2 t) (fun I => zr_heads 0 I.2)
      (fun I => zr_heads 0 I.2)
      (fun I => zoneStart (zoneRebalanceIndex true t I.1) + 8 * zoneRebalanceIndex true t I.1 +
        (if zoneRebalanceIndex true t I.1 < I.1.1 then 9 else 7) + 1 +
        if decide (zoneRebalanceIndex true t I.1 < I.1.1) then
          zr_tauOf (zr_fpSeg t x) (zr_rowP0 t I) + 1 + (3 * (zoneRebalanceIndex true t I.1 + 1) + 8)
        else zoneStart I.1.1 + 11 * I.1.1 + 20) (zr_rowL t) (zr_rowU t) :=
  letI := (zr_rowDec t x).1
  letI := (zr_rowDec t x).2
  zr_PinStep_branch zr_scanNe (zr_scanPin_step t x) (zr_scan_verdict t x) (zr_foundSeg t x).step
    (zr_shortPin_step t x) _ _

/-- **The rightward row's exits**: the found arm's at a found scan, the short path's
otherwise. -/
private lemma zr_rowC_back {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) :
    zr_BackIs (zr_rowC t x)
      (zr_branchBack (zr_oneBack (zr_exitOf (zr_foundSeg t x).C) true)
        (zr_oneBack (zr_exitOf (zr_shortPin t x)) false))
      fun I => if decide (zoneRebalanceIndex true t I.1 < I.1.1) then true else false :=
  letI := (zr_rowDec t x).1
  letI := (zr_rowDec t x).2
  zr_BackIs_branch zr_scanNe (zr_scanPin_step t x) (zr_scan_verdict t x)
    (zr_BackIs_one _ true) (zr_BackIs_one _ false)

/-- The rightward row's exit state. -/
private lemma zr_rowC_state {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) (I : ZoneData k × ℤ)
    (d : Cfg 2 (ZoneSym k) (zr_stOf (zr_rowC t x)) x)
    (hd : d.state = some (zr_entryOf (zr_rowC t x))) (hp : (zr_rowC t x).pre I d) :
    ((zr_rowC t x).post I d).state = some (if zoneRebalanceIndex true t I.1 < I.1.1 then
      Sum.inl (Sum.inr (zr_exitOf (zr_foundSeg t x).C)) else
      Sum.inr (zr_exitOf (zr_shortPin t x))) := by
  obtain ⟨s, hs, hb⟩ := zr_rowC_back t x I d hd hp
  rw [hs]
  by_cases h : zoneRebalanceIndex true t I.1 < I.1.1
  · rw [if_pos h]
    beta_reduce at hb
    rw [if_pos (decide_eq_true h)] at hb
    rcases s with (s | s) | s
    · exact absurd hb (by simp [zr_branchBack])
    · dsimp only [zr_branchBack] at hb
      unfold zr_oneBack at hb
      split_ifs at hb with h1
      rw [h1]
    · dsimp only [zr_branchBack] at hb
      unfold zr_oneBack at hb
      split_ifs at hb
      exact absurd hb (by simp)
  · rw [if_neg h]
    beta_reduce at hb
    rw [if_neg (by rwa [decide_eq_true_iff])] at hb
    rcases s with (s | s) | s
    · exact absurd hb (by simp [zr_branchBack])
    · dsimp only [zr_branchBack] at hb
      unfold zr_oneBack at hb
      split_ifs at hb
      exact absurd hb (by simp)
    · dsimp only [zr_branchBack] at hb
      unfold zr_oneBack at hb
      split_ifs at hb with h1
      rw [h1]

/-- A zone-row start is pinned at the rightward row's start pin, at its own scratch start. -/
private lemma zr_rowPre_pin {k : ℕ} {S : Type} {x : List (ZoneSym k)} {D : ZoneData k}
    {d : Cfg 2 (ZoneSym k) S x} (hp : zoneRowPre D d) :
    zr_pinned (zr_rowT0 (D, d.workTapePos 1)) (zr_heads 0 (D, d.workTapePos 1).2) d := by
  refine ⟨funext fun j => funext fun r => ?_, funext fun j => ?_⟩
  · by_cases hj : j = 0
    · subst hj
      rw [hp.1]
      rfl
    · obtain rfl : j = 1 := by omega
      rw [hp.2.2 r]
      rfl
  · by_cases hj : j = 0
    · subst hj
      rw [hp.2.1]
      rfl
    · obtain rfl : j = 1 := by omega
      rfl

/-- **The rightward row's time** is at most `2300 · (2^i₀ + 1)`. -/
private lemma zr_rowC_time {k : ℕ} (t : Fin k) (x : List (ZoneSym k)) (I : ZoneData k × ℤ) :
    zoneStart (zoneRebalanceIndex true t I.1) + 8 * zoneRebalanceIndex true t I.1 +
        (if zoneRebalanceIndex true t I.1 < I.1.1 then 9 else 7) + 1 +
        (if decide (zoneRebalanceIndex true t I.1 < I.1.1) then
          zr_tauOf (zr_fpSeg t x) (zr_rowP0 t I) + 1 + (3 * (zoneRebalanceIndex true t I.1 + 1) + 8)
        else zoneStart I.1.1 + 11 * I.1.1 + 20) ≤
      2300 * (2 ^ zoneRebalanceIndex true t I.1 + 1) := by
  have hz := zoneStart_eq (zoneRebalanceIndex true t I.1)
  have hi : zoneRebalanceIndex true t I.1 < 2 ^ zoneRebalanceIndex true t I.1 :=
    Nat.lt_two_pow_self
  rw [pow_succ] at hz
  by_cases h : zoneRebalanceIndex true t I.1 < I.1.1
  · have hf := zr_fpSeg_time t x (zr_rowP0_valid t h)
    have hp : 2 ^ (zr_rowP0 t I).i = 2 * 2 ^ zoneRebalanceIndex true t I.1 := by
      show 2 ^ (zoneRebalanceIndex true t I.1 + 1) = _
      rw [pow_succ]
      ring
    rw [hp] at hf
    rw [if_pos h, if_pos (decide_eq_true h)]
    omega
  · have hs := zr_short_eq t h
    rw [if_neg h, if_neg (by rwa [decide_eq_true_iff])]
    rw [← hs]
    omega

/-- The rightward row's found and short exits. -/
private noncomputable abbrev zr_rowDone {k : ℕ} (t : Fin k) :=
  (Sum.inl (Sum.inr (zr_exitOf (zr_foundSeg t ([] : List (ZoneSym k))).C)) :
    zr_stOf (zr_rowC t ([] : List (ZoneSym k))))

/-- The rightward row's short exit. -/
private noncomputable abbrev zr_rowShort {k : ℕ} (t : Fin k) :=
  (Sum.inr (zr_exitOf (zr_shortPin t ([] : List (ZoneSym k)))) :
    zr_stOf (zr_rowC t ([] : List (ZoneSym k))))

/-- **The rightward rebalance row** on the data, its envelopes at the constant `C ≥ 2300`: the
rightward row at the start's own scratch start. -/
private noncomputable def zr_rowR {k : ℕ} (t : Fin k) (C : ℕ) (hC : 2300 ≤ C)
    (x : List (ZoneSym k)) :
    Contract (zr_machineOf (zr_rowC t ([] : List (ZoneSym k))))
      (zr_entryOf (zr_rowC t ([] : List (ZoneSym k)))) {some (zr_rowDone t), some (zr_rowShort t)}
      (ZoneData k) x :=
  Contract.ofSegment zoneRowPre (fun D d => (zr_rowC t x).time (D, d.workTapePos 1) d)
    (zoneRebalancePost true t (zr_rowDone t) (zr_rowShort t))
    (zoneRowLo (zoneRebalanceIndex true t) C) (zoneRowHi (zoneRebalanceIndex true t) C)
    (fun D d hd hp => by
      have hpin := zr_rowPre_pin hp
      obtain ⟨hpre, ⟨hT, hP⟩, hin, hout, -, hbox⟩ := (zr_rowC_step t x).2 _ d trivial hpin
      have hseg := (zr_rowC t x).segment (D, d.workTapePos 1) d hd hpre
      have hpost : (zr_rowC t x).post (D, d.workTapePos 1) d =
          zoneRebalancePost true t (zr_rowDone t) (zr_rowShort t) D d := by
        refine Cfg.ext ?_ hin (funext fun j => funext fun r => ?_) (funext fun j => ?_) hout
        · rw [zr_rowC_state t x _ d hd hpre]
          simp only [zoneRebalancePost]
        · rw [hT]
          by_cases hj : j = 0
          · subst hj
            simp only [zoneRebalancePost, if_true]
            rfl
          · obtain rfl : j = 1 := by omega
            simp only [zoneRebalancePost, show (1 : Fin 2) ≠ 0 by decide, if_false, hp.2.2 r]
            rfl
        · rw [hP]
          simp only [zoneRebalancePost]
          by_cases hj : j = 0
          · subst hj
            rw [hp.2.1]
            rfl
          · obtain rfl : j = 1 := by omega
            rfl
      rw [hpost] at hseg
      refine hseg.mono (fun s hs => ?_) fun p hb => ?_
      · rcases hs with rfl | rfl
        · exact Or.inl ⟨_, rfl, rfl⟩
        · exact Or.inr ⟨_, rfl, rfl⟩
      · have hpos : (0 : ℤ) < 2 ^ zoneRebalanceIndex true t D := by positivity
        have hi : (zoneRebalanceIndex true t D : ℤ) < 2 ^ zoneRebalanceIndex true t D := by
          exact_mod_cast Nat.lt_two_pow_self
        rw [headBox_iff] at hb ⊢
        intro j
        have h := Finset.mem_Icc.mp (hb j)
        obtain ⟨hl, hh⟩ := hbox j
        rw [Finset.mem_Icc]
        simp only [zoneRowLo, zoneRowHi]
        by_cases hj : j = 0
        · subst hj
          simp only [zr_rowL, zr_rowU, zr_heads, if_true] at hl hh
          simp only [if_true]
          omega
        · obtain rfl : j = 1 := by omega
          simp only [zr_rowL, zr_rowU, zr_heads, show (1 : Fin 2) ≠ 0 by decide,
            if_false] at hl hh
          simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
          have hC' : (2300 : ℤ) ≤ C := by exact_mod_cast hC
          have hm : (2300 : ℤ) * (2 ^ zoneRebalanceIndex true t D + 1) ≤
              C * (2 ^ zoneRebalanceIndex true t D + 1) :=
            mul_le_mul_of_nonneg_right hC' (by positivity)
          push_cast at hh ⊢
          constructor <;> linarith)
    (fun D d _ _ => by
      simp only [zoneRebalancePost]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl)

/-- **The rightward rebalance row's fields**: its precondition, endpoint and envelopes are the
target's, and its time is at most `C · (2^i₀ + 1)`. -/
private lemma zr_rowR_spec {k : ℕ} (t : Fin k) (C : ℕ) (hC : 2300 ≤ C) (x : List (ZoneSym k)) :
    (zr_rowR t C hC x).pre = zoneRowPre ∧
      (zr_rowR t C hC x).post = zoneRebalancePost true t (zr_rowDone t) (zr_rowShort t) ∧
      (zr_rowR t C hC x).lo = zoneRowLo (zoneRebalanceIndex true t) C ∧
      (zr_rowR t C hC x).hi = zoneRowHi (zoneRebalanceIndex true t) C ∧
      ∀ D d, d.state = some (zr_entryOf (zr_rowC t ([] : List (ZoneSym k)))) →
        (zr_rowR t C hC x).pre D d →
          (zr_rowR t C hC x).time D d ≤ C * (2 ^ zoneRebalanceIndex true t D + 1) := by
  refine ⟨funext fun D => funext fun d => by rw [zr_rowR, Contract.ofSegment_pre],
    funext fun D => funext fun d => by rw [zr_rowR, Contract.ofSegment_post],
    funext fun D => funext fun d => funext fun j => by rw [zr_rowR, Contract.ofSegment_lo],
    funext fun D => funext fun d => funext fun j => by rw [zr_rowR, Contract.ofSegment_hi],
    fun D d hd hp => ?_⟩
  rw [zr_rowR, Contract.ofSegment_pre] at hp
  rw [zr_rowR, Contract.ofSegment_time]
  obtain ⟨-, -, -, -, ht, -⟩ := (zr_rowC_step t x).2 _ d trivial (zr_rowPre_pin hp)
  rw [ht]
  have := zr_rowC_time t x (D, d.workTapePos 1)
  have h2 : 2300 * (2 ^ zoneRebalanceIndex true t D + 1) ≤
      C * (2 ^ zoneRebalanceIndex true t D + 1) :=
    Nat.mul_le_mul_right _ hC
  exact this.trans h2

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
every guard and without a fullness assumption. The rightward scan is proved as a contract with
both exits (a loop host whose rounds mark a unary zone count on scratch), and so is its short
path (the return home and the count's clear). One level's column moves for the rightward
cascade are proved as machine segments with their guards enabled: the right inward shift and
the left outward shift at level `i`, each from the zoned tape to the zoned tape of the shifted
track with the heads and the scratch restored, in `76 · 2^(i-1) + 77` and `76 · 2^(i-1) + 107`
steps; their one-slot guard tests are characterized, and a disabled guard leaves the tape
unchanged. The rightward cascade's passes are proved: the descending inward pass on the right
and outward pass on the left, the walk out between them, the guarded home move (a column
operation on the two zones `0` and the home through scratch, guarded by left zone `0`'s outer
slot), a single pop, the ascending inward and outward passes and their two returns, each a
pinned segment on a loop host whose rounds keep a count stack on scratch. Their composition,
the found path, runs from the scanned zone's field and the scan's count to the home and the
count's end, with track `t` cascaded to the right at the scanned index (`zoneCascadeRight`,
through the side-pass reordering), every other track and the count kept, and the zoned head
within `zoneStart (i₀ + 1)` of home, in at most `1000 · 2^(i₀ + 1) + 200` steps (each round's
time bounded by its level and the passes' geometric sums). The rightward row is proved: the scan
as a pinned test with its two exits, then at a found index the found path and the count's clear,
at a short scan the short path, through the pinned branch; it is a contract with this target's
fields at `dir = true` for every constant `C ≥ 2300`, the zoned head within `zoneStart (i₀ + 1)`
of home and scratch within `18 · 2^i₀ + i₀ + 13` of its start. The leftward row (planned as the
mirrored machine through `Turing.Contract.lockstep`) and the assembly remain open. Only this
target's body is admitted. -/
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
