/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.ZoneTape
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic

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
(`Turing.zoneCascade_cost_le`). -/
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
distance; clear the ruler and return home. Each phase is `O(2^ℓ)`. -/
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
