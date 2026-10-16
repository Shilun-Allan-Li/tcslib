/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.FinRange

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the zone layer, pure part (Z2, §13d)

The per-track data of the Hennie–Stearns simulation ([AB09] §1.7; `machine-library-design.md`
§13, Z2, as revised by §13d): two stacks of **zones** around a home cell, level `i` holding up to
`2 · 2^i` virtual cells per side, with the pure rebalancing operations, the classical cascade,
its mirror, the scanned index, the total guarded rebalance, the extension by one level, and the
virtual tape a track represents. Nothing here is a machine. The multi-track physical carrier is
`Build/ZoneTape` (§13d, G3) and the machine rows are `Build/ZoneRebalance` (§13d, G4).

**Status: proved.** Every declaration is proved; the last, `Turing.zoneCascadeRight_home` (the
cascade's new home is the right word's first cell), in the §13d G2 fill. History: the
statement phase of tranche A-S2
(`audits/zone-infra-findings.md`, rounds 1–3: the inward-room blocker repaired by totally guarded
ops, the cascade added, the top-left room hypotheses); the §13d revision (2026-10-10) and its
G3/G4 statement gate (`audits/s13d-g24-statements-findings.md`), which retired this module's
binary realization (`zoneTape`, its paired-cell codec, the seven staging-window lemmas) and its
two binary shift rows (`exists_zoneShiftInTM`, `exists_zoneShiftOutTM`), superseded by the rich
alphabet and the G4 rows.

## Design (13a; refined by the A-S2 audit and the §13d revision)

* **The carrier is data, the invariant is the consumer's.** `ZoneContents` carries per-zone
  words bounded by capacity; the Hennie–Stearns `{empty, half, full}` fullness discipline, the
  `2^i`-credit amortization and the simulation theorem live with the consumer (plan §2.1).
* **The operations are totally guarded.** The level-`i` inward shift moves the inner `2^(i-1)`
  stored cells of zone `i` into the **empty** zone `i - 1` and carries no room premise; the
  outward shift moves the outer half of a **full** zone `i - 1` onto the front of zone `i`, with
  its room condition inside its guard. Outside its guard every operation is the identity.
* **The classical rebalance is a cascade** of these ops (`zoneCascadeRight`; its mirror
  `zoneCascadeLeft`, defined through `ZoneContents.swap`); the rebalance of §13d
  (`zoneRebalance`) is the cascade at the scanned index `zoneShiftIndex`, total on every input
  (decision 13d.3), and the identity when every feeding zone is empty.
* **The extent** is a laid-out `ℓ` with an extension by one level (decision 13d.2): the new zones
  are half full of virtual blanks (`ZoneContents.extend`), which changes no represented tape.

## Main definitions

* `Turing.zoneCapacity`, `Turing.zoneBase`, `Turing.zoneIndex`: the layout arithmetic.
* `Turing.ZoneContents`, `Turing.zoneSlot`, `Turing.ZoneContents.words`: the carrier.
* `Turing.zoneSide`, `Turing.zoneTrackTape`: the represented half-words and virtual tape.
* `Turing.zoneShiftInW`/`Turing.zoneShiftOutW`, `Turing.zoneShiftIn`/`Turing.zoneShiftOut`:
  the pairwise ops; `Turing.zoneMoveRight`/`Left`, `Turing.zoneMove`, `Turing.zoneHomeWrite`.
* `Turing.zoneStepPair`, `Turing.zoneCascadeRight`, `Turing.ZoneContents.swap`,
  `Turing.zoneCascadeLeft`, `Turing.zoneCascade`: the cascade and its mirror.
* `Turing.zoneShiftIndex`, `Turing.zoneRebalance`, `Turing.ZoneContents.extend`: §13d's index,
  rebalance and extension.

## Main results

* `Turing.zoneSide_shiftInW`/`OutW`, `Turing.zoneShiftInW_full_donor`: honesty and the
  full-donor regression.
* `Turing.zoneSide_cascadeRight`, `Turing.zoneCascadeRight_lengths`, `Turing.zoneCascade_cost_le`,
  `Turing.zoneCascadeRight_zero`, `Turing.zoneCascadeRight_blocked`,
  `Turing.zoneCascadeRight_frame`, and the mirrors `Turing.zoneSide_cascadeLeft`,
  `Turing.zoneCascadeLeft_lengths`.
* `Turing.zoneShiftIndex_empty`, `Turing.zoneShiftIndex_nonempty`, `Turing.zoneShiftIndex_eq`,
  `Turing.zoneShiftIndex_extend`: the scan.
* `Turing.zoneRebalance_frame`, `Turing.zoneSide_rebalance_right`/`left`,
  `Turing.zoneTrackTape_rebalance_right`/`left`: what a rebalance does.
* `Turing.zoneSide_extend`, `Turing.zoneTrackTape_extend`: the extension is invisible.
* `Turing.zoneCapacity_eq` — a zone's capacity as an equation, the specification API (user,
  2026-10-16).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§1.7, the Hennie–Stearns simulation; Exercise 1.6.)
* In-repo precedents: `SweepCell`/`SweepAlphabet` (`Robustness/SingleTape.lean`);
  `ObliviousSetup.lean`'s guide-zone layout.
-/

namespace Turing

/-! ### Layout arithmetic -/

/-- The capacity of zone `i`, in virtual cells per side. -/
def zoneCapacity (i : ℕ) : ℕ := 2 * 2 ^ i

/-- **A zone's capacity as an equation** (the specification API, user 2026-10-16). -/
theorem zoneCapacity_eq (i : ℕ) : zoneCapacity i = 2 * 2 ^ i :=
  rfl

/-- The first virtual slot of zone `i`: the exact total capacity of the
zones inside it. -/
def zoneBase (i : ℕ) : ℕ := 2 * (2 ^ i - 1)

/-- Bases telescope by capacities (skeleton-time proof; flagged). -/
theorem zoneBase_succ (i : ℕ) : zoneBase (i + 1) = zoneBase i + zoneCapacity i := by
  have h : 0 < 2 ^ i := Nat.two_pow_pos i
  simp only [zoneBase, zoneCapacity, pow_succ]
  omega

/-- The zone owning virtual slot `s`: the unique `i` with
`zoneBase i ≤ s < zoneBase (i + 1)`. -/
def zoneIndex (s : ℕ) : ℕ := Nat.log2 (s / 2 + 1)

/-- `zoneIndex` is the inverse of the base arithmetic: a slot lies in the
zone it indexes.

**Proof sketch.** Write `s = 2r + ε`; both base endpoints are even, so the
sandwich `zoneBase i ≤ s < zoneBase (i + 1)` is equivalent to
`2^i ≤ r + 1 < 2^(i+1)`, which characterizes `Nat.log2 (r + 1)` (the
argument is positive, so there is no logarithm-at-zero case). The round-1
audit's independent derivation is the route. -/
theorem zoneIndex_eq_iff (s i : ℕ) :
    zoneIndex s = i ↔ zoneBase i ≤ s ∧ s < zoneBase (i + 1) := by
  rw [zoneIndex, Nat.log2_eq_iff (by omega)]
  have h := Nat.two_pow_pos i
  have h' := Nat.two_pow_pos (i + 1)
  unfold zoneBase
  omega

/-! ### The carrier -/

/-- The zone contents of one tape: the home cell and, per level and side,
the stored word (inner end first), bounded by capacity. Fullness
discipline is deliberately **not** carried here (design §13a): the
Hennie-Stearns `{empty, half, full}` invariant is the consumer's, and the
round-1 audit's cascade analysis confirms intermediate cascade states
leave the discipline anyway. -/
structure ZoneContents (ℓ : ℕ) where
  /-- the virtual cell under the virtual head -/
  home : Option Bool
  /-- the left zone words, inner end first -/
  left : Fin ℓ → List (Option Bool)
  /-- the right zone words, inner end first -/
  right : Fin ℓ → List (Option Bool)
  /-- left words fit their zones -/
  left_le : ∀ i, (left i).length ≤ zoneCapacity i.val
  /-- right words fit their zones -/
  right_le : ∀ i, (right i).length ≤ zoneCapacity i.val

/-- The stored virtual cell at slot `s` of one side, or `none` when the
slot is beyond the stored words (an unoccupied slot, `⊠` on the zoned tape of
`Build/ZoneTape` — distinct from an occupied slot storing a virtual blank). -/
def zoneSlot {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) (s : ℕ) :
    Option (Option Bool) :=
  if h : zoneIndex s < ℓ then (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]?
  else none

/-- The empty contents (blank home, every zone empty). -/
def ZoneContents.empty (ℓ : ℕ) : ZoneContents ℓ where
  home := none
  left := fun _ => []
  right := fun _ => []
  left_le := fun _ => by simp
  right_le := fun _ => by simp

/-! ### The represented word -/

/-- The virtual half-word one side represents: the zone words
concatenated inner-first. -/
def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i

private theorem zoneSide_succ {n : ℕ} (w : Fin (n + 1) → List (Option Bool)) :
    zoneSide w = w 0 ++ zoneSide (fun k => w k.succ) := by
  simp [zoneSide, List.finRange_succ, List.flatMap_map]

/-- Replacing two adjacent zone words with the same concatenation preserves
the represented side.

**Proof sketch.** Induct on the number of levels, peeling off the
unchanged first word until the changed pair is at the front. -/
private theorem zoneSide_adjacent {n : ℕ} (a : ℕ) (ha : a + 1 < n)
    (w v : Fin n → List (Option Bool))
    (hp : v ⟨a, by omega⟩ ++ v ⟨a + 1, ha⟩ =
      w ⟨a, by omega⟩ ++ w ⟨a + 1, ha⟩)
    (hf : ∀ k, k.val ≠ a → k.val ≠ a + 1 → v k = w k) :
    zoneSide v = zoneSide w := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    cases a with
    | zero =>
      cases n with
      | zero => omega
      | succ n =>
        rw [zoneSide_succ, zoneSide_succ]
        rw [zoneSide_succ, zoneSide_succ, ← List.append_assoc, ← List.append_assoc]
        rw [show v 0 ++ v (Fin.succ 0) = w 0 ++ w (Fin.succ 0) from hp]
        congr 1
        congr 1
        funext k
        apply hf <;> simp
    | succ a =>
      rw [zoneSide_succ, zoneSide_succ, hf 0 (by simp) (by simp)]
      congr 1
      apply ih a (by omega) (fun k => w k.succ) (fun k => v k.succ)
      · exact hp
      · intro k h0 h1
        apply hf <;> simp only [Fin.val_succ] <;> omega

/-! ### Pure rebalancing (pairwise, order-preserving, totally guarded) -/

/-- The level-`i` inward shift on one side's family: when `1 ≤ i < ℓ` and
zone `i - 1` is **empty**, move the inner `2^(i-1)` stored cells (or all
of them, if fewer) of zone `i` into it; identity otherwise. **No room
premise exists** (round-1 repair, A-S2-1): the operation removes cells
from the donor, so a full donor is always legal — the exact case the
classical rebalance needs. -/
def zoneShiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if w ⟨i - 1, by omega⟩ = [] then
      if j.val = i - 1 then (w ⟨i, hi.2⟩).take (2 ^ (i - 1))
      else if j.val = i then (w ⟨i, hi.2⟩).drop (2 ^ (i - 1))
      else w j
    else w j
  else w j

/-- The level-`i` outward shift on one side's family: when `1 ≤ i < ℓ`,
zone `i - 1` is **full**, and the receiving zone `i` has room for the
moved half, move zone `i - 1`'s outer half onto the front of zone `i`;
identity otherwise. The room condition lives **inside the guard**
(round-1 repair): no caller carries a hypothesis, and a cramped receiver
makes the op the identity rather than ill-defined. -/
def zoneShiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if (w ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) ∧
        (w ⟨i, hi.2⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i then
      if j.val = i - 1 then (w ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
      else if j.val = i then
        (w ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++ w ⟨i, hi.2⟩
      else w j
    else w j
  else w j

/-- Inward rebalancing never changes the represented half-word.

**Proof sketch.** A disabled guard gives the identity. When enabled, zones
`i - 1` and `i` are adjacent in the inner-first concatenation, zone
`i - 1` was empty, and `take ++ drop` restores zone `i`'s word, so the
concatenation is unchanged. -/
theorem zoneSide_shiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftInW i w) = zoneSide w := by
  by_cases hi : 1 ≤ i ∧ i < ℓ
  · by_cases he : w ⟨i - 1, by omega⟩ = []
    · apply zoneSide_adjacent (i - 1) (by omega)
      · have hne : i ≠ i - 1 := by omega
        have hsucc : i - 1 + 1 = i := by omega
        simp [zoneShiftInW, hi, he, hsucc, hne, List.take_append_drop]
      · intro k h0 h1
        have hk : k.val ≠ i := by omega
        simp [zoneShiftInW, hi, he, h0, hk]
    · have hsame : zoneShiftInW i w = w := by
        funext k
        simp [zoneShiftInW, hi, he]
      rw [hsame]
  · have hsame : zoneShiftInW i w = w := by
      funext k
      simp [zoneShiftInW, hi]
    rw [hsame]

/-- Outward rebalancing never changes the represented half-word.

**Proof sketch.** A disabled guard gives the identity. When enabled, the
adjacent two-zone segment is literally re-associated:
`take q ++ (drop q ++ wᵢ) = wᵢ₋₁ ++ wᵢ` at the cutoff `q = 2^(i-1)`. -/
theorem zoneSide_shiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftOutW i w) = zoneSide w := by
  by_cases hi : 1 ≤ i ∧ i < ℓ
  · by_cases hg : (w ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) ∧
        (w ⟨i, hi.2⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i
    · apply zoneSide_adjacent (i - 1) (by omega)
      · have hne : i ≠ i - 1 := by omega
        have hsucc : i - 1 + 1 = i := by omega
        simp [zoneShiftOutW, hi, hg, hsucc, hne, ← List.append_assoc]
      · intro k h0 h1
        have hk : k.val ≠ i := by omega
        simp [zoneShiftOutW, hi, hg, h0, hk]
    · have hsame : zoneShiftOutW i w = w := by
        funext k
        simp [zoneShiftOutW, hi, hg]
      rw [hsame]
  · have hsame : zoneShiftOutW i w = w := by
      funext k
      simp [zoneShiftOutW, hi]
    rw [hsame]

/-- **The full-donor regression** (required by the round-1 audit,
A-S2-1): above an empty zone, a donor of any length — a full one included —
shifts inward with no side condition: the receiving zone gets the inner
`2^(i-1)` cells (or all, if fewer) and the donor keeps the rest.

**Proof sketch.** Unfold `zoneShiftInW`: both guards fire by the
hypotheses, and the two branch equations are the stated `take`/`drop`. -/
theorem zoneShiftInW_full_donor {ℓ : ℕ} (i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ)
    (w : Fin ℓ → List (Option Bool)) (hempty : w ⟨i - 1, by omega⟩ = []) :
    zoneShiftInW i w ⟨i - 1, by omega⟩ = (w ⟨i, hℓ⟩).take (2 ^ (i - 1)) ∧
    zoneShiftInW i w ⟨i, hℓ⟩ = (w ⟨i, hℓ⟩).drop (2 ^ (i - 1)) := by
  have hne : i ≠ i - 1 := by omega
  simp [zoneShiftInW, hi, hℓ, hempty, hne]

private theorem zoneShiftInW_capacity {ℓ : ℕ} (i : ℕ)
    (w : Fin ℓ → List (Option Bool))
    (hw : ∀ j, (w j).length ≤ zoneCapacity j.val) :
    ∀ j, (zoneShiftInW i w j).length ≤ zoneCapacity j.val := by
  intro j
  unfold zoneShiftInW
  split_ifs with hi he hj hj
  · simp only [List.length_take, zoneCapacity, hj]
    omega
  · have h := hw ⟨i, hi.2⟩
    dsimp only at h
    simp only [List.length_drop, hj]
    exact (Nat.sub_le _ _).trans h
  · exact hw j
  · exact hw j
  · exact hw j

/-- Lift the inward shift to contents: `side = false` acts on the left
family, `side = true` on the right. Hypothesis-free (round-1 repair).

**Proof sketch** (capacity fields): the receiving zone gets at most
`2^(i-1) ≤ zoneCapacity (i-1)` cells; the donor's word only shrinks;
untouched zones keep their bounds. -/
def zoneShiftIn {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    ZoneContents ℓ where
  home := z.home
  left := if side then z.left else zoneShiftInW i z.left
  right := if side then zoneShiftInW i z.right else z.right
  left_le := by
    cases side
    · exact zoneShiftInW_capacity i z.left z.left_le
    · exact z.left_le
  right_le := by
    cases side
    · exact z.right_le
    · exact zoneShiftInW_capacity i z.right z.right_le

private theorem zoneShiftOutW_capacity {ℓ : ℕ} (i : ℕ)
    (w : Fin ℓ → List (Option Bool))
    (hw : ∀ j, (w j).length ≤ zoneCapacity j.val) :
    ∀ j, (zoneShiftOutW i w j).length ≤ zoneCapacity j.val := by
  intro j
  unfold zoneShiftOutW
  split_ifs with hi hg hj hj
  · simp only [List.length_take, zoneCapacity, hj]
    omega
  · simp only [List.length_append, List.length_drop, hg.1, hj]
    have h := hg.2
    unfold zoneCapacity at *
    omega
  · exact hw j
  · exact hw j
  · exact hw j

/-- Lift the outward shift to contents. Hypothesis-free: the receiving
zone's room condition is inside the family op's guard.

**Proof sketch** (capacity fields): when the guard fires, the shrunk
lower word fits trivially and the enlarged upper word fits by the guard's
own room conjunct; otherwise everything is unchanged. -/
def zoneShiftOut {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    ZoneContents ℓ where
  home := z.home
  left := if side then z.left else zoneShiftOutW i z.left
  right := if side then zoneShiftOutW i z.right else z.right
  left_le := by
    cases side
    · exact zoneShiftOutW_capacity i z.left z.left_le
    · exact z.left_le
  right_le := by
    cases side
    · exact z.right_le
    · exact zoneShiftOutW_capacity i z.right z.right_le

/-! ### Pure head steps and the home write -/

/-- Overwrite the virtual cell under the head. -/
def zoneHomeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool) :
    ZoneContents ℓ := { z with home := v }

/-- The virtual head steps right: the home is pushed onto the inner end of
the left stack's zone `0`, and the new home is popped from the right
stack's zone `0` (blank when that zone is empty — the virtual tape is
blank past its stored extent; the Hennie-Stearns consumer's invariant
makes this the genuinely-blank case). Capacity of `L_0` is the consumer's
rebalancing obligation, carried here as a hypothesis; the hypothesis-free
guarded form is `Turing.zoneMove`. -/
def zoneMoveRight {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    ZoneContents ℓ where
  home := ((z.right ⟨0, hℓ⟩).headI : Option Bool)
  left := fun j => if j.val = 0 then z.home :: z.left j else z.left j
  right := fun j => if j.val = 0 then (z.right j).tail else z.right j
  left_le := by
    intro j
    split_ifs with hj
    · have he : j = ⟨0, hℓ⟩ := Fin.ext hj
      subst j
      simpa only [List.length_cons] using hroom
    · exact z.left_le j
  right_le := by
    intro j
    split_ifs
    · simpa only [List.length_tail] using
        (Nat.sub_le (z.right j).length 1).trans (z.right_le j)
    · exact z.right_le j

/-- The mirrored left step. -/
def zoneMoveLeft {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    ZoneContents ℓ where
  home := ((z.left ⟨0, hℓ⟩).headI : Option Bool)
  left := fun j => if j.val = 0 then (z.left j).tail else z.left j
  right := fun j => if j.val = 0 then z.home :: z.right j else z.right j
  left_le := by
    intro j
    split_ifs
    · simpa only [List.length_tail] using
        (Nat.sub_le (z.left j).length 1).trans (z.left_le j)
    · exact z.left_le j
  right_le := by
    intro j
    split_ifs with hj
    · have he : j = ⟨0, hℓ⟩ := Fin.ext hj
      subst j
      simpa only [List.length_cons] using hroom
    · exact z.right_le j

/-- The totally guarded head step (`dir = true` is right): acts when
`0 < ℓ` and the pushed side has room, else identity — the foldable form
the cascade uses. -/
def zoneMove {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  if hℓ : 0 < ℓ then
    match dir with
    | true =>
      if h : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveRight hℓ z h
      else z
    | false =>
      if h : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveLeft hℓ z h
      else z
  else z

/-- A right step transforms the represented tape as the virtual head move:
the old home joins the left word's inner end, and the right word loses its
inner cell (a nonempty `R_0` case; the blank-extension case pads with the
virtual blank).

**Proof sketch.** Pure list bookkeeping on `zoneSide`: `finRange`'s head
is zone `0`, and only zone `0` changes on each side. -/
theorem zoneSide_moveRight {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0)
    (hne : z.right ⟨0, hℓ⟩ ≠ []) :
    zoneSide (zoneMoveRight hℓ z hroom).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneMoveRight hℓ z hroom).right = (zoneSide z.right).tail := by
  cases ℓ with
  | zero => omega
  | succ n =>
    have hleft : (fun k : Fin n => (zoneMoveRight hℓ z hroom).left k.succ) =
        (fun k : Fin n => z.left k.succ) := by
      funext k
      simp [zoneMoveRight]
    have hright : (fun k : Fin n => (zoneMoveRight hℓ z hroom).right k.succ) =
        (fun k : Fin n => z.right k.succ) := by
      funext k
      simp [zoneMoveRight]
    constructor
    · rw [zoneSide_succ, zoneSide_succ, hleft]
      simp [zoneMoveRight]
    · rw [zoneSide_succ, zoneSide_succ, hright]
      simp only [zoneMoveRight, Fin.val_zero, ite_true]
      exact (List.tail_append_of_ne_nil hne).symm

/-! ### The classical rebalance as a cascade (round-1 repair, A-S2-1)

The round-1 audit supplied the schedule and its analysis; the statements
below are the required gate material. One classical right move at index
`j`: a descending pass of inward-right/outward-left pairs from level `j`
down to `1`, the head step, and the ascending pass back up. -/

/-- One cascade stage at level `i`: shift inward on the right (feeding the
head's side) and outward on the left (draining the side the head leaves). -/
def zoneStepPair {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  zoneShiftOut false i (zoneShiftIn true i z)

/-- The classical right-move rebalance at index `j`: descend `j → 1`,
step right, ascend `1 → j`. -/
def zoneCascadeRight {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  (List.range j).foldl (fun z i => zoneStepPair (i + 1) z)
    (zoneMove true
      ((List.range j).reverse.foldl (fun z i => zoneStepPair (i + 1) z) z))

private theorem zoneStepPair_side {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) :
    zoneSide (zoneStepPair i z).left = zoneSide z.left ∧
      zoneSide (zoneStepPair i z).right = zoneSide z.right :=
  ⟨zoneSide_shiftOutW i z.left, zoneSide_shiftInW i z.right⟩

private theorem zoneStepPair_frame {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ)
    (k : Fin ℓ) (h0 : k.val ≠ i - 1) (h1 : k.val ≠ i) :
    (zoneStepPair i z).left k = z.left k ∧
      (zoneStepPair i z).right k = z.right k := by
  change zoneShiftOutW i z.left k = z.left k ∧ zoneShiftInW i z.right k = z.right k
  constructor
  · unfold zoneShiftOutW
    split_ifs <;> simp_all
  · unfold zoneShiftInW
    split_ifs <;> simp_all

private theorem zoneStepPair_active {ℓ : ℕ} (i : ℕ) (hi : i + 1 < ℓ)
    (z : ZoneContents ℓ) (hr : z.right ⟨i, by omega⟩ = [])
    (hl : (z.left ⟨i, by omega⟩).length = zoneCapacity i)
    (hroom : (z.left ⟨i + 1, hi⟩).length + 2 ^ i ≤ zoneCapacity (i + 1)) :
    (zoneStepPair (i + 1) z).right ⟨i, by omega⟩ =
        (z.right ⟨i + 1, hi⟩).take (2 ^ i) ∧
    (zoneStepPair (i + 1) z).left ⟨i, by omega⟩ =
        (z.left ⟨i, by omega⟩).take (2 ^ i) ∧
    (zoneStepPair (i + 1) z).right ⟨i + 1, hi⟩ =
        (z.right ⟨i + 1, hi⟩).drop (2 ^ i) ∧
    (zoneStepPair (i + 1) z).left ⟨i + 1, hi⟩ =
        (z.left ⟨i, by omega⟩).drop (2 ^ i) ++ z.left ⟨i + 1, hi⟩ := by
  simp [zoneStepPair, zoneShiftIn, zoneShiftOut, zoneShiftInW, zoneShiftOutW,
    hi, hr, hl, hroom]

private theorem zoneCascadeRight_succ {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascadeRight (j + 1) z =
      zoneStepPair (j + 1) (zoneCascadeRight j (zoneStepPair (j + 1) z)) := by
  simp [zoneCascadeRight, List.range_succ, List.reverse_append, List.foldl_append]

/-- **The cascade keeps every level above its index** (made public at the
§13d G3/G4 landing, its proof unchanged). Levels strictly above `j` are untouched on both sides.

**Proof sketch.** Induction on `j`: the base move touches level `0` only, and each outer pair
`zoneStepPair (j + 1)` touches levels `j` and `j + 1` only. -/
theorem zoneCascadeRight_frame {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ)
    (k : Fin ℓ) (hk : j < k.val) :
    (zoneCascadeRight j z).left k = z.left k ∧
      (zoneCascadeRight j z).right k = z.right k := by
  induction j generalizing z with
  | zero =>
    have hk0 : k.val ≠ 0 := by omega
    simp only [zoneCascadeRight, List.range_zero, List.reverse_nil, List.foldl_nil]
    unfold zoneMove
    split_ifs <;> simp [zoneMoveRight, hk0]
  | succ j ih =>
    rw [zoneCascadeRight_succ]
    rw [(zoneStepPair_frame _ _ k (by omega) (by omega)).1,
      (zoneStepPair_frame _ _ k (by omega) (by omega)).2]
    rw [(ih _ (by omega)).1, (ih _ (by omega)).2]
    exact zoneStepPair_frame _ _ k (by omega) (by omega)

/-- The index-`0` cascade is the guarded head move once level zero has room: both folds run
over `List.range 0 = []`, and `zoneMove`'s guard fires. -/
private theorem zoneCascadeRight_zero_eq {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    zoneCascadeRight 0 z = zoneMoveRight hℓ z hroom := by
  show zoneMove true z = _
  simp only [zoneMove, dif_pos hℓ, dif_pos hroom]

/-- **The levels below `j` after the outer step pair.** From the classical lower state at index
`j + 1` (right zones below `j + 1` empty, left zones below it full) with room for one pass at
`j + 1`, the outer step pair `zoneStepPair (j + 1)` leaves the right zones below `j` empty, the
left zones below `j` full, and `2^j` cells in the left zone `j`.

**Proof sketch.** The pair touches levels `j` and `j + 1` only (`zoneStepPair_frame`); at level
`j` it keeps the first `2^j` of the full left zone's `2 · 2^j` cells (`zoneStepPair_active`). -/
private theorem zoneStepPair_below {ℓ : ℕ} (j : ℕ) (hj : j + 1 < ℓ) (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j + 1), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j + 1), (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hroom' : (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤ zoneCapacity (j + 1)) :
    (∀ k (hk : k < j), (zoneStepPair (j + 1) z).right ⟨k, by omega⟩ = []) ∧
    (∀ k (hk : k < j),
      ((zoneStepPair (j + 1) z).left ⟨k, by omega⟩).length = zoneCapacity k) ∧
    ((zoneStepPair (j + 1) z).left ⟨j, by omega⟩).length = 2 ^ j := by
  have hjl : j < ℓ := by omega
  have hactive := zoneStepPair_active j hj z (hr j (by omega))
    (hl j (by omega)) hroom'
  have hr' : ∀ k (hk : k < j),
      (zoneStepPair (j + 1) z).right ⟨k, by omega⟩ = [] := by
    intro k hk
    rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩ (by dsimp; omega) (by dsimp; omega)).2]
    exact hr k (by omega)
  have hl' : ∀ k (hk : k < j),
      ((zoneStepPair (j + 1) z).left ⟨k, by omega⟩).length = zoneCapacity k := by
    intro k hk
    rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩ (by dsimp; omega) (by dsimp; omega)).1]
    exact hl k (by omega)
  have hlower : ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length = 2 ^ j := by
    rw [hactive.2.1, List.length_take, hl j (by omega)]
    unfold zoneCapacity
    omega
  exact ⟨hr', hl', hlower⟩

/-- **The classical pre-state descends one level.** If `z` is in the classical pre-state of
`Turing.zoneSide_cascadeRight` at index `j + 1`, then the outer step pair `zoneStepPair (j + 1)`
leaves it in the classical pre-state at index `j`: the right zones below `j` empty, the left zones
below `j` full, a nonempty donor at `j`, and room for one pass on the left at `j`.

**Proof sketch.** The levels below `j`, and the `2^j` cells left in the left zone `j`, are
`zoneStepPair_below`. At level `j` the pair moves the donor's first `2^j` cells in, which are
nonempty since the donor is (`zoneStepPair_active`), and the `2^j` left cells with `2^(j-1)` more
fit the capacity `2 · 2^j`. -/
private theorem zoneStepPair_pre {ℓ : ℕ} (j : ℕ) (hj : j + 1 < ℓ) (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j + 1), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j + 1), (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j + 1, hj⟩ ≠ [])
    (hroom : (z.left ⟨j + 1, hj⟩).length + 2 ^ (j + 1 - 1) ≤ zoneCapacity (j + 1)) :
    (∀ k (hk : k < j), (zoneStepPair (j + 1) z).right ⟨k, by omega⟩ = []) ∧
    (∀ k (hk : k < j),
      ((zoneStepPair (j + 1) z).left ⟨k, by omega⟩).length = zoneCapacity k) ∧
    (zoneStepPair (j + 1) z).right ⟨j, by omega⟩ ≠ [] ∧
    ((zoneStepPair (j + 1) z).left ⟨j, by omega⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j := by
  have hjl : j < ℓ := by omega
  have hroom' : (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
      zoneCapacity (j + 1) := by simpa using hroom
  have hactive := zoneStepPair_active j hj z (hr j (by omega))
    (hl j (by omega)) hroom'
  obtain ⟨hr', hl', hlower⟩ := zoneStepPair_below j hj z hr hl hroom'
  have hd' : (zoneStepPair (j + 1) z).right ⟨j, hjl⟩ ≠ [] := by
    rw [hactive.1]
    apply List.ne_nil_of_length_pos
    rw [List.length_take]
    exact lt_min (Nat.two_pow_pos j) (List.length_pos_iff.mpr hdonor)
  have hroomlower : ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length +
      2 ^ (j - 1) ≤ zoneCapacity j := by
    rw [hlower]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le j 1)
    unfold zoneCapacity
    omega
  exact ⟨hr', hl', hd', hroomlower⟩

/-- **The classical right cascade, both facts by one induction.** Under the classical pre-state
at index `j`, the cascade's words are the old ones with the home pushed on the left and the right
word's head popped (`Turing.zoneSide_cascadeRight`), and its new home is that head
(`Turing.zoneCascadeRight_home`).

**Proof sketch.** Induction on `j`. At `0` the cascade is the central move: it pushes the old home
on the left and pops the donor's head into the home (`Turing.zoneSide_moveRight`), and the donor,
zone `0`, is the right word's first word. At `j + 1` the outer step pair leaves the pre-state at
`j` (`zoneStepPair_pre`), and both step pairs keep both concatenations and the home
(`zoneStepPair_side`), so the induction hypothesis gives both facts. -/
private theorem zoneCascadeRight_classical {ℓ : ℕ} (j : ℕ) (hj : j < ℓ) (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j), (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ [])
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) :
    (zoneSide (zoneCascadeRight j z).left = z.home :: zoneSide z.left ∧
      zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail) ∧
    (zoneCascadeRight j z).home = (zoneSide z.right).headI := by
  induction j generalizing z with
  | zero =>
    have hroom0 : (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      simpa using hroom
    rw [zoneCascadeRight_zero_eq hj z hroom0]
    refine ⟨zoneSide_moveRight hj z hroom0 hdonor, ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨a, as, ha⟩ := List.exists_cons_of_ne_nil hdonor
    simp only [zoneMoveRight]
    rw [zoneSide_succ, show (0 : Fin (n + 1)) = ⟨0, hj⟩ from rfl, ha]
    rfl
  | succ j ih =>
    obtain ⟨hr', hl', hd', hroomlower⟩ := zoneStepPair_pre j hj z hr hl hdonor hroom
    obtain ⟨hinner, hhome⟩ := ih (by omega) (zoneStepPair (j + 1) z) hr' hl' hd' hroomlower
    rw [zoneCascadeRight_succ]
    refine ⟨?_, ?_⟩
    · rw [(zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2, hinner.1, hinner.2,
        (zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2]
      exact ⟨rfl, rfl⟩
    · show (zoneCascadeRight j (zoneStepPair (j + 1) z)).home = _
      rw [hhome, (zoneStepPair_side _ _).2]

/-- The cascade realizes exactly one virtual right move. Preconditions are
the classical pre-state at index `j` — on the right, zones below `j` empty
and the donor `j` nonempty; on the left, zones below `j` full — **plus the
top-left receiving room for one pass** (round-2 repair, A-S2-R2-1: without
it, a full left zone `j` blocks the drain, the guarded ops are identities,
and the conclusion is false already at `ℓ = 1`, `j = 0`). The `+ 2^(j-1)`
form is the round-2 audit's weaker sufficient condition for the word
equalities (at `j = 0`, natural subtraction makes it `+ 1`); the boundary
instance with room for exactly one pass — where these equalities hold but
half-full restoration fails — is the recorded reason this theorem's
hypothesis is weaker than `zoneCascadeRight_lengths`'s.

**Proof sketch** (the round-2 audit's schedule analysis, adopted as the
binding route): each descending prefix of the donor is nonempty, so `R₀`
is nonempty at the central move, and the left descending pass makes room
for the push under `hroom`; every surrounding shift preserves the
concatenations whether its guard fires or not
(`zoneSide_shiftInW`/`OutW`), so the single legal push/pop
(`zoneSide_moveRight`) gives exactly the two word equalities. Half-full
restoration is **not** used. Formally the induction on `j` is shared with
`Turing.zoneCascadeRight_home` (the private `zoneCascadeRight_classical`). -/
theorem zoneSide_cascadeRight {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ [])
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) :
    zoneSide (zoneCascadeRight j z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail :=
  (zoneCascadeRight_classical j hj z hr hl hdonor hroom).1

/-- The cascade restores the half-full discipline below its index: after a
classical right move at index `j` from a donor holding at least `2^j`
cells, every level below `j` is half-full on both sides, the right donor
loses exactly `2^j` cells, and the left zone `j` gains exactly `2^j`.

The top-left room hypothesis is **necessary** (round-2 repair,
A-S2-R2-1): the conclusion's left-top growth together with the result's
`left_le` field imply exactly `|L_j| + 2^j ≤ zoneCapacity j`, and the
classical stable invariant (`|L_j| + |R_j| = 2 · zoneCapacity j / 2` with
`|R_j| ≥ 2^j`) supplies it on every textbook pre-state, so no classical
instance is excluded.

**Proof sketch** (the round-2 audit's two-pass induction, adopted as the
binding route): the descending pass ends with the level-zero pair at
`(1, 1)`, each intermediate level `k` at `(2^(k-1), 3·2^(k-1))`, and the
top pair shifted by `2^(j-1)` — the top outward push legal by `hroom`,
the lower receivers legal because they were just drained; the head move
makes level zero `(0, 2)`; the ascending pass re-fires every guard on
those occupancies, the second top push legal exactly because
`|L_j| + 2^(j-1) + 2^(j-1) = |L_j| + 2^j ≤ zoneCapacity j`. -/
theorem zoneCascadeRight_lengths {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : 2 ^ j ≤ (z.right ⟨j, hj⟩).length)
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ j ≤ zoneCapacity j) :
    (∀ k (hk : k < j),
      ((zoneCascadeRight j z).right ⟨k, by omega⟩).length = 2 ^ k ∧
      ((zoneCascadeRight j z).left ⟨k, by omega⟩).length = 2 ^ k) ∧
    ((zoneCascadeRight j z).right ⟨j, hj⟩).length =
      (z.right ⟨j, hj⟩).length - 2 ^ j ∧
    ((zoneCascadeRight j z).left ⟨j, hj⟩).length =
      (z.left ⟨j, hj⟩).length + 2 ^ j := by
  induction j generalizing z with
  | zero =>
    have hroom0 : (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      simpa using hroom
    have hm := zoneCascadeRight_zero_eq hj z hroom0
    rw [hm]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      omega
    · simp [zoneMoveRight]
    · simp [zoneMoveRight]
  | succ j ih =>
    have hjl : j < ℓ := by omega
    have hp : 0 < 2 ^ j := Nat.two_pow_pos j
    have hroom1 : (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by
      rw [pow_succ] at hroom
      omega
    have hactive := zoneStepPair_active j hj z (hr j (by omega))
      (hl j (by omega)) hroom1
    let z1 := zoneStepPair (j + 1) z
    have hbelow := zoneStepPair_below j hj z hr hl hroom1
    have hrlower : (z1.right ⟨j, hjl⟩).length = 2 ^ j := by
      change ((zoneStepPair (j + 1) z).right ⟨j, hjl⟩).length = _
      rw [hactive.1, List.length_take]
      rw [pow_succ] at hdonor
      omega
    have hllower : (z1.left ⟨j, hjl⟩).length = 2 ^ j := hbelow.2.2
    have hrtop : (z1.right ⟨j + 1, hj⟩).length =
        (z.right ⟨j + 1, hj⟩).length - 2 ^ j := by
      change ((zoneStepPair (j + 1) z).right ⟨j + 1, hj⟩).length = _
      rw [hactive.2.2.1, List.length_drop]
    have hltop : (z1.left ⟨j + 1, hj⟩).length =
        (z.left ⟨j + 1, hj⟩).length + 2 ^ j := by
      change ((zoneStepPair (j + 1) z).left ⟨j + 1, hj⟩).length = _
      rw [hactive.2.2.2, List.length_append, List.length_drop, hl j (by omega)]
      unfold zoneCapacity
      omega
    have hinner := ih hjl z1 hbelow.1 hbelow.2.1 (by rw [hrlower]) (by
      rw [hllower]
      unfold zoneCapacity
      omega)
    let z2 := zoneCascadeRight j z1
    have hrzero : z2.right ⟨j, hjl⟩ = [] := by
      apply List.length_eq_zero_iff.mp
      change ((zoneCascadeRight j z1).right ⟨j, hjl⟩).length = 0
      rw [hinner.2.1, hrlower, Nat.sub_self]
    have hlfull : (z2.left ⟨j, hjl⟩).length = zoneCapacity j := by
      change ((zoneCascadeRight j z1).left ⟨j, hjl⟩).length = _
      rw [hinner.2.2, hllower]
      unfold zoneCapacity
      omega
    have hframe := zoneCascadeRight_frame j z1 ⟨j + 1, hj⟩ (by dsimp; omega)
    have hrtop2 : (z2.right ⟨j + 1, hj⟩).length =
        (z.right ⟨j + 1, hj⟩).length - 2 ^ j := by
      change ((zoneCascadeRight j z1).right ⟨j + 1, hj⟩).length = _
      rw [hframe.2, hrtop]
    have hltop2 : (z2.left ⟨j + 1, hj⟩).length =
        (z.left ⟨j + 1, hj⟩).length + 2 ^ j := by
      change ((zoneCascadeRight j z1).left ⟨j + 1, hj⟩).length = _
      rw [hframe.1, hltop]
    have hroom2 : (z2.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by
      rw [hltop2]
      rw [pow_succ] at hroom
      omega
    have hactive2 := zoneStepPair_active j hj z2 hrzero hlfull hroom2
    rw [zoneCascadeRight_succ]
    change (∀ k (hk : k < j + 1),
      ((zoneStepPair (j + 1) z2).right ⟨k, _⟩).length = 2 ^ k ∧
      ((zoneStepPair (j + 1) z2).left ⟨k, _⟩).length = 2 ^ k) ∧
      ((zoneStepPair (j + 1) z2).right ⟨j + 1, hj⟩).length =
        (z.right ⟨j + 1, hj⟩).length - 2 ^ (j + 1) ∧
      ((zoneStepPair (j + 1) z2).left ⟨j + 1, hj⟩).length =
        (z.left ⟨j + 1, hj⟩).length + 2 ^ (j + 1)
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      by_cases hkj : k = j
      · subst k
        rw [hactive2.1, hactive2.2.1, List.length_take, List.length_take,
          hrtop2, hlfull]
        rw [pow_succ] at hdonor
        unfold zoneCapacity
        constructor <;> omega
      · have hkj' : k < j := by omega
        rw [(zoneStepPair_frame (j + 1) z2 ⟨k, by omega⟩
          (by dsimp; omega) (by dsimp; omega)).2,
          (zoneStepPair_frame (j + 1) z2 ⟨k, by omega⟩
          (by dsimp; omega) (by dsimp; omega)).1]
        exact hinner.1 k hkj'
    · rw [hactive2.2.2.1, List.length_drop, hrtop2, pow_succ]
      omega
    · rw [hactive2.2.2.2, List.length_append, List.length_drop, hlfull, hltop2,
        pow_succ]
      unfold zoneCapacity
      omega

/-- Regression (round-2 audit, A-S2-R2-1): the `j = 0` cascade is exactly
the guarded head move, and with level-zero room and a nonempty donor it
realizes the virtual right move.

**Proof sketch.** `List.range 0 = []`, so the folds vanish; `zoneMove`'s
guard fires by the hypotheses and `zoneSide_moveRight` finishes. -/
theorem zoneCascadeRight_zero {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hdonor : z.right ⟨0, hℓ⟩ ≠ [])
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    zoneSide (zoneCascadeRight 0 z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneCascadeRight 0 z).right = (zoneSide z.right).tail := by
  rw [zoneCascadeRight_zero_eq hℓ z hroom]
  exact zoneSide_moveRight hℓ z hroom hdonor

/-- Regression (round-2 audit, A-S2-R2-1): a **full top receiver** blocks
the cascade harmlessly — with the classical lower-left state and
`L_j` at capacity, every outward-left guard fails, the head move is
blocked, and the represented words on both sides are unchanged.

**Proof sketch.** Lower left zones are full, so no outward-left guard
below `j` has room; at `j` the receiver is full; hence `L₀` stays full and
`zoneMove` takes its identity branch. The inward-right shifts preserve the
right concatenation by `zoneSide_shiftInW`. -/
theorem zoneCascadeRight_blocked {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hfull : (z.left ⟨j, hj⟩).length = zoneCapacity j) :
    zoneSide (zoneCascadeRight j z).left = zoneSide z.left ∧
    zoneSide (zoneCascadeRight j z).right = zoneSide z.right := by
  induction j generalizing z with
  | zero =>
    have hno : ¬ (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      rw [hfull]
      omega
    simp [zoneCascadeRight, zoneMove, hj, hno]
  | succ j ih =>
    have hno : ¬ (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by
      rw [hfull]
      have hp := Nat.two_pow_pos j
      omega
    have hf : (zoneStepPair (j + 1) z).left = z.left := by
      funext k
      simp [zoneStepPair, zoneShiftOut, zoneShiftIn, zoneShiftOutW, hj, hno]
    have hl' : ∀ k (hk : k < j),
        ((zoneStepPair (j + 1) z).left ⟨k, by omega⟩).length = zoneCapacity k := by
      intro k hk
      rw [hf]
      exact hl k (by omega)
    have hfull' : ((zoneStepPair (j + 1) z).left ⟨j, by omega⟩).length =
        zoneCapacity j := by
      rw [hf]
      exact hl j (by omega)
    have hinner := ih (by omega) (zoneStepPair (j + 1) z) hl' hfull'
    rw [zoneCascadeRight_succ, (zoneStepPair_side _ _).1,
      (zoneStepPair_side _ _).2, hinner.1, hinner.2,
      (zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2]
    exact ⟨rfl, rfl⟩

/-- The cascade's summed row budgets stay geometric: the charge lemma the
Hennie-Stearns amortization consumes (two shift pairs per level, each
within a per-level budget `2^i + i + 1`; the G4 rows of `Build/ZoneRebalance` state their
total as `C · (2^{i₀} + 1)`).

**Proof sketch.** `i + 1 ≤ 2^i` for `i ≥ 1`, so each summand is at most
`4 · 2 · 2^i = 8 · 2^i`, and the geometric sum over `1 ≤ i ≤ j` is
`8 · (2^(j+1) - 2) ≤ 16 · 2^j` — the round-1 audit's charge calculation. -/
theorem zoneCascade_cost_le (j : ℕ) :
    ∑ i ∈ Finset.range j, 4 * (2 ^ (i + 1) + (i + 1) + 1) ≤ 16 * 2 ^ j := by
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, 4 * (2 ^ (i + 1) + (i + 1) + 1)) + 16 ≤
        16 * 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hsmall : n + 2 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self
      simp only [pow_succ] at *
      omega
  have h := hsum j
  omega


/-! ## The §13d additions to the pure layer (G3/G4)

The mirror, the left cascade derived from it, the scanned index, the total guarded rebalance,
the extension by one level, and the virtual tape a track represents. Nothing here is a machine;
the multi-track carrier is `Build/ZoneTape` and the machine rows are `Build/ZoneRebalance`. -/

/-- The zone words of one side: `side = true` is the right stack, `false` the left. -/
def ZoneContents.words {ℓ : ℕ} (side : Bool) (z : ZoneContents ℓ) : Fin ℓ → List (Option Bool) :=
  if side then z.right else z.left

/-- Each side's words fit their zones. -/
theorem ZoneContents.words_le {ℓ : ℕ} (side : Bool) (z : ZoneContents ℓ) (i : Fin ℓ) :
    (z.words side i).length ≤ zoneCapacity i.val := by
  cases side
  · exact z.left_le i
  · exact z.right_le i

/-- **The mirror** of zone contents: the left and right stacks exchanged, the home kept. It
reverses the represented virtual tape about the head (`Turing.zoneTrackTape_swap`). -/
def ZoneContents.swap {ℓ : ℕ} (z : ZoneContents ℓ) : ZoneContents ℓ where
  home := z.home
  left := z.right
  right := z.left
  left_le := z.right_le
  right_le := z.left_le

/-- The mirror is an involution. -/
@[simp] theorem ZoneContents.swap_swap {ℓ : ℕ} (z : ZoneContents ℓ) : z.swap.swap = z := by
  cases z
  rfl

/-- **The classical left-move rebalance at index `j`**: the mirror of `Turing.zoneCascadeRight`,
defined through `Turing.ZoneContents.swap` (design §13d, G4: "its lemmas derived by symmetry,
never copied"). [AB09, §1.7], the shift performed for a left head move. -/
def zoneCascadeLeft {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  (zoneCascadeRight j z.swap).swap

/-- **The left cascade realizes one virtual left move** under the mirrored classical
pre-state: left zones below `j` empty, right zones below `j` full, the left donor `j`
nonempty, and the top-right room for one pass. The old home joins the right word's inner end
and the left word loses its inner cell. [AB09, §1.7]

**Proof sketch.** `Turing.zoneSide_cascadeRight` applied to the mirror; the mirror's stacks
are the original's exchanged, so its hypotheses and conclusions are these, read through
`Turing.ZoneContents.swap`. -/
theorem zoneSide_cascadeLeft {ℓ : ℕ} (j : ℕ) (hj : j < ℓ) (z : ZoneContents ℓ)
    (hl : ∀ k (hk : k < j), z.left ⟨k, by omega⟩ = [])
    (hr : ∀ k (hk : k < j), (z.right ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.left ⟨j, hj⟩ ≠ [])
    (hroom : (z.right ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) :
    zoneSide (zoneCascadeLeft j z).right = z.home :: zoneSide z.right ∧
    zoneSide (zoneCascadeLeft j z).left = (zoneSide z.left).tail :=
  zoneSide_cascadeRight j hj z.swap hl hr hdonor hroom

/-- **The left cascade restores the half-full discipline below its index**: the mirror of
`Turing.zoneCascadeRight_lengths`. [AB09, §1.7]

**Proof sketch.** `Turing.zoneCascadeRight_lengths` applied to the mirror. -/
theorem zoneCascadeLeft_lengths {ℓ : ℕ} (j : ℕ) (hj : j < ℓ) (z : ZoneContents ℓ)
    (hl : ∀ k (hk : k < j), z.left ⟨k, by omega⟩ = [])
    (hr : ∀ k (hk : k < j), (z.right ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : 2 ^ j ≤ (z.left ⟨j, hj⟩).length)
    (hroom : (z.right ⟨j, hj⟩).length + 2 ^ j ≤ zoneCapacity j) :
    (∀ k (hk : k < j),
      ((zoneCascadeLeft j z).left ⟨k, by omega⟩).length = 2 ^ k ∧
      ((zoneCascadeLeft j z).right ⟨k, by omega⟩).length = 2 ^ k) ∧
    ((zoneCascadeLeft j z).left ⟨j, hj⟩).length = (z.left ⟨j, hj⟩).length - 2 ^ j ∧
    ((zoneCascadeLeft j z).right ⟨j, hj⟩).length = (z.right ⟨j, hj⟩).length + 2 ^ j :=
  zoneCascadeRight_lengths j hj z.swap hl hr hdonor hroom

/-- The cascade in direction `dir` (`true` is a right head move). -/
def zoneCascade {ℓ : ℕ} (dir : Bool) (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  if dir then zoneCascadeRight j z else zoneCascadeLeft j z

/-- **The scanned index of a rebalance** (design §13d, G4 step 1): for a head move in
direction `dir`, the least level whose zone on the *feeding* side (the right stack for a right
move, the left for a left move) is nonempty; `ℓ` when every feeding zone is empty. [AB09,
§1.7]: "the smallest `i₀` such that `R_{i₀}` is not empty", the *index* of the shift. -/
def zoneShiftIndex {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : ℕ :=
  (List.finRange ℓ).findIdx fun i => !(z.words dir i).isEmpty

/-- The scanned index is at most the number of laid-out levels. -/
theorem zoneShiftIndex_le {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) :
    zoneShiftIndex dir z ≤ ℓ := by
  have h := List.findIdx_le_length (p := fun i => !(z.words dir i).isEmpty)
    (xs := List.finRange ℓ)
  simpa [zoneShiftIndex] using h

/-- Every feeding zone below the scanned index is empty.

**Proof sketch.** `List.not_of_lt_findIdx` at the position of the level in `List.finRange`. -/
theorem zoneShiftIndex_empty {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) (i : Fin ℓ)
    (hi : i.val < zoneShiftIndex dir z) : z.words dir i = [] := by
  have h := List.not_of_lt_findIdx (p := fun i => !(z.words dir i).isEmpty)
    (xs := List.finRange ℓ) hi
  simp only [List.getElem_finRange, Bool.not_eq_eq_eq_not, Bool.not_false,
    List.isEmpty_iff] at h
  simpa using h

/-- Below `ℓ`, the feeding zone at the scanned index is nonempty.

**Proof sketch.** `List.findIdx_getElem` at the found position. -/
theorem zoneShiftIndex_nonempty {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ)
    (h : zoneShiftIndex dir z < ℓ) : z.words dir ⟨zoneShiftIndex dir z, h⟩ ≠ [] := by
  have hl : (List.finRange ℓ).findIdx (fun i => !(z.words dir i).isEmpty) <
      (List.finRange ℓ).length := by simpa [zoneShiftIndex] using h
  have h' := List.findIdx_getElem (p := fun i => !(z.words dir i).isEmpty)
    (xs := List.finRange ℓ) (w := hl)
  simp only [List.getElem_finRange, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff] at h'
  simpa [zoneShiftIndex] using h'

/-- The scanned index is `j` when every feeding zone below `j` is empty and the one at `j` is
not; the characterization the extension lemma uses.

**Proof sketch.** `List.findIdx_eq` at position `j` of `List.finRange ℓ`. -/
theorem zoneShiftIndex_eq {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) (j : ℕ) (hj : j < ℓ)
    (hbelow : ∀ i : Fin ℓ, i.val < j → z.words dir i = [])
    (hat : z.words dir ⟨j, hj⟩ ≠ []) : zoneShiftIndex dir z = j := by
  unfold zoneShiftIndex
  rw [List.findIdx_eq (by simpa using hj)]
  constructor
  · simpa [List.getElem_finRange] using hat
  · intro i hi
    simpa [List.getElem_finRange] using hbelow ⟨i, by omega⟩ hi

/-- The scanned index equals `ℓ` exactly when every feeding zone is empty.

**Proof sketch.** `List.findIdx_lt_length` and the bound `Turing.zoneShiftIndex_le`. -/
theorem zoneShiftIndex_eq_length_iff {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) :
    zoneShiftIndex dir z = ℓ ↔ ∀ i, z.words dir i = [] := by
  constructor
  · intro h i
    exact zoneShiftIndex_empty dir z i (by omega)
  · intro h
    have hle := zoneShiftIndex_le dir z
    by_contra hne
    exact zoneShiftIndex_nonempty dir z (by omega) (h _)

/-- **The total guarded rebalance** for a head move in direction `dir` (design §13d, decision
13d.3, in the A-S2 totality form): the cascade at the scanned index when that index is below
`ℓ`, the identity when every feeding zone is empty (the case the extension row serves). It is
defined for every contents; the classical fullness discipline is not assumed. [AB09, §1.7] -/
def zoneRebalance {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  if zoneShiftIndex dir z < ℓ then zoneCascade dir (zoneShiftIndex dir z) z else z

/-- With no nonempty feeding zone the rebalance is the identity. -/
theorem zoneRebalance_of_le {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ)
    (h : ℓ ≤ zoneShiftIndex dir z) : zoneRebalance dir z = z := by
  simp [zoneRebalance, show ¬ zoneShiftIndex dir z < ℓ by omega]

/-- **A right rebalance realizes one virtual right move** under the classical left state at
its index (left zones below the index full, room at the index for one pass); the right-side
hypotheses of `Turing.zoneSide_cascadeRight` are supplied by the scan. [AB09, §1.7]

**Proof sketch.** Unfold the guard; the scan gives the empty lower right zones
(`Turing.zoneShiftIndex_empty`) and the nonempty donor (`Turing.zoneShiftIndex_nonempty`), and
`Turing.zoneSide_cascadeRight` finishes. -/
theorem zoneSide_rebalance_right {ℓ : ℕ} (z : ZoneContents ℓ) (h : zoneShiftIndex true z < ℓ)
    (hl : ∀ k (hk : k < zoneShiftIndex true z),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hroom : (z.left ⟨zoneShiftIndex true z, h⟩).length + 2 ^ (zoneShiftIndex true z - 1) ≤
      zoneCapacity (zoneShiftIndex true z)) :
    zoneSide (zoneRebalance true z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneRebalance true z).right = (zoneSide z.right).tail := by
  have hr : ∀ k (hk : k < zoneShiftIndex true z), z.right ⟨k, by omega⟩ = [] :=
    fun k hk => zoneShiftIndex_empty true z ⟨k, by omega⟩ hk
  have hd : z.right ⟨zoneShiftIndex true z, h⟩ ≠ [] := zoneShiftIndex_nonempty true z h
  simp only [zoneRebalance, if_pos h, zoneCascade, if_true]
  exact zoneSide_cascadeRight _ h z hr hl hd hroom

/-- The rebalance in direction `false` is the mirror of the rebalance in direction `true`. -/
theorem zoneRebalance_false {ℓ : ℕ} (z : ZoneContents ℓ) :
    zoneRebalance false z = (zoneRebalance true z.swap).swap := by
  have hi : zoneShiftIndex false z = zoneShiftIndex true z.swap := rfl
  by_cases h : zoneShiftIndex true z.swap < ℓ <;>
    simp [zoneRebalance, zoneCascade, zoneCascadeLeft, hi, h]

/-- **The rebalance keeps every level above its scanned index**, on both sides and in both
directions: the zones a rebalance may change are those of levels `0` to the index.

**Proof sketch.** A guarded identity changes nothing; otherwise this is
`Turing.zoneCascadeRight_frame` at the index, read through the mirror for `dir = false`. -/
theorem zoneRebalance_frame {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) (k : Fin ℓ)
    (hk : zoneShiftIndex dir z < k.val) :
    (zoneRebalance dir z).left k = z.left k ∧ (zoneRebalance dir z).right k = z.right k := by
  cases dir
  · have hk' : zoneShiftIndex true z.swap < k.val := hk
    rw [zoneRebalance_false]
    unfold zoneRebalance
    split_ifs with h
    · simp only [zoneCascade, if_true]
      exact (zoneCascadeRight_frame _ z.swap k hk').symm
    · exact ⟨rfl, rfl⟩
  · unfold zoneRebalance
    split_ifs with h
    · simp only [zoneCascade, if_true]
      exact zoneCascadeRight_frame _ z k hk
    · exact ⟨rfl, rfl⟩

/-- **The extension by one level** (design §13d, decision 13d.2): the contents with level `ℓ`
laid out on both sides, each new zone **half full of virtual blanks** (`2^ℓ` stored blank
cells, the inner half of capacity `2 · 2^ℓ`), every other field unchanged. [AB09, §1.7]:
zones are made half full "the first time we encounter it". -/
def ZoneContents.extend {ℓ : ℕ} (z : ZoneContents ℓ) : ZoneContents (ℓ + 1) where
  home := z.home
  left := Fin.lastCases (List.replicate (2 ^ ℓ) none) z.left
  right := Fin.lastCases (List.replicate (2 ^ ℓ) none) z.right
  left_le := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, List.length_replicate, Fin.val_last, zoneCapacity]
      omega
    · simpa only [Fin.lastCases_castSucc, Fin.coe_castSucc] using z.left_le j
  right_le := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, List.length_replicate, Fin.val_last, zoneCapacity]
      omega
    · simpa only [Fin.lastCases_castSucc, Fin.coe_castSucc] using z.right_le j

/-- The extension keeps the old levels' words. -/
theorem ZoneContents.extend_words_castSucc {ℓ : ℕ} (side : Bool) (z : ZoneContents ℓ)
    (i : Fin ℓ) : z.extend.words side i.castSucc = z.words side i := by
  cases side <;> simp [ZoneContents.words, ZoneContents.extend]

/-- The extension's new level holds `2^ℓ` stored blank cells on each side. -/
theorem ZoneContents.extend_words_last {ℓ : ℕ} (side : Bool) (z : ZoneContents ℓ) :
    z.extend.words side (Fin.last ℓ) = List.replicate (2 ^ ℓ) none := by
  cases side <;> simp [ZoneContents.words, ZoneContents.extend]

/-- The extension pads each represented half-word with `2^ℓ` virtual blanks at its outer end.

**Proof sketch.** `List.finRange_succ_last` splits the levels into the old ones, embedded by
`Fin.castSucc`, and the new last one; the concatenation splits accordingly. -/
theorem zoneSide_extend {ℓ : ℕ} (side : Bool) (z : ZoneContents ℓ) :
    zoneSide (z.extend.words side) = zoneSide (z.words side) ++ List.replicate (2 ^ ℓ) none := by
  unfold zoneSide
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp [ZoneContents.extend_words_castSucc, ZoneContents.extend_words_last]

/-- **After a short scan, the extended contents scan to the new level**: when every feeding
zone of `z` is empty (scanned index `ℓ`), the extension's scanned index is `ℓ`, now below the
level count `ℓ + 1`, since the new feeding zone holds `2^ℓ ≥ 1` blank cells.

**Proof sketch.** `Turing.zoneShiftIndex_eq` at `ℓ`: the old levels are the old zones, all
empty by `Turing.zoneShiftIndex_eq_length_iff`, and the new one is a nonempty replicate. -/
theorem zoneShiftIndex_extend {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ)
    (h : zoneShiftIndex dir z = ℓ) : zoneShiftIndex dir z.extend = ℓ := by
  have hall := (zoneShiftIndex_eq_length_iff dir z).mp h
  apply zoneShiftIndex_eq dir z.extend ℓ (by omega)
  · intro i hi
    have : i = (⟨i.val, hi⟩ : Fin ℓ).castSucc := Fin.ext rfl
    rw [this, ZoneContents.extend_words_castSucc]
    exact hall _
  · have : (⟨ℓ, by omega⟩ : Fin (ℓ + 1)) = Fin.last ℓ := rfl
    rw [this, ZoneContents.extend_words_last]
    exact List.ne_nil_of_length_pos (by rw [List.length_replicate]; exact Nat.two_pow_pos ℓ)

/-- The extension does not move a scanned index that is already below `ℓ`.

**Proof sketch.** `Turing.zoneShiftIndex_eq` at the old index: the zones up to it are the old
ones. -/
theorem zoneShiftIndex_extend_of_lt {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ)
    (h : zoneShiftIndex dir z < ℓ) : zoneShiftIndex dir z.extend = zoneShiftIndex dir z := by
  apply zoneShiftIndex_eq dir z.extend _ (by omega)
  · intro i hi
    have : i = (⟨i.val, by omega⟩ : Fin ℓ).castSucc := Fin.ext rfl
    rw [this, ZoneContents.extend_words_castSucc]
    exact zoneShiftIndex_empty dir z _ hi
  · have : (⟨zoneShiftIndex dir z, by omega⟩ : Fin (ℓ + 1)) = (⟨_, h⟩ : Fin ℓ).castSucc :=
      Fin.ext rfl
    rw [this, ZoneContents.extend_words_castSucc]
    exact zoneShiftIndex_nonempty dir z h

/-- **The virtual tape a track represents** (design §13d, G3), relative to its head: position
`0` is the home cell, positive positions read the right half-word inner end first, negative
positions the left one; a stored virtual blank (`none` in a zone word) and a position beyond the
stored words both read as blank. [AB09, §1.7]: the simulated tape, read off the zones. -/
def zoneTrackTape {ℓ : ℕ} (z : ZoneContents ℓ) (p : ℤ) : Option Bool :=
  if p = 0 then z.home
  else if 0 < p then ((zoneSide z.right)[(p - 1).toNat]?).join
  else ((zoneSide z.left)[(-p - 1).toNat]?).join

/-- Empty contents represent the blank tape. -/
theorem zoneTrackTape_empty (ℓ : ℕ) : zoneTrackTape (ZoneContents.empty ℓ) = fun _ => none := by
  funext p
  simp [zoneTrackTape, ZoneContents.empty, zoneSide]

/-- The mirror reverses the represented tape about the head.

**Proof sketch.** Unfold; the two half-words exchange and `-p` exchanges the sign cases. -/
theorem zoneTrackTape_swap {ℓ : ℕ} (z : ZoneContents ℓ) (p : ℤ) :
    zoneTrackTape z.swap p = zoneTrackTape z (-p) := by
  unfold zoneTrackTape
  by_cases h0 : p = 0
  · subst h0
    simp [ZoneContents.swap]
  · by_cases hp : 0 < p
    · simp only [h0, hp, if_false, if_true, neg_eq_zero, show ¬ 0 < -p by omega]
      rw [neg_neg]
      rfl
    · simp only [h0, hp, if_false, neg_eq_zero, show 0 < -p by omega, if_true]
      rw [show -p - 1 = -p - 1 from rfl]
      rfl

/-- **The extension does not change the represented tape**: the padding cells are virtual
blanks at the outer ends.

**Proof sketch.** `Turing.zoneSide_extend`; a lookup in the padded word is the old lookup
inside the old word and a stored blank beyond it, and both read as blank there. -/
theorem zoneTrackTape_extend {ℓ : ℕ} (z : ZoneContents ℓ) :
    zoneTrackTape z.extend = zoneTrackTape z := by
  have hr := zoneSide_extend true z
  have hl := zoneSide_extend false z
  simp only [ZoneContents.words, if_true, Bool.false_eq_true, if_false] at hr hl
  have key : ∀ (w : List (Option Bool)) (n : ℕ),
      ((w ++ List.replicate (2 ^ ℓ) none)[n]?).join = (w[n]?).join := by
    intro w n
    by_cases hn : n < w.length
    · rw [List.getElem?_append_left hn]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate,
        List.getElem?_eq_none (show w.length ≤ n by omega)]
      split_ifs <;> rfl
  funext p
  unfold zoneTrackTape
  rw [hr, hl, key, key]
  rfl

/-- Writing the home changes the represented tape at the head only. -/
theorem zoneTrackTape_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool) (p : ℤ) :
    zoneTrackTape (zoneHomeWrite z v) p = if p = 0 then v else zoneTrackTape z p := by
  unfold zoneTrackTape zoneHomeWrite
  split_ifs <;> rfl

/-- **The cascade's new home is the right word's first cell** under the classical pre-state of
`Turing.zoneSide_cascadeRight`. This is the one fact about the cascade's internals that the
represented-tape statement needs beyond the landed lemmas. [AB09, §1.7]: the leftmost symbol of
`R_{i₀}` is put in position `0`.

**Proof sketch.** The shift pairs keep the home (both wrappers copy it), so the home after the
cascade is the one the central move sets: the head of zone `0` on the right after the
descending pass. That pass keeps the right concatenation (`Turing.zoneSide_shiftInW`) and
leaves zone `0` nonempty (each descending prefix of the nonempty donor is nonempty, as in the
proof of `Turing.zoneSide_cascadeRight`), and zone `0` is the first word of the
concatenation, so its head is the right word's head. Formally the induction on `j` is shared
with `Turing.zoneSide_cascadeRight` (the private `zoneCascadeRight_classical`): at `0` the
cascade is the central move, which sets the home to the donor's head; at `j + 1` the outer step
pair keeps the right concatenation and leaves the pre-state at `j`. -/
theorem zoneCascadeRight_home {ℓ : ℕ} (j : ℕ) (hj : j < ℓ) (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j), (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ [])
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) :
    (zoneCascadeRight j z).home = (zoneSide z.right).headI :=
  (zoneCascadeRight_classical j hj z hr hl hdonor hroom).2

/-- **The cascade realizes the virtual right move on the represented tape**: under the
classical pre-state of `Turing.zoneSide_cascadeRight`, the tape the cascade represents is the
old one read one cell further right. [AB09, §1.7]

**Proof sketch.** Positions `p > 0` read the right word's tail one place earlier, `p = 0` the
new home, which is the right word's head (`Turing.zoneCascadeRight_home`; the right word is
nonempty because it contains the donor), and `p < 0` the left word with the old home pushed
on (`Turing.zoneSide_cascadeRight`). -/
theorem zoneTrackTape_cascadeRight {ℓ : ℕ} (j : ℕ) (hj : j < ℓ) (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j), (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ [])
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) (p : ℤ) :
    zoneTrackTape (zoneCascadeRight j z) p = zoneTrackTape z (p + 1) := by
  obtain ⟨hL, hR⟩ := zoneSide_cascadeRight j hj z hr hl hdonor hroom
  have hH := zoneCascadeRight_home j hj z hr hl hdonor hroom
  have hne : zoneSide z.right ≠ [] := by
    intro he
    apply hdonor
    have hmem : z.right ⟨j, hj⟩ ⊆ zoneSide z.right := by
      intro a ha
      exact List.mem_flatMap.mpr ⟨⟨j, hj⟩, List.mem_finRange _, ha⟩
    rw [he] at hmem
    exact List.eq_nil_iff_forall_not_mem.mpr fun a ha => by simpa using hmem ha
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  unfold zoneTrackTape
  rw [hL, hR, hH, hcs]
  by_cases h0 : p = 0
  · subst h0
    simp
  · by_cases hp : 0 < p
    · simp only [h0, hp, if_false, if_true, show p + 1 ≠ 0 by omega, show 0 < p + 1 by omega,
        List.tail_cons]
      rw [show (p + 1 - 1).toNat = (p - 1).toNat + 1 by omega, List.getElem?_cons_succ]
    · by_cases hm : p = -1
      · subst hm
        simp
      · simp only [h0, hp, if_false, show p + 1 ≠ 0 by omega, show ¬ 0 < p + 1 by omega]
        rw [show (-p - 1).toNat = (-(p + 1) - 1).toNat + 1 by omega, List.getElem?_cons_succ]

/-- **The left cascade realizes the virtual left move on the represented tape**: the mirror of
`Turing.zoneTrackTape_cascadeRight`. [AB09, §1.7]

**Proof sketch.** Through the mirror (`Turing.zoneTrackTape_swap`): the left cascade is the
right cascade of the mirror, read back through the mirror. -/
theorem zoneTrackTape_cascadeLeft {ℓ : ℕ} (j : ℕ) (hj : j < ℓ) (z : ZoneContents ℓ)
    (hl : ∀ k (hk : k < j), z.left ⟨k, by omega⟩ = [])
    (hr : ∀ k (hk : k < j), (z.right ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.left ⟨j, hj⟩ ≠ [])
    (hroom : (z.right ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) (p : ℤ) :
    zoneTrackTape (zoneCascadeLeft j z) p = zoneTrackTape z (p - 1) := by
  have h := zoneTrackTape_cascadeRight j hj z.swap hl hr hdonor hroom (-p)
  unfold zoneCascadeLeft
  rw [zoneTrackTape_swap, h, zoneTrackTape_swap]
  congr 1
  omega

/-- **A left rebalance realizes one virtual left move** under the classical right state at its
index: the mirror of `Turing.zoneSide_rebalance_right`. [AB09, §1.7]

**Proof sketch.** `Turing.zoneRebalance_false` writes the left rebalance as the mirrored right
one; `Turing.zoneSide_rebalance_right` applies to the mirror. -/
theorem zoneSide_rebalance_left {ℓ : ℕ} (z : ZoneContents ℓ) (h : zoneShiftIndex false z < ℓ)
    (hr : ∀ k (hk : k < zoneShiftIndex false z),
      (z.right ⟨k, by omega⟩).length = zoneCapacity k)
    (hroom : (z.right ⟨zoneShiftIndex false z, h⟩).length + 2 ^ (zoneShiftIndex false z - 1) ≤
      zoneCapacity (zoneShiftIndex false z)) :
    zoneSide (zoneRebalance false z).right = z.home :: zoneSide z.right ∧
    zoneSide (zoneRebalance false z).left = (zoneSide z.left).tail := by
  rw [zoneRebalance_false]
  exact zoneSide_rebalance_right z.swap h hr hroom

/-- **A right rebalance moves the represented tape one cell**: under the classical left state
at its scanned index (below `ℓ`), the tape the rebalanced track represents is the old one read
one cell further right. This is the per-track honesty statement the Hennie–Stearns assembly
consumes. [AB09, §1.7]

**Proof sketch.** Unfold the guard; the scan supplies the right-side hypotheses
(`Turing.zoneShiftIndex_empty`, `Turing.zoneShiftIndex_nonempty`) and
`Turing.zoneTrackTape_cascadeRight` finishes. -/
theorem zoneTrackTape_rebalance_right {ℓ : ℕ} (z : ZoneContents ℓ)
    (h : zoneShiftIndex true z < ℓ)
    (hl : ∀ k (hk : k < zoneShiftIndex true z),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hroom : (z.left ⟨zoneShiftIndex true z, h⟩).length + 2 ^ (zoneShiftIndex true z - 1) ≤
      zoneCapacity (zoneShiftIndex true z)) (p : ℤ) :
    zoneTrackTape (zoneRebalance true z) p = zoneTrackTape z (p + 1) := by
  have hr : ∀ k (hk : k < zoneShiftIndex true z), z.right ⟨k, by omega⟩ = [] :=
    fun k hk => zoneShiftIndex_empty true z ⟨k, by omega⟩ hk
  have hd : z.right ⟨zoneShiftIndex true z, h⟩ ≠ [] := zoneShiftIndex_nonempty true z h
  simp only [zoneRebalance, if_pos h, zoneCascade, if_true]
  exact zoneTrackTape_cascadeRight _ h z hr hl hd hroom p

/-- **A left rebalance moves the represented tape one cell the other way**: the mirror of
`Turing.zoneTrackTape_rebalance_right`. [AB09, §1.7]

**Proof sketch.** Through `Turing.zoneRebalance_false` and `Turing.zoneTrackTape_swap`. -/
theorem zoneTrackTape_rebalance_left {ℓ : ℕ} (z : ZoneContents ℓ)
    (h : zoneShiftIndex false z < ℓ)
    (hr : ∀ k (hk : k < zoneShiftIndex false z),
      (z.right ⟨k, by omega⟩).length = zoneCapacity k)
    (hroom : (z.right ⟨zoneShiftIndex false z, h⟩).length + 2 ^ (zoneShiftIndex false z - 1) ≤
      zoneCapacity (zoneShiftIndex false z)) (p : ℤ) :
    zoneTrackTape (zoneRebalance false z) p = zoneTrackTape z (p - 1) := by
  rw [zoneRebalance_false, zoneTrackTape_swap,
    zoneTrackTape_rebalance_right z.swap h hr hroom, zoneTrackTape_swap]
  congr 1
  omega

end Turing
