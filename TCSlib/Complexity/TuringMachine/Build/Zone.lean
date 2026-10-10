/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the zoned tape carrier (Z2)

The zone representation of the machine-construction library
(`machine-library-design.md` §13, Z2; decisions 13.1 and 13.2): the data
of two stacks of **zones** — level `i` holding up to `2 · 2^i` virtual
cells per side — realized on one physical binary tape around a two-cell
home, with each virtual `Option Bool` cell stored as a **paired
presence/data cell** (decision 13.2; the `SweepAlphabet` product cells of
`Robustness/SingleTape.lean` are the in-repo precedent this replaces with
pairing, keeping the binary alphabet). This is the Hennie-Stearns
representation ([AB09] §1.7): the virtual head always reads at the home,
and locality is restored by per-level rebalancing shifts whose costs are
geometric in the level.

## Design (13a; spec-time refinements, amended by the round-1 audit)

* **The carrier is data, the invariant is the consumer's.** `ZoneContents`
  carries per-zone words bounded by capacity; the Hennie-Stearns
  `{empty, half, full}` fullness discipline, the `2^i`-credit amortization,
  and the simulation theorem live with the consumer (plan §2.1).
* **Shifts are pairwise, order-preserving, and totally guarded** (round-1
  repair, finding A-S2-1): the level-`i` inward shift moves the inner
  `2^(i-1)` stored cells of zone `i` into the **empty** zone `i - 1`, and
  carries **no room premise** — it removes cells from the donor, so a full
  donor is always a legal source. The outward shift moves the outer half
  of a **full** zone `i - 1` onto the front of zone `i`, and its room
  condition on the receiving zone lives **inside its guard**. Outside its
  guard every operation is the identity, and the machine rows realize the
  total guarded operation — identity branch included. The classical
  multi-level rebalance is the descending/move/ascending cascade of these
  ops (`zoneCascadeRight` below), whose represented-word, length, and
  geometric-cost statements are part of this gate per the round-1 audit.
* **One shift machine per direction and side**, taking the level in unary
  on the scratch tape: the Hennie-Stearns simulator is a single machine,
  so the level cannot be baked into finite control.
* **Left/right asymmetry of the cell pairing** is fixed by the layout
  (below) and documented once: on the right, even offsets carry presence
  bits; on the left, odd offsets do.

## The physical layout

Home: cells `0` (presence) and `1` (data). Right virtual slot `s`: cells
`2s + 2` (presence) and `2s + 3` (data). Left virtual slot `s`: cells
`-2s - 2` (presence) and `-2s - 1` (data). Zone `i` owns the slots
`[zoneBase i, zoneBase i + zoneCapacity i)` of its side, where
`zoneCapacity i = 2 · 2^i` and `zoneBase i = 2 · (2^i - 1)` (the exact sum
of the inner capacities). Every integer cell is owned by exactly one slot
or the home.

## Status: statement skeleton (§13 statement phase, tranche A-S2, round 3)

Definitions are real; every contract is `sorry`d with a proof sketch.
Round 1 (`audits/zone-infra-findings.md`) returned the inward-room blocker
(A-S2-1, repaired: premise removed, wrappers split, cascade added); round
2 (`audits/zone-infra-r2-findings.md`) accepted that repair and returned
one blocker on the new cascade contracts (A-S2-R2-1, repaired: the
top-left room hypotheses added — necessary for the lengths theorem, the
weaker one-pass form for the word theorem — with the `j = 0` and
blocked-cascade regressions).

## Main definitions and results

* `Turing.zoneCellBits`/`Turing.zoneCellOf` — the paired-cell codec.
* `Turing.ZoneContents`, `Turing.zoneTape` — the carrier and its physical
  realization.
* `Turing.zoneSide` — the represented virtual half-word (inner zones
  first).
* `Turing.zoneShiftInW`/`Turing.zoneShiftOutW` — the pure pairwise
  rebalancing ops on one side's family, totally guarded, with
  `Turing.zoneSide_shiftInW`/`Turing.zoneSide_shiftOutW` the honesty
  lemmas: rebalancing never changes the represented word.
* `Turing.zoneShiftIn`/`Turing.zoneShiftOut` — the hypothesis-free
  contents-level wrappers (round-1 repair).
* `Turing.zoneMoveRight`/`Turing.zoneMoveLeft`, `Turing.zoneMove`,
  `Turing.zoneHomeWrite` — the pure head-step and write ops.
* `Turing.zoneShiftInW_full_donor` — the full-donor regression required by
  the round-1 audit: a full donor above an empty zone shifts inward with
  no side condition.
* `Turing.zoneCascadeRight`, `Turing.zoneSide_cascadeRight`,
  `Turing.zoneCascadeRight_lengths`, `Turing.zoneCascade_cost_le`,
  `Turing.zoneCascadeRight_zero`, `Turing.zoneCascadeRight_blocked` — the
  classical rebalance as a cascade of pairwise ops: under the classical
  pre-state **and the top-left room hypotheses** it realizes one virtual
  right move and restores every inner level to half-full; its summed row
  budgets stay geometric; the regressions pin the `j = 0` case and the
  harmlessly blocked full-receiver case.
* `Turing.FinTM.exists_zoneShiftInTM`/`exists_zoneShiftOutTM` — the
  machine rows: one two-tape machine per direction and side, level in
  unary on the scratch tape, exact `O(2^i)` budgets, visited sets inside
  the level-`i` physical extent, realizing the total guarded op.
* `Turing.zoneTape_blank_outside`,
  `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — the cardinality
  exports the Z4 space annotation consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.7, the Hennie-Stearns
  simulation; Exercise 1.6.)
* In-repo precedents: `SweepCell`/`SweepAlphabet`
  (`Robustness/SingleTape.lean`); `ObliviousSetup.lean`'s guide-zone
  layout.
-/

namespace Turing

/-! ### The paired-cell codec (decision 13.2) -/

/-- Encode one virtual `Option Bool` cell as its presence and data bits. -/
def zoneCellBits (v : Option Bool) : Bool × Bool := (v.isSome, v.getD false)

/-- Decode a presence/data bit pair back to the virtual cell. -/
def zoneCellOf (p d : Bool) : Option Bool := if p then some d else none

/-- The codec round-trips (skeleton-time proof; flagged). -/
theorem zoneCellOf_bits (v : Option Bool) :
    zoneCellOf (zoneCellBits v).1 (zoneCellBits v).2 = v := by
  cases v <;> rfl

/-! ### Layout arithmetic -/

/-- The capacity of zone `i`, in virtual cells per side. -/
def zoneCapacity (i : ℕ) : ℕ := 2 * 2 ^ i

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
slot is beyond the stored words (an unoccupied slot, physically blank —
distinct, through the pairing, from an occupied slot storing a blank). -/
def zoneSlot {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) (s : ℕ) :
    Option (Option Bool) :=
  if h : zoneIndex s < ℓ then (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]?
  else none

/-- The physical realization of zone contents: home at cells `0`/`1`,
right slot `s` at `2s + 2`/`2s + 3`, left slot `s` at `-2s - 2`/`-2s - 1`;
occupied slots store their presence and data bits, unoccupied slots and
cells beyond every zone are blank. On the right, even cells (relative to
the slot base) carry presence; on the left the roles are mirrored, so odd
negative offsets carry data — the one asymmetry of the layout, fixed
here. -/
def zoneTape {ℓ : ℕ} (z : ZoneContents ℓ) : ℤ → Option Bool := fun c =>
  if c = 0 then some z.home.isSome
  else if c = 1 then some (z.home.getD false)
  else if 2 ≤ c then
    let n := (c - 2).toNat
    match zoneSlot z.right (n / 2) with
    | some v => some (if n % 2 = 0 then v.isSome else v.getD false)
    | none => none
  else
    let n := (-c - 1).toNat
    match zoneSlot z.left (n / 2) with
    | some v => some (if n % 2 = 1 then v.isSome else v.getD false)
    | none => none

/-- The empty contents (blank home, every zone empty). -/
def ZoneContents.empty (ℓ : ℕ) : ZoneContents ℓ where
  home := none
  left := fun _ => []
  right := fun _ => []
  left_le := fun _ => by simp
  right_le := fun _ => by simp

/-- The empty contents realize the almost-blank tape: the home pair
stores the blank cell, and every other physical cell is blank.

**Proof sketch.** `zoneSlot` of the empty family is `none` at every slot
(`List.getElem?` of `[]`), so both side branches of `zoneTape` return
`none`; the home cells compute `zoneCellBits none = (false, false)`. -/
theorem zoneTape_empty (ℓ : ℕ) (c : ℤ) :
    zoneTape (ZoneContents.empty ℓ) c =
      if c = 0 then some false else if c = 1 then some false else none := by
  simp [zoneTape, ZoneContents.empty, zoneSlot]

/-- Cells beyond the physical extent of `ℓ` levels are blank, for every
contents: the zones' slots stop at `zoneBase ℓ`, so the tape is `none`
outside `[-(2 * zoneBase ℓ + 1), 2 * zoneBase ℓ + 1]`.

**Proof sketch.** A cell at distance beyond the extent maps to a slot
`s ≥ zoneBase ℓ`; `zoneIndex_eq_iff` puts `zoneIndex s ≥ ℓ`, so `zoneSlot`
returns `none` by its guard. (The round-1 audit computed the sharper
asymmetric extent `[-2·zoneBase ℓ, 2·zoneBase ℓ + 1]`; the stated
symmetric bound is the safe envelope.) -/
theorem zoneTape_blank_outside {ℓ : ℕ} (z : ZoneContents ℓ) (c : ℤ)
    (hc : (2 * zoneBase ℓ + 1 : ℤ) < |c|) : zoneTape z c = none := by
  have hs (w : Fin ℓ → List (Option Bool)) (s : ℕ)
      (hb : zoneBase ℓ ≤ s) : zoneSlot w s = none := by
    unfold zoneSlot
    split_ifs with hi
    · have htop := ((zoneIndex_eq_iff s (zoneIndex s)).mp rfl).2
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.succ_le_of_lt hi)
      unfold zoneBase at *
      omega
    · rfl
  have h0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; omega
  have h1 : c ≠ 1 := by intro h; rw [h] at hc; change 2 * (zoneBase ℓ : ℤ) + 1 < 1 at hc; omega
  simp only [zoneTape, if_neg h0, if_neg h1]
  by_cases hpos : 2 ≤ c
  · rw [if_pos hpos]
    rw [abs_of_nonneg (by omega : 0 ≤ c)] at hc
    have hb : zoneBase ℓ ≤ (c - 2).toNat / 2 := by omega
    simp only [hs z.right _ hb]
  · rw [if_neg hpos]
    rw [abs_of_neg (by omega : c < 0)] at hc
    have hb : zoneBase ℓ ≤ (-c - 1).toNat / 2 := by omega
    simp only [hs z.left _ hb]

/-! ### The represented word -/

/-- The virtual half-word one side represents: the zone words
concatenated inner-first. -/
def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i

private theorem zoneSide_succ {n : ℕ} (w : Fin (n + 1) → List (Option Bool)) :
    zoneSide w = w 0 ++ zoneSide (fun k => w k.succ) := by
  simp [zoneSide, List.finRange_succ, List.flatMap_map]

/-- Replacing two adjacent zone words with the same concatenation preserves
the represented side. Induct on the number of levels, peeling off the
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

/-- Writing the home changes exactly the two home cells of the physical
tape.

**Proof sketch.** `zoneTape` consults `home` only in its first two
branches; every slot branch reads the untouched families. -/
theorem zoneTape_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool)
    (c : ℤ) (h0 : c ≠ 0) (h1 : c ≠ 1) :
    zoneTape (zoneHomeWrite z v) c = zoneTape z c := by
  simp only [zoneTape, zoneHomeWrite, if_neg h0, if_neg h1]

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

/-- The recursive descent and ascent only touch levels at or below their
index. Induction peels off the outer pair; the base move touches zero. -/
private theorem zoneCascadeRight_frame {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ)
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
restoration is **not** used. -/
theorem zoneSide_cascadeRight {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ [])
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) :
    zoneSide (zoneCascadeRight j z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail := by
  induction j generalizing z with
  | zero =>
    have hroom0 : (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      simpa using hroom
    simpa only [zoneCascadeRight, List.range_zero, List.reverse_nil,
      List.foldl_nil, zoneMove, dif_pos hj, dif_pos hroom0] using
      zoneSide_moveRight hj z hroom0 hdonor
  | succ j ih =>
    have hjl : j < ℓ := by omega
    have hroom' : (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤
        zoneCapacity (j + 1) := by simpa using hroom
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
    have hd' : (zoneStepPair (j + 1) z).right ⟨j, hjl⟩ ≠ [] := by
      rw [hactive.1]
      apply List.ne_nil_of_length_pos
      rw [List.length_take]
      exact lt_min (Nat.two_pow_pos j) (List.length_pos_iff.mpr hdonor)
    have hlower : ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length = 2 ^ j := by
      rw [hactive.2.1, List.length_take, hl j (by omega)]
      unfold zoneCapacity
      omega
    have hroomlower : ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length +
        2 ^ (j - 1) ≤ zoneCapacity j := by
      rw [hlower]
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le j 1)
      unfold zoneCapacity
      omega
    have hinner := ih hjl (zoneStepPair (j + 1) z) hr' hl' hd' hroomlower
    rw [zoneCascadeRight_succ, (zoneStepPair_side _ _).1,
      (zoneStepPair_side _ _).2, hinner.1, hinner.2,
      (zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2]
    exact ⟨rfl, rfl⟩

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
    have hm : zoneCascadeRight 0 z = zoneMoveRight hj z hroom0 := by
      simp [zoneCascadeRight, zoneMove, hj, hroom0]
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
    have hr' : ∀ k (hk : k < j), z1.right ⟨k, by omega⟩ = [] := by
      intro k hk
      change (zoneStepPair (j + 1) z).right ⟨k, _⟩ = []
      rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩
        (by dsimp; omega) (by dsimp; omega)).2]
      exact hr k (by omega)
    have hl' : ∀ k (hk : k < j),
        (z1.left ⟨k, by omega⟩).length = zoneCapacity k := by
      intro k hk
      change ((zoneStepPair (j + 1) z).left ⟨k, _⟩).length = _
      rw [(zoneStepPair_frame (j + 1) z ⟨k, by omega⟩
        (by dsimp; omega) (by dsimp; omega)).1]
      exact hl k (by omega)
    have hrlower : (z1.right ⟨j, hjl⟩).length = 2 ^ j := by
      change ((zoneStepPair (j + 1) z).right ⟨j, hjl⟩).length = _
      rw [hactive.1, List.length_take]
      rw [pow_succ] at hdonor
      omega
    have hllower : (z1.left ⟨j, hjl⟩).length = 2 ^ j := by
      change ((zoneStepPair (j + 1) z).left ⟨j, hjl⟩).length = _
      rw [hactive.2.1, List.length_take, hl j (by omega)]
      unfold zoneCapacity
      omega
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
    have hinner := ih hjl z1 hr' hl' (by rw [hrlower]) (by
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
  simpa only [zoneCascadeRight, List.range_zero, List.reverse_nil,
    List.foldl_nil, zoneMove, dif_pos hℓ, dif_pos hroom] using
    zoneSide_moveRight hℓ z hroom hdonor

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
within the row budget `2^i + i + 1`).

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

/-! ### The machine rows -/

/-- The physical bits of a zone word in the order seen moving away from
home. On the left a pair is read data-first, on the right presence-first.
This is the finite word to be staged by a delimited catalog transfer. -/
private def zoneStageWord (side : Bool) (w : List (Option Bool)) : List Bool :=
  w.flatMap fun v =>
    if side then [v.isSome, v.getD false] else [v.getD false, v.isSome]

/-- Each occupied virtual cell contributes exactly two nonblank cells. -/
private theorem zoneStageWord_length (side : Bool) (w : List (Option Bool)) :
    (zoneStageWord side w).length = 2 * w.length := by
  induction w with
  | nil => simp [zoneStageWord]
  | cons v w ih =>
    cases side <;> simp_all [zoneStageWord, Nat.mul_add]

/-- Looking up a physical bit first chooses its virtual cell and then
the appropriate component of that cell's pair.
**Proof sketch.** Peel off two positions with each list cell; quotient by
two chooses the remaining cell, and remainder chooses its component. -/
private theorem zoneStageWord_getElem (side : Bool) (w : List (Option Bool))
    (p : ℕ) :
    (zoneStageWord side w)[p]? = (w[p / 2]?).map (fun v =>
      if p % 2 = 0 then
        if side then v.isSome else v.getD false
      else if side then v.getD false else v.isSome) := by
  induction w generalizing p with
  | nil => simp [zoneStageWord]
  | cons v w ih =>
    cases p with
    | zero => cases side <;> simp [zoneStageWord]
    | succ p =>
      cases p with
      | zero => cases side <;> simp [zoneStageWord]
      | succ p =>
        have hd : (p + 1 + 1) / 2 = p / 2 + 1 := by omega
        have hr : (p + 1 + 1) % 2 = p % 2 := by omega
        cases side <;> simpa [zoneStageWord, hd, hr] using ih p

/-- A slot inside a specified zone reads that zone's word at its local
offset. The existing logarithm theorem supplies the owning level. -/
private theorem zoneStageSlot {ℓ : ℕ} (w : Fin ℓ → List (Option Bool))
    (i : Fin ℓ) (p : ℕ) (hp : p < zoneCapacity i.val) :
    zoneSlot w (zoneBase i.val + p) = (w i)[p]? := by
  have hi : zoneIndex (zoneBase i.val + p) = i.val :=
    (zoneIndex_eq_iff _ _).mpr ⟨by omega, by rw [zoneBase_succ]; omega⟩
  simp [zoneSlot, hi, i.isLt]

/-- The right zone window is exactly the staged word, followed by blanks
up to the zone's capacity. No claim is made about the two boundary cells.
**Proof sketch.** Subtract the physical base, divide the bit offset by
two, and use the owning-slot theorem and paired-word lookup. -/
private theorem zoneStage_rightWindow {ℓ : ℕ} (z : ZoneContents ℓ)
    (i : Fin ℓ) (p : ℕ) (hp : p < 2 * zoneCapacity i.val) :
    zoneTape z (2 * (zoneBase i.val : ℤ) + 2 + p) =
      FinTM.bufferTape (zoneStageWord true (z.right i)) p := by
  have h0 : 2 * (zoneBase i.val : ℤ) + 2 + p ≠ 0 := by omega
  have h1 : 2 * (zoneBase i.val : ℤ) + 2 + p ≠ 1 := by omega
  have h2 : 2 ≤ 2 * (zoneBase i.val : ℤ) + 2 + p := by omega
  have hn : (2 * (zoneBase i.val : ℤ) + 2 + p - 2).toNat =
      2 * zoneBase i.val + p := by omega
  have hd : (2 * zoneBase i.val + p) / 2 = zoneBase i.val + p / 2 := by omega
  have hr : (2 * zoneBase i.val + p) % 2 = p % 2 := by omega
  have hs := zoneStageSlot z.right i (p / 2) (by omega)
  simp only [zoneTape, if_neg h0, if_neg h1, if_pos h2, hn, hd, hr, hs,
    FinTM.bufferTape_nat, zoneStageWord_getElem, ite_true]
  cases (z.right i)[p / 2]? <;> rfl

/-- Reading the left window away from home reverses the two bit roles
within each pair, without reversing the order of the virtual cells.
**Proof sketch.** The negative physical coordinate gives the same local
quotient as on the right, but presence is at odd offsets. -/
private theorem zoneStage_leftWindow {ℓ : ℕ} (z : ZoneContents ℓ)
    (i : Fin ℓ) (p : ℕ) (hp : p < 2 * zoneCapacity i.val) :
    zoneTape z (-(2 * (zoneBase i.val : ℤ)) - 1 - p) =
      FinTM.bufferTape (zoneStageWord false (z.left i)) p := by
  have h0 : -(2 * (zoneBase i.val : ℤ)) - 1 - p ≠ 0 := by omega
  have h1 : -(2 * (zoneBase i.val : ℤ)) - 1 - p ≠ 1 := by omega
  have h2 : ¬ 2 ≤ -(2 * (zoneBase i.val : ℤ)) - 1 - p := by omega
  have hn : (-(-(2 * (zoneBase i.val : ℤ)) - 1 - p) - 1).toNat =
      2 * zoneBase i.val + p := by omega
  have hd : (2 * zoneBase i.val + p) / 2 = zoneBase i.val + p / 2 := by omega
  have hr : (2 * zoneBase i.val + p) % 2 = p % 2 := by omega
  have hs := zoneStageSlot z.left i (p / 2) (by omega)
  simp only [zoneTape, if_neg h0, if_neg h1, if_neg h2, hn, hd, hr, hs,
    FinTM.bufferTape_nat, zoneStageWord_getElem, Bool.false_eq_true, ite_false]
  by_cases he : p % 2 = 0
  · cases (z.left i)[p / 2]? <;> simp [he]
  · have ho : p % 2 = 1 := by omega
    cases (z.left i)[p / 2]? <;> simp [ho]

/-- Both oriented zone windows, including the adjacent delimiter cells,
fit inside the interval allowed by the shift-machine contract. -/
private theorem zoneStage_window_bounds (i : ℕ) (p : ℤ)
    (hp : -1 ≤ p ∧ p ≤ 2 * (zoneCapacity i : ℤ)) :
    (2 * (zoneBase i : ℤ) + 2 + p) ∈
        Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
          (2 * (zoneBase (i + 1) : ℤ) + 2) ∧
      (-(2 * (zoneBase i : ℤ)) - 1 - p) ∈
        Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
          (2 * (zoneBase (i + 1) : ℤ) + 2) := by
  have hb : (zoneBase (i + 1) : ℤ) = zoneBase i + zoneCapacity i := by
    exact_mod_cast zoneBase_succ i
  simp only [Finset.mem_Icc]
  omega

namespace FinTM

/-- **Z2, the inward shift row.** One two-tape machine per side: tape `0`
carries a zoned tape, tape `1` the level in unary (`replicate i true` as a
buffered word). From any configuration holding `zoneTape z` at origin and
the level word at origin, the machine halts at
`zoneTape (zoneShiftIn side i z)` — **realizing the total guarded
operation, identity branch included** (round-1 repair: there is no room
premise, and a false guard means the machine restores the original tape) —
with both heads home, the level word intact, within `c * (2^i + i + 1)`
steps, first return at the halt, the data head inside the level-`i + 1`
physical extent, and the scratch tape's space in the same budget.

**Proof sketch** (fill plan): scan the level word; test the lower zone's
emptiness by one pass over its window (a stored virtual blank occupies two
nonblank cells, so word ends are detectable); on a live guard, stage the
donor's inner `2^(i-1)` pairs through tape `1` with the R3 transfer
discipline and write them inward; on a dead guard, rewind and halt with
the tape untouched. Navigation counters follow the round-1 audit's
geometric-ledger route (anchored binary countdown, `O(2^i)` total carry
work; unary-level initialization polynomial in `i`, absorbed). R2 seams
join the constantly many phases. -/
theorem exists_zoneShiftInTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShiftIn side i z)
            else bufferTape (List.replicate i true)) ∧
          (Z.tm.runFrom d T).workTapePos = (fun _ => 0) ∧
          (Z.tm.runFrom d T).output = [] ∧
          (Z.tm.runFrom d T).inputPos = d.inputPos ∧
          (∀ t < T, (Z.tm.runFrom d t).state ≠ none) ∧
          (∀ j (hj : j.val = 0) (t : ℕ), t ≤ T →
            (Z.tm.runFrom d t).workTapePos j ∈
              Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
                (2 * (zoneBase (i + 1) : ℤ) + 2)) ∧
          (∀ j : Fin Z.k, j.val = 1 →
            Z.tm.spaceUsedByTape d T j ≤ c * (2 ^ i + i + 1)) := by
  sorry

/-- **Z2, the outward shift row**: the mirrored contract realizing the
total guarded outward operation (the room condition is inside the pure
op's guard; a cramped receiver yields the identity), with the same budget
shape, interval clause, and scratch bound.

**Proof sketch** (fill plan): as the inward row with the fullness and
room tests up front (both by bounded window passes) and the transfer
direction reversed; the full lower zone's outer half is staged through
tape `1` and written to zone `i`'s front after its stored word is slid
outward by `2^(i-1)` slots — one extra pass over the level-`i` window,
inside the same geometric budget. -/
theorem exists_zoneShiftOutTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShiftOut side i z)
            else bufferTape (List.replicate i true)) ∧
          (Z.tm.runFrom d T).workTapePos = (fun _ => 0) ∧
          (Z.tm.runFrom d T).output = [] ∧
          (Z.tm.runFrom d T).inputPos = d.inputPos ∧
          (∀ t < T, (Z.tm.runFrom d t).state ≠ none) ∧
          (∀ j (hj : j.val = 0) (t : ℕ), t ≤ T →
            (Z.tm.runFrom d t).workTapePos j ∈
              Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
                (2 * (zoneBase (i + 1) : ℤ) + 2)) ∧
          (∀ j : Fin Z.k, j.val = 1 →
            Z.tm.spaceUsedByTape d T j ≤ c * (2 ^ i + i + 1)) := by
  sorry

end FinTM

/-! ### The cardinality export (consumed by Z4) -/

/-- A head confined to an integer interval visits at most its cardinality.

**Proof sketch.** The visited set is a finite image contained in the
interval by hypothesis; `Finset.card_le_card` and `Int.card_Icc` finish. -/
theorem MultiTapeTM.spaceUsedByTape_le_card_Icc {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (d : Cfg k Symbol State input) (t : ℕ) (i : Fin k) (lo hi : ℤ)
    (h : ∀ u ≤ t, (tm.runFrom d u).workTapePos i ∈ Finset.Icc lo hi) :
    tm.spaceUsedByTape d t i ≤ (hi + 1 - lo).toNat := by
  unfold MultiTapeTM.spaceUsedByTape
  calc
    _ ≤ (Finset.Icc lo hi).card := Finset.card_le_card (by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
      exact h u (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu))
    _ = _ := Int.card_Icc lo hi

end Turing
