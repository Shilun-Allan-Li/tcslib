/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation

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

## Status: statement skeleton (§13 statement phase, tranche A-S2, round 2)

Definitions are real; every contract is `sorry`d with a proof sketch. The
round-1 gate (`audits/zone-infra-findings.md`) returned one blocker
(A-S2-1, repaired here: the inward room premise removed, the wrappers
split, the cascade statements added) and docstring corrections (A-S2-4,
applied).

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
  `Turing.zoneCascadeRight_lengths`, `Turing.zoneCascade_cost_le` — the
  classical rebalance as a cascade of pairwise ops: it realizes one
  virtual right move, leaves every inner level half-full, and its summed
  row budgets stay geometric.
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
  sorry

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
  sorry

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
  sorry

/-! ### The represented word -/

/-- The virtual half-word one side represents: the zone words
concatenated inner-first. -/
def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i

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
  sorry

/-- Outward rebalancing never changes the represented half-word.

**Proof sketch.** A disabled guard gives the identity. When enabled, the
adjacent two-zone segment is literally re-associated:
`take q ++ (drop q ++ wᵢ) = wᵢ₋₁ ++ wᵢ` at the cutoff `q = 2^(i-1)`. -/
theorem zoneSide_shiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftOutW i w) = zoneSide w := by
  sorry

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
  sorry

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
  left_le := by sorry
  right_le := by sorry

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
  left_le := by sorry
  right_le := by sorry

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
  sorry

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
  left_le := by sorry
  right_le := by sorry

/-- The mirrored left step. -/
def zoneMoveLeft {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    ZoneContents ℓ where
  home := ((z.left ⟨0, hℓ⟩).headI : Option Bool)
  left := fun j => if j.val = 0 then (z.left j).tail else z.left j
  right := fun j => if j.val = 0 then z.home :: z.right j else z.right j
  left_le := by sorry
  right_le := by sorry

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
  sorry

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

/-- The cascade realizes exactly one virtual right move. Preconditions are
the classical pre-state at index `j`: on the right, zones below `j` empty
and the donor `j` nonempty; on the left, zones below `j` full.

**Proof sketch** (the round-1 audit's schedule analysis, adopted as the
binding route): on the descending pass each inward-right guard fires into
an empty lower zone and each outward-left guard fires from a full lower
zone with room above; after the head step, the ascending pass re-fires the
same guards on the half-full intermediate state. Order preservation of the
raw ops (`zoneSide_shiftInW`/`OutW`) and the single nonempty level-zero pop
(`zoneSide_moveRight`) give the stated word transformation. -/
theorem zoneSide_cascadeRight {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ []) :
    zoneSide (zoneCascadeRight j z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail := by
  sorry

/-- The cascade restores the half-full discipline below its index: after a
classical right move at index `j` from a donor holding at least `2^j`
cells, every level below `j` is half-full on both sides, the right donor
loses exactly `2^j` cells, and the left zone `j` gains exactly `2^j`.

**Proof sketch.** Track the two passes level by level (the round-1 audit's
ledger): the descending pass makes each lower receiving word half-full and
leaves the remainder upstairs; the ascending pass halves the level-zero
surplus back upward symmetrically. -/
theorem zoneCascadeRight_lengths {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : 2 ^ j ≤ (z.right ⟨j, hj⟩).length) :
    (∀ k (hk : k < j),
      ((zoneCascadeRight j z).right ⟨k, by omega⟩).length = 2 ^ k ∧
      ((zoneCascadeRight j z).left ⟨k, by omega⟩).length = 2 ^ k) ∧
    ((zoneCascadeRight j z).right ⟨j, hj⟩).length =
      (z.right ⟨j, hj⟩).length - 2 ^ j ∧
    ((zoneCascadeRight j z).left ⟨j, hj⟩).length =
      (z.left ⟨j, hj⟩).length + 2 ^ j := by
  sorry

/-- The cascade's summed row budgets stay geometric: the charge lemma the
Hennie-Stearns amortization consumes (two shift pairs per level, each
within the row budget `2^i + i + 1`).

**Proof sketch.** `i + 1 ≤ 2^i` for `i ≥ 1`, so each summand is at most
`4 · 2 · 2^i = 8 · 2^i`, and the geometric sum over `1 ≤ i ≤ j` is
`8 · (2^(j+1) - 2) ≤ 16 · 2^j` — the round-1 audit's charge calculation. -/
theorem zoneCascade_cost_le (j : ℕ) :
    ∑ i ∈ Finset.range j, 4 * (2 ^ (i + 1) + (i + 1) + 1) ≤ 16 * 2 ^ j := by
  sorry

/-! ### The machine rows -/

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
  sorry

end Turing
