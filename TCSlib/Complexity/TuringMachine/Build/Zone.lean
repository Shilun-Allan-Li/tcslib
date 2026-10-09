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

## Design (13a; spec-time refinements recorded here)

* **The carrier is data, the invariant is the consumer's.** `ZoneContents`
  carries per-zone words bounded by capacity; the Hennie-Stearns
  `{empty, half, full}` fullness discipline, the `2^i`-credit amortization,
  and the simulation theorem live with the consumer (plan §2.1), exactly
  as the §12 loop host kept the space ledgers outside.
* **Shifts are pairwise and order-preserving** (spec-time refinement): the
  level-`i` inward shift moves the inner `2^(i-1)` stored cells of zone
  `i` into the empty zone `i - 1`; the outward shift moves the outer half
  of a full zone `i - 1` onto the front of zone `i`. Each preserves the
  represented virtual word *by construction* (lists concatenate in the
  same order), and the classical cascade is a sequence of these ops —
  mathematics on top, not a machine obligation.
* **One shift machine per direction and side**, taking the level in unary
  on the scratch tape: the Hennie-Stearns simulator is a single machine,
  so the level cannot be baked into finite control. The rows below are
  existential seam-to-seam contracts over arbitrary configurations
  (`Cfg.ofWords` does not reach negative cells), with exact geometric
  budgets and visited-interval clauses.
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

## Status: statement skeleton (§13 statement phase, tranche A-S2)

Definitions are real; every contract is `sorry`d with a proof sketch.

## Main definitions and results

* `Turing.zoneCellBits`/`Turing.zoneCellOf` — the paired-cell codec.
* `Turing.ZoneContents`, `Turing.zoneTape` — the carrier and its physical
  realization.
* `Turing.zoneSide` — the represented virtual half-word (inner zones
  first).
* `Turing.zoneShiftIn`/`Turing.zoneShiftOut` — the pure pairwise
  rebalancing ops, with `Turing.zoneSide_shiftIn`/`_shiftOut` the
  honesty lemmas: rebalancing never changes the represented word.
* `Turing.zoneMoveRight`/`Turing.zoneMoveLeft`,
  `Turing.zoneHomeWrite` — the pure head-step and write ops with their
  readout lemmas.
* `Turing.FinTM.exists_zoneShiftInTM`/`exists_zoneShiftOutTM` — the
  machine rows: one two-tape machine per direction and side, level in
  unary on the scratch tape, exact `O(2^i)` budgets, visited sets inside
  the level-`i` physical extent.
* `Turing.zoneTape_blank_outside`, `Turing.spaceUsedByTape_le_card_Icc` —
  the cardinality exports the Z4 space annotation consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.7, the Hennie-Stearns
  simulation; Exercise 1.6.)
* In-repo precedents: `SweepCell`/`SweepAlphabet`
  (`Robustness/SingleTape.lean`, the product-cell multiplexing this
  pairing replaces at binary alphabet); `ObliviousSetup.lean`'s guide-zone
  layout (the oblivious schedule's zones, harvested for the layout
  arithmetic's shape).
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

**Proof sketch.** `zoneBase i ≤ s < zoneBase (i + 1)` unfolds to
`2^i ≤ s / 2 + 1 < 2^(i+1)` by the division arithmetic of the even bases,
and `Nat.log2` is characterized by exactly that sandwich. -/
theorem zoneIndex_eq_iff (s i : ℕ) :
    zoneIndex s = i ↔ zoneBase i ≤ s ∧ s < zoneBase (i + 1) := by
  sorry

/-! ### The carrier -/

/-- The zone contents of one tape: the home cell and, per level and side,
the stored word (inner end first), bounded by capacity. Fullness
discipline is deliberately **not** carried here (design §13a): the
Hennie-Stearns `{empty, half, full}` invariant is the consumer's. -/
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
returns `none` by its guard. -/
theorem zoneTape_blank_outside {ℓ : ℕ} (z : ZoneContents ℓ) (c : ℤ)
    (hc : (2 * zoneBase ℓ + 1 : ℤ) < |c|) : zoneTape z c = none := by
  sorry

/-! ### The represented word -/

/-- The virtual half-word one side represents: the zone words
concatenated inner-first. -/
def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i

/-! ### Pure rebalancing (pairwise, order-preserving) -/

/-- The level-`i` inward shift on one side's family (`1 ≤ i`): if zone
`i - 1` is empty, move the inner `2^(i-1)` stored cells (or all of them,
if fewer) of zone `i` into it. Total, with the identity outside its
guard. -/
def zoneShiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if w ⟨i - 1, by omega⟩ = [] then
      if j.val = i - 1 then (w ⟨i, hi.2⟩).take (2 ^ (i - 1))
      else if j.val = i then (w ⟨i, hi.2⟩).drop (2 ^ (i - 1))
      else w j
    else w j
  else w j

/-- The level-`i` outward shift on one side's family (`1 ≤ i`): if zone
`i - 1` is full, move its outer half onto the front of zone `i`. Total,
with the identity outside its guard; the capacity obligation on zone `i`
is part of the machine row's precondition, not of the pure op. -/
def zoneShiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if (w ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) then
      if j.val = i - 1 then (w ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
      else if j.val = i then
        (w ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++ w ⟨i, hi.2⟩
      else w j
    else w j
  else w j

/-- Inward rebalancing never changes the represented half-word.

**Proof sketch.** Only zones `i - 1` and `i` change; in the inner-first
concatenation they are adjacent, zone `i - 1` was empty, and
`take ++ drop` restores zone `i`'s word, so the concatenation is
unchanged. -/
theorem zoneSide_shiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftInW i w) = zoneSide w := by
  sorry

/-- Outward rebalancing never changes the represented half-word.

**Proof sketch.** Adjacent zones again: `take` keeps zone `i - 1`'s inner
half in place and the dropped outer half is prepended to zone `i`, so the
two-zone segment of the concatenation is literally re-associated. -/
theorem zoneSide_shiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftOutW i w) = zoneSide w := by
  sorry

/-- Lift a one-side rebalancing to contents: `side = false` acts on the
left family, `side = true` on the right. The capacity proofs transport
because `take`/`drop` never exceed the moved words' lengths and the
outward target's room is the machine row's precondition.

**Proof sketch** (for the embedded capacity fields): `take (2^(i-1))` has
length at most `2^(i-1) ≤ zoneCapacity (i-1)`; the outward target's
length is `2^(i-1) + (w i).length`, bounded by the row's precondition
`(w i).length + 2^(i-1) ≤ zoneCapacity i` — carried here as a hypothesis. -/
def zoneShift {ℓ : ℕ} (inward : Bool) (side : Bool) (i : ℕ)
    (z : ZoneContents ℓ)
    (hroom : ∀ hi : i < ℓ,
      ((if side then z.right else z.left) ⟨i, hi⟩).length + 2 ^ (i - 1) ≤
        zoneCapacity i) : ZoneContents ℓ where
  home := z.home
  left := if side then z.left
    else (if inward then zoneShiftInW i z.left else zoneShiftOutW i z.left)
  right := if side then
    (if inward then zoneShiftInW i z.right else zoneShiftOutW i z.right)
    else z.right
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
rebalancing obligation, carried here as a hypothesis. -/
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

/-! ### The machine rows -/

namespace FinTM

/-- **Z2, the inward shift row.** One two-tape machine per side: tape `0`
carries a zoned tape, tape `1` the level in unary (`replicate i true` as a
buffered word). From any configuration holding `zoneTape z` at origin and
the level word at origin, the machine halts at the rebalanced tape with
both heads home, the level word intact, within `c * (2^i + i + 1)` steps,
first return at the halt, and the visited sets inside the level-`i + 1`
physical extent on tape `0` and a `c * (2^i + i + 1)`-cell interval on
tape `1`. No fullness hypothesis beyond the pure op's guard: the row
realizes `zoneShift` exactly where the guard fires and must not be invoked
elsewhere (the consumer's invariant supplies the guard).

**Proof sketch** (fill plan): scan the level word to locate zone `i`'s
physical window (the bases are computable by doubling a unary counter —
`2^(i-1)` cells staged on tape `1` past the level word); move the inner
`2^(i-1)` stored pairs of zone `i` inward with the R3 transfer discipline
staged through tape `1`; R2 seams between the scan, stage, and write-back
phases; the budget is geometric because every phase is one pass over the
level-`i` window. -/
theorem exists_zoneShiftInTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        (hroom : ∀ hi' : i < ℓ,
          ((if side then z.right else z.left) ⟨i, hi'⟩).length + 2 ^ (i - 1) ≤
            zoneCapacity i)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShift true side i z hroom)
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
outward `zoneShift`, with the same budget shape, interval clause, and
scratch bound.

**Proof sketch** (fill plan): as the inward row with the transfer
direction reversed; the full zone `i - 1`'s outer half is staged through
tape `1` and written to zone `i`'s front after its stored word is slid
outward by `2^(i-1)` slots — one extra pass over the level-`i` window,
inside the same geometric budget. -/
theorem exists_zoneShiftOutTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        (hroom : ∀ hi' : i < ℓ,
          ((if side then z.right else z.left) ⟨i, hi'⟩).length + 2 ^ (i - 1) ≤
            zoneCapacity i)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShift false side i z hroom)
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
