/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedSeed
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Partial inverse coordinates for selected row nonces

The coordinate maps depend only on the fixed circuit, assignment enumeration, and row
permutation. A padded occurrence places its challenge nonce in the selected row's first
or second encryption layer. The reverse map reads its occurrence rank. Unused padded
slots and unchanged nonce coordinates are represented by `none`.

## Main definitions

* `NonceCoordinates.Index`: a gate, actual assignment, and nonce-half coordinate.
* `NonceCoordinates.pick`, `place`: partial inverse coordinate maps.

## Main results

* The coordinate maps are exact partial inverses.
* Reading a filled nonce coordinate agrees with the generic coordinate replacement map.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (independent coins at every use of one inactive key).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates

open BoolCircuit

/-- A nonce coordinate consists of a gate, its actual argument assignment, and a half bit:
`false` denotes the first nonce, and `true` the second. -/
abbrev Index {m : ℕ} (C : DAGCircuit m) :=
  Σ i : Fin C.gates.length, (Fin C.gates[i.val].args.length → Bool) × Bool

/-- `Index C` is the dependent product of gate indices and assignment/half pairs. -/
theorem Index_eq {m : ℕ} (C : DAGCircuit m) :
    Index C = (Σ i : Fin C.gates.length, (Fin C.gates[i.val].args.length → Bool) × Bool) := rfl

/-- Pick the challenge index for a selected nonce coordinate. The selected argument's half
is first for position zero and second otherwise; out-of-capacity occurrences return `none`. -/
noncomputable def pick {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (x : Index C) : Option (Fin (q + 1)) :=
  (GateOccurrences.selectedPosition C.gates[x.1.val] x.2.1 u).bind fun p =>
    if x.2.2 = decide (p.val ≠ 0) then
      let j := SelectedSeed.slotIndex C rows perm u x.1 x.2.1 p
      if h : j < q + 1 then some ⟨j, h⟩ else none
    else none

/-- `pick` selects the occurrence rank exactly for the selected nonce half and within capacity. -/
theorem pick_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (x : Index C) :
    pick C rows perm u q x =
      (GateOccurrences.selectedPosition C.gates[x.1.val] x.2.1 u).bind (fun p =>
        if x.2.2 = decide (p.val ≠ 0) then
          let j := SelectedSeed.slotIndex C rows perm u x.1 x.2.1 p
          if h : j < q + 1 then some ⟨j, h⟩ else none
        else none) := rfl

/-- Place a padded challenge slot at its gate, actual assignment, and selected nonce half.
Padding without an occurrence has no destination coordinate. -/
def place {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (j : Fin (q + 1)) : Option (Index C) :=
  (GateOccurrences.padded q (GateOccurrences.occurrences C rows perm u) j).map fun s =>
    ⟨s.1, (perm s.1 ((rows s.1).getD s.2.1 (fun _ => false)), decide (s.2.2 ≠ 0))⟩

/-- `place` maps the padded occurrence triple to its actual-assignment nonce coordinate. -/
theorem place_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (j : Fin (q + 1)) :
    place C rows perm u q j =
      (GateOccurrences.padded q (GateOccurrences.occurrences C rows perm u) j).map (fun s =>
        ⟨s.1, (perm s.1 ((rows s.1).getD s.2.1 (fun _ => false)), decide (s.2.2 ≠ 0))⟩) := rfl

/-- A padded occurrence `(i,r,p)` is placed at actual assignment `perm i (rows[i][r])`
and nonce half `decide (p≠0)`. -/
theorem place_of_padded {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (j : Fin (q + 1)) (i : Fin C.gates.length) (r p : ℕ)
    (h : GateOccurrences.padded q (GateOccurrences.occurrences C rows perm u) j =
      some (i, r, p)) :
    place C rows perm u q j =
      some ⟨i, (perm i ((rows i).getD r (fun _ => false)), decide (p ≠ 0))⟩ := by
  rw [place_eq, h, Option.map_some]

/-- Every picked challenge slot is placed back at the original nonce coordinate.
Completeness of the assignment rows ensures the occurrence rank has the prescribed row.

**Proof sketch.** A successful pick identifies the selected argument, the matching nonce
half, and an in-capacity occurrence rank. Reading that padded rank returns the exact gate,
row and position. The row-index reader recovers the original actual assignment, and the
picked half is precisely the half recorded by placement. -/
theorem place_of_pick {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i) (x : Index C) (j : Fin (q + 1))
    (h : pick C rows perm u q x = some j) : place C rows perm u q j = some x := by
  rcases x with ⟨i, a, half⟩
  rw [pick_eq] at h
  obtain ⟨p, hp, hrest⟩ := Option.bind_eq_some_iff.mp h
  change (if half = decide (p.val ≠ 0) then
    (if hi : SelectedSeed.slotIndex C rows perm u i a p < q + 1 then
      some ⟨SelectedSeed.slotIndex C rows perm u i a p, hi⟩ else none) else none) = some j
    at hrest
  split_ifs at hrest with hhalf hidx
  · have heq : (⟨SelectedSeed.slotIndex C rows perm u i a p, hidx⟩ : Fin (q + 1)) = j :=
      Option.some.inj hrest
    cases heq
    obtain ⟨hvertex, hbit⟩ :=
      (GateOccurrences.selectedPosition_eq_some_iff _ _ _ (hargs i) p).mp hp
    rw [place_eq, SelectedSeed.slotIndex_padded C rows perm u q i a p (hargs i)
      (hcomplete i) hvertex hbit hidx, Option.map_some,
      SelectedSeed.rowIndex_actual C rows perm i a (hcomplete i), ← hhalf]

/-- Every placed challenge slot is picked back at the same index. Duplicate-free row
and occurrence enumerations make both indices exact.

**Proof sketch.** A successful placement supplies an occurrence triple and its valid row
and argument indices. Its vertex and bit tests force the selected-position search to choose
that argument. The occurrence lookup inverts its rank, so the pick uses the original padded
slot and fits the available capacity. -/
theorem pick_of_place {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hrows : ∀ i, (rows i).Nodup) (x : Index C) (j : Fin (q + 1))
    (h : place C rows perm u q j = some x) : pick C rows perm u q x = some j := by
  rw [place_eq] at h
  obtain ⟨t, ht, hx⟩ := Option.map_eq_some_iff.mp h
  rcases t with ⟨i, row, p⟩
  cases hx
  rw [GateOccurrences.padded_eq] at ht
  have hmem := List.mem_iff_getElem?.mpr ⟨j.val, ht⟩
  obtain ⟨hr, hp, hvertex, hbit⟩ :=
    (GateOccurrences.mem_occurrences_iff C rows perm u i row p (hargs i)).mp hmem
  have hsel := (GateOccurrences.selectedPosition_eq_some_iff _ _ _ (hargs i) ⟨p, hp⟩).mpr
    ⟨hvertex, hbit⟩
  have hidx := SelectedSeed.slotIndex_of_lookup C rows perm u i row j.val ⟨p, hp⟩
    hr (hrows i) ht
  rw [pick_eq, hsel, Option.bind_some, if_pos rfl]
  change (if h : SelectedSeed.slotIndex C rows perm u i
    (perm i ((rows i).getD row (fun _ => false))) ⟨p, hp⟩ < q + 1 then
      some ⟨_, h⟩ else none) = some j
  have hbound : SelectedSeed.slotIndex C rows perm u i
      (perm i ((rows i).getD row (fun _ => false))) ⟨p, hp⟩ < q + 1 := by
    rw [hidx]
    exact j.isLt
  rw [dif_pos hbound]
  exact congrArg some (Fin.ext hidx)

/-- Pick and place are exact partial inverses, including unmatched padding and unchanged
nonce coordinates. These are the hypotheses of the generic coordinate-swap law. -/
theorem pick_iff_place {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i) (hrows : ∀ i, (rows i).Nodup)
    (x : Index C) (j : Fin (q + 1)) :
    pick C rows perm u q x = some j ↔ place C rows perm u q j = some x :=
  ⟨place_of_pick C rows perm u q hargs hcomplete x j,
    pick_of_place C rows perm u q hargs hrows x j⟩

/-- Reading either half of the filled nonce table is exactly the partial coordinate
replacement prescribed by `pick`, with the old nonce retained for an unmatched coordinate.

**Proof sketch.** With no selected argument both halves are retained. With a selected
argument, distinguish its first/second encryption layer and whether its occurrence fits the
capacity. The matching half reads its challenge slot; the other half remains fixed. -/
theorem nonce_read {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u q : ℕ) (r : Fin (q + 1) → ρ)
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) (half : Bool) :
    (if half then (SelectedSeed.nonce C rows s u q r i a).2
      else (SelectedSeed.nonce C rows s u q r i a).1) =
        (pick C rows s.2.2 u q ⟨i, (a, half)⟩).elim
          (if half then (s.2.1 i a).2 else (s.2.1 i a).1) r := by
  rw [pick_eq, SelectedSeed.nonce_eq]
  cases hs : GateOccurrences.selectedPosition C.gates[i.val] a u with
  | none => simp only [Option.elim_none, Option.bind_none]
  | some p =>
    simp only [Option.elim_some, Option.bind_some]
    cases half <;> by_cases hp : p.val = 0 <;>
      by_cases hj : SelectedSeed.slotIndex C rows s.2.2 u i a p < q + 1 <;>
      simp only [hp, hj, ne_eq, not_true_eq_false, not_false_eq_true, decide_true,
        decide_false, ite_true, ite_false, dite_true, dite_false, Option.elim_some,
        Option.elim_none, Bool.false_eq_true, Bool.true_eq_false]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.NonceCoordinates
