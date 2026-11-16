/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.NonceCoordinates

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coordinates of a garbling seed and its selected challenge

Existing product, sum, currying and Boolean-function equivalences expose a garbling seed
as its unchanged assignment permutation and one table of key/nonce values. The challenge
is one selected key and a padded vector of row nonces. No equality on coordinate values
is used; repeated actual values are allowed.

## Main definitions

* `SeedCoordinates.Permutations`, `Index`, `ChallengeIndex`: the coordinate types.
* `SeedCoordinates.seedEquiv`, `challengeEquiv`: the exact coordinate equivalences.

## Main results

* Exact forward and inverse coordinate readers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (fresh selected key and encryption coins).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates

open BoolCircuit

/-- The unchanged seed component is the family of assignment permutations at every gate.
`Permutations C = ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length →
Bool))`. -/
abbrev Permutations {m : ℕ} (C : DAGCircuit m) :=
  (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool)

/-- `Permutations C` is the dependent family of per-gate assignment permutations.
`Permutations C = ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length →
Bool))`. -/
theorem Permutations_eq {m : ℕ} (C : DAGCircuit m) :
    Permutations C =
      ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool)) := rfl

/-- A full seed coordinate is either a vertex/bit key label or a row nonce coordinate.
`Index C = ((Fin C.size × Bool) ⊕ NonceCoordinates.Index C)`. -/
abbrev Index {m : ℕ} (C : DAGCircuit m) :=
  (Fin C.size × Bool) ⊕ NonceCoordinates.Index C

/-- `Index C` is the sum of key labels and row-nonce coordinates.
`Index C = ((Fin C.size × Bool) ⊕ NonceCoordinates.Index C)`. -/
theorem Index_eq {m : ℕ} (C : DAGCircuit m) :
    Index C = ((Fin C.size × Bool) ⊕ NonceCoordinates.Index C) := rfl

/-- Challenge coordinates consist of one selected key slot and `q+1` padded nonce slots.
`ChallengeIndex q = (Unit ⊕ Fin (q + 1))`. -/
abbrev ChallengeIndex (q : ℕ) := Unit ⊕ Fin (q + 1)

/-- `ChallengeIndex q = Unit ⊕ Fin (q+1)`. -/
theorem ChallengeIndex_eq (q : ℕ) : ChallengeIndex q = (Unit ⊕ Fin (q + 1)) := rfl

/-- `Data C V` is the pair of the full two-key table and the full two-half nonce table.
`Data C V = ((Fin C.size → Bool → V) × ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length →
Bool) → V × V))`. -/
abbrev Data {m : ℕ} (C : DAGCircuit m) (V : Type) :=
  (Fin C.size → Bool → V) ×
    ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → V × V)

/-- `Data C V` is the product of its key and nonce function tables.
`Data C V = ((Fin C.size → Bool → V) × ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length →
Bool) → V × V))`. -/
theorem Data_eq {m : ℕ} (C : DAGCircuit m) (V : Type) :
    Data C V = ((Fin C.size → Bool → V) ×
      ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → V × V)) := rfl

/-- Existing currying, Boolean-function and sum-function equivalences identify the key/nonce
value tables with one coordinate function. No permutation distribution is involved.
`dataEquiv C V d = Sum.elim (fun label => d.1 label.1 label.2) (fun x => if x.2.2 then (d.2 x.1
x.2.1).2 else (d.2 x.1 x.2.1).1)`. -/
def dataEquiv {m : ℕ} (C : DAGCircuit m) (V : Type) : Data C V ≃ (Index C → V) :=
  let key := (Equiv.curry (Fin C.size) Bool V).symm
  let nonce : ((i : Fin C.gates.length) →
      (Fin C.gates[i.val].args.length → Bool) → V × V) ≃ (NonceCoordinates.Index C → V) :=
    ((Equiv.piCongrRight fun i => Equiv.piCongrRight fun _ :
        (Fin C.gates[i.val].args.length → Bool) => (Equiv.boolArrowEquivProd V).symm).trans
      (Equiv.piCongrRight fun i =>
        (Equiv.curry (Fin C.gates[i.val].args.length → Bool) Bool V).symm)).trans
      (Equiv.piCurry (fun (i : Fin C.gates.length)
        (_ : (Fin C.gates[i.val].args.length → Bool) × Bool) => V)).symm
  (key.prodCongr nonce).trans (Equiv.sumArrowEquivProdArrow _ _ V).symm

/-- The data-coordinate map reads the key table on key labels and the chosen nonce half.
`dataEquiv C V d = Sum.elim (fun label => d.1 label.1 label.2) (fun x => if x.2.2 then (d.2 x.1
x.2.1).2 else (d.2 x.1 x.2.1).1)`. -/
theorem dataEquiv_eq {m : ℕ} (C : DAGCircuit m) (V : Type) (d : Data C V) :
    dataEquiv C V d = Sum.elim (fun label => d.1 label.1 label.2)
      (fun x => if x.2.2 then (d.2 x.1 x.2.1).2 else (d.2 x.1 x.2.1).1) := rfl

/-- The inverse data-coordinate map restores both key choices and both nonce halves.
`(dataEquiv C V).symm f = ((fun v b => f (Sum.inl (v, b))), fun i a => (f (Sum.inr ⟨i, (a, false)⟩),
f (Sum.inr ⟨i, (a, true)⟩)))`. -/
theorem dataEquiv_symm {m : ℕ} (C : DAGCircuit m) (V : Type) (f : Index C → V) :
    (dataEquiv C V).symm f = ((fun v b => f (Sum.inl (v, b))),
      fun i a => (f (Sum.inr ⟨i, (a, false)⟩), f (Sum.inr ⟨i, (a, true)⟩))) := rfl

/-- The value-table equivalence retains any unchanged parameter `P`, such as actual XOR
shifts and unused tape coordinates. No uniformity of a derived permutation is assumed.
`paramEquiv C V P (p, d) = (p, dataEquiv C V d)`. -/
def paramEquiv {m : ℕ} (C : DAGCircuit m) (V P : Type) :
    P × Data C V ≃ P × (Index C → V) := (Equiv.refl P).prodCongr (dataEquiv C V)

/-- `paramEquiv` retains `p` and converts only the key/nonce data table.
`paramEquiv C V P (p, d) = (p, dataEquiv C V d)`. -/
theorem paramEquiv_eq {m : ℕ} (C : DAGCircuit m) (V P : Type) (p : P) (d : Data C V) :
    paramEquiv C V P (p, d) = (p, dataEquiv C V d) := rfl

/-- The inverse parameterized map retains `p` and restores only its data table.
`(paramEquiv C V P).symm (p, f) = (p, (dataEquiv C V).symm f)`. -/
theorem paramEquiv_symm {m : ℕ} (C : DAGCircuit m) (V P : Type) (p : P) (f : Index C → V) :
    (paramEquiv C V P).symm (p, f) = (p, (dataEquiv C V).symm f) := rfl

/-- A full abstract garbling seed is equivalent to its permutation family and key/nonce
coordinate table. This auxiliary equivalence makes no claim that concrete XOR-shift tapes
induce uniform samples over all permutations.
`seedEquiv C V s = (s.2.2, Sum.elim (fun label => s.1 label.1 label.2) (fun x => if x.2.2 then
(s.2.1 x.1 x.2.1).2 else (s.2.1 x.1 x.2.1).1))`. -/
def seedEquiv {m : ℕ} (C : DAGCircuit m) (V : Type) :
    GarbleSeed C V (V × V) ≃ Permutations C × (Index C → V) :=
  ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)).trans
    ((Equiv.refl _).prodCongr (dataEquiv C V))

/-- `seedEquiv` retains the permutations and reads key labels or first/second row nonces.
`seedEquiv C V s = (s.2.2, Sum.elim (fun label => s.1 label.1 label.2) (fun x => if x.2.2 then
(s.2.1 x.1 x.2.1).2 else (s.2.1 x.1 x.2.1).1))`. -/
theorem seedEquiv_eq {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V)) :
    seedEquiv C V s = (s.2.2, Sum.elim (fun label => s.1 label.1 label.2)
      (fun x => if x.2.2 then (s.2.1 x.1 x.2.1).2 else (s.2.1 x.1 x.2.1).1)) := rfl

/-- The coordinate permutation family is exactly the original seed's permutation family.
`(seedEquiv C V s).1 = s.2.2`. -/
theorem seedEquiv_perm {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V)) :
    (seedEquiv C V s).1 = s.2.2 := rfl

/-- A key coordinate reads its original vertex/bit key.
`(seedEquiv C V s).2 (Sum.inl (v, b)) = s.1 v b`. -/
theorem seedEquiv_key {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V))
    (v : Fin C.size) (b : Bool) : (seedEquiv C V s).2 (Sum.inl (v, b)) = s.1 v b := rfl

/-- A nonce coordinate reads the first half for `false` and the second half for `true`.
`(seedEquiv C V s).2 (Sum.inr ⟨i, (a, half)⟩) = if half then (s.2.1 i a).2 else (s.2.1 i a).1`. -/
theorem seedEquiv_nonce {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) (half : Bool) :
    (seedEquiv C V s).2 (Sum.inr ⟨i, (a, half)⟩) =
      if half then (s.2.1 i a).2 else (s.2.1 i a).1 := rfl

/-- The inverse coordinate map restores the two key choices, both nonce halves, and the
unchanged permutation family.
`(seedEquiv C V).symm (p, f) = ((fun v b => f (Sum.inl (v, b))), ((fun i a => (f (Sum.inr ⟨i, (a,
false)⟩), f (Sum.inr ⟨i, (a, true)⟩))), p))`. -/
theorem seedEquiv_symm {m : ℕ} (C : DAGCircuit m) (V : Type)
    (p : Permutations C) (f : Index C → V) :
    (seedEquiv C V).symm (p, f) =
      ((fun v b => f (Sum.inl (v, b))),
        ((fun i a => (f (Sum.inr ⟨i, (a, false)⟩), f (Sum.inr ⟨i, (a, true)⟩))), p)) := rfl

/-- A selected key and its padded nonce vector are one table on the sum of challenge slots.
`challengeEquiv q V (k, r) = Sum.elim (fun _ => k) r`. -/
def challengeEquiv (q : ℕ) (V : Type) :
    V × (Fin (q + 1) → V) ≃ (ChallengeIndex q → V) :=
  (((Equiv.funUnique Unit V).symm).prodCongr (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow Unit (Fin (q + 1)) V).symm

/-- `challengeEquiv q V (k,r)` is `Sum.elim (fun _ => k) r`. -/
theorem challengeEquiv_eq (q : ℕ) (V : Type) (k : V) (r : Fin (q + 1) → V) :
    challengeEquiv q V (k, r) = Sum.elim (fun _ => k) r := rfl

/-- The inverse challenge-coordinate map reads the key slot and all padded nonce slots.
`(challengeEquiv q V).symm f = (f (Sum.inl ()), fun j => f (Sum.inr j))`. -/
theorem challengeEquiv_symm (q : ℕ) (V : Type) (f : ChallengeIndex q → V) :
    (challengeEquiv q V).symm f = (f (Sum.inl ()), fun j => f (Sum.inr j)) := rfl

/-- Pick the single key slot at `(u,true)`, or the selected nonce slot given by the nonce
coordinate map. The map depends on the row permutation and never on coordinate values.
`pick C rows perm u q x = Sum.elim (fun label => if label = (u, true) then some (Sum.inl () :
ChallengeIndex q) else none) (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map
Sum.inr) x`. -/
noncomputable def pick {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (x : Index C) :
    Option (ChallengeIndex q) :=
  Sum.elim (fun label => if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none)
    (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map Sum.inr) x

/-- `pick` selects the key challenge at `(u,true)` and delegates nonce coordinates to the
nonce-slot map.
`pick C rows perm u q x = Sum.elim (fun label => if label = (u, true) then some (Sum.inl () :
ChallengeIndex q) else none) (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map
Sum.inr) x`. -/
theorem pick_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (x : Index C) :
    pick C rows perm u q x =
      Sum.elim
        (fun label => if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none)
        (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map Sum.inr) x := rfl

/-- Place the selected key at `(u,true)` and each used nonce slot at its selected row half.
`place C rows perm u q j = Sum.elim (fun _ => some (Sum.inl (u, true) : Index C)) (fun nonce =>
(NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j`. -/
def place {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (j : ChallengeIndex q) : Option (Index C) :=
  Sum.elim (fun _ => some (Sum.inl (u, true) : Index C))
    (fun nonce => (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j

/-- `place` retains the distinction between the key challenge and padded nonce challenges.
`place C rows perm u q j = Sum.elim (fun _ => some (Sum.inl (u, true) : Index C)) (fun nonce =>
(NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j`. -/
theorem place_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (j : ChallengeIndex q) :
    place C rows perm u q j =
      Sum.elim (fun _ => some (Sum.inl (u, true) : Index C))
        (fun nonce => (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j := rfl

/-- Full key/nonce picks and placements are exact partial inverses. The key and nonce
summands are disjoint, and nonce padding remains unmatched.
`pick C rows perm u q x = some j ↔ place C rows perm u q j = some x`.

**Proof sketch.** In the key summand there is one matching vertex/bit coordinate and one
challenge slot. Mixed summands cannot match. Within the nonce summand, injectivity of the
sum constructor reduces both directions to the existing nonce-coordinate inverse contract. -/
theorem pick_iff_place {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ)
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i) (hrows : ∀ i, (rows i).Nodup)
    (x : Index C) (j : ChallengeIndex q) :
    pick C rows perm u q x = some j ↔ place C rows perm u q j = some x := by
  cases x with
  | inl label =>
    cases j with
    | inl keySlot =>
      -- Step 1: key summand. The only matching pair is the coordinate `(u, true)` and the single
      -- key slot.
      cases keySlot
      rw [pick_eq, place_eq]
      change (if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none) =
        some (Sum.inl () : ChallengeIndex q) ↔
        some (Sum.inl (u, true) : Index C) = some (Sum.inl label : Index C)
      by_cases h : label = (u, true)
      · subst label
        constructor
        · intro _; rfl
        · intro _; exact if_pos rfl
      · constructor
        · intro h'
          rw [if_neg h] at h'
          cases h'
        · intro h'
          exact (h (Sum.inl.inj (Option.some.inj h')).symm).elim
    | inr nonce =>
      -- Step 2: mixed summands cannot match. A key label never picks a nonce slot, and `place`
      -- sends nonce slots only to nonce coordinates.
      rw [pick_eq, place_eq]
      change (if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none) =
        some (Sum.inr nonce : ChallengeIndex q) ↔
        (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr =
          some (Sum.inl label : Index C)
      constructor
      · intro h
        by_cases hc : label = (u, true)
        · rw [if_pos hc] at h; cases h
        · rw [if_neg hc] at h; cases h
      · intro h
        obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp h
        cases heq
  | inr coordinate =>
    cases j with
    | inl keySlot =>
      -- Step 3: mixed summands cannot match. A nonce coordinate never picks the key slot, and
      -- `place` sends the key slot to a key label.
      cases keySlot
      rw [pick_eq, place_eq]
      change (NonceCoordinates.pick C rows perm u.val q coordinate).map Sum.inr =
        some (Sum.inl () : ChallengeIndex q) ↔
          some (Sum.inl (u, true) : Index C) = some (Sum.inr coordinate : Index C)
      constructor
      · intro h
        obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp h
        cases heq
      · intro h; cases h
    | inr nonce =>
      -- Step 4: nonce summand. Injectivity of `Sum.inr` reduces both directions to the
      -- nonce-coordinate inverse contract `NonceCoordinates.pick_iff_place`.
      rw [pick_eq, place_eq]
      change (NonceCoordinates.pick C rows perm u.val q coordinate).map Sum.inr =
        some (Sum.inr nonce : ChallengeIndex q) ↔
          (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr =
            some (Sum.inr coordinate : Index C)
      constructor
      · intro h
        obtain ⟨j, hp, heq⟩ := Option.map_eq_some_iff.mp h
        have hj : j = nonce := Sum.inr.inj heq
        subst j
        exact Option.map_eq_some_iff.mpr ⟨coordinate,
          (NonceCoordinates.pick_iff_place C rows perm u.val q hargs hcomplete hrows _ _).mp hp,
          rfl⟩
      · intro h
        obtain ⟨x, hp, heq⟩ := Option.map_eq_some_iff.mp h
        have hx : x = coordinate := Sum.inr.inj heq
        subst x
        exact Option.map_eq_some_iff.mpr ⟨nonce,
          (NonceCoordinates.pick_iff_place C rows perm u.val q hargs hcomplete hrows _ _).mpr hp,
          rfl⟩

/-- The seed coordinate map is its unchanged permutation paired with the data-coordinate map.
`seedEquiv C V s = (s.2.2, dataEquiv C V (s.1, s.2.1))`. -/
theorem seedEquiv_eq_data {m : ℕ} (C : DAGCircuit m) (V : Type)
    (s : GarbleSeed C V (V × V)) :
    seedEquiv C V s = (s.2.2, dataEquiv C V (s.1, s.2.1)) := rfl

/-- Filling the selected key and nonce vector is exactly the value-coordinate replacement
prescribed by `pick`. This pointwise identity holds at every value, including collisions,
and for arbitrary unused padding; no distribution or permutation-uniformity assumption occurs.
`dataEquiv C V ((SelectedSeed.fill C rows s u q k r).1, (SelectedSeed.fill C rows s u q k r).2.1) =
fun x => (pick C rows s.2.2 u q x).elim (dataEquiv C V (s.1, s.2.1) x) (challengeEquiv q V (k, r))`.

**Proof sketch.** At key coordinates the filled-key reader changes just `(u,true)`, matching
the single key slot. At nonce coordinates the nonce-coordinate read contract gives precisely
the picked challenge value or the retained old value. The challenge sum map reads the key
in its left summand and the nonce vector in its right summand. -/
theorem dataEquiv_fill {m : ℕ} (C : DAGCircuit m) (V : Type)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C V (V × V)) (u : Fin C.size) (q : ℕ) (k : V)
    (r : Fin (q + 1) → V) :
    dataEquiv C V ((SelectedSeed.fill C rows s u q k r).1,
      (SelectedSeed.fill C rows s u q k r).2.1) =
        fun x => (pick C rows s.2.2 u q x).elim (dataEquiv C V (s.1, s.2.1) x)
          (challengeEquiv q V (k, r)) := by
  funext x
  cases x with
  | inl label =>
    rcases label with ⟨v, b⟩
    simp only [dataEquiv_eq, pick_eq, Sum.elim_inl, SelectedSeed.fill_key,
      challengeEquiv_eq, Prod.mk.injEq]
    by_cases h : v = u ∧ b = true
    · simp only [h, and_self, ite_true, Option.elim_some, Sum.elim_inl]
    · simp only [h, ite_false, Option.elim_none]
  | inr coordinate =>
    rcases coordinate with ⟨i, a, half⟩
    simp only [dataEquiv_eq, Sum.elim_inr, SelectedSeed.fill_nonce]
    rw [NonceCoordinates.nonce_read]
    simp only [pick_eq, challengeEquiv_eq, Sum.elim_inr]
    cases h : NonceCoordinates.pick C rows s.2.2 u.val q ⟨i, (a, half)⟩ with
    | none => simp only [Option.map_none, Option.elim_none]
    | some j => simp only [Option.map_some, Option.elim_some, Sum.elim_inr]

/-- The complete filled abstract seed retains its permutation and performs exactly the
partial replacement of its key/nonce value coordinates.
`seedEquiv C V (SelectedSeed.fill C rows s u q k r) = (s.2.2, fun x => (pick C rows s.2.2 u q
x).elim (dataEquiv C V (s.1, s.2.1) x) (challengeEquiv q V (k, r)))`. -/
theorem seedEquiv_fill {m : ℕ} (C : DAGCircuit m) (V : Type)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C V (V × V)) (u : Fin C.size) (q : ℕ) (k : V)
    (r : Fin (q + 1) → V) :
    seedEquiv C V (SelectedSeed.fill C rows s u q k r) =
      (s.2.2, fun x => (pick C rows s.2.2 u q x).elim (dataEquiv C V (s.1, s.2.1) x)
        (challengeEquiv q V (k, r))) :=
  (seedEquiv_eq_data C V _).trans (Prod.ext
    (funext fun i => SelectedSeed.fill_perm C rows s u q k r i)
    (dataEquiv_fill C V rows s u q k r))

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates
