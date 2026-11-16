/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateOccurrences

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Filling one selected key and all its encryption nonces

The assignment rows and permutation are fixed before a selected key and an independent
nonce vector are supplied. Occurrence ranks address one challenge nonce for every use
of the selected inactive label. All other key and nonce coordinates stay fixed.

## Main definitions

* `SelectedSeed.rowIndex`: the enumerated row for a prescribed actual assignment.
* `SelectedSeed.slotIndex`: its index in the all-occurrence list.

## Main results

* Exact row-index and challenge-slot readers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (fixing all randomness except one inactive key and its uses).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed

open BoolCircuit

/-- The enumerated row of actual assignment `a` is the index of `perm.symm a` in `rows`. -/
noncomputable def rowIndex {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) : ℕ :=
  (rows i).idxOf ((perm i).symm a)

/-- `rowIndex C rows perm i a = (rows i).idxOf ((perm i).symm a)`. -/
theorem rowIndex_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
    rowIndex C rows perm i a = (rows i).idxOf ((perm i).symm a) := rfl

/-- A complete assignment enumeration contains the row index of every actual assignment. -/
theorem rowIndex_lt {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (hcomplete : ∀ a, a ∈ rows i) : rowIndex C rows perm i a < (rows i).length :=
  List.idxOf_lt_length_iff.mpr (hcomplete ((perm i).symm a))

/-- Reading the enumerated row at `rowIndex` and applying its permutation recovers the
prescribed actual assignment exactly. -/
theorem rowIndex_actual {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (hcomplete : ∀ a, a ∈ rows i) :
    perm i ((rows i).getD (rowIndex C rows perm i a) (fun _ => false)) = a := by
  rw [rowIndex_eq,
    List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr (hcomplete ((perm i).symm a))),
    List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hcomplete ((perm i).symm a)))]
  exact Equiv.apply_symm_apply (perm i) a

/-- The challenge slot for actual assignment `a` and argument position `p` is the index
of `(i,rowIndex a,p)` in the complete occurrence list. -/
noncomputable def slotIndex {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) : ℕ :=
  (GateOccurrences.occurrences C rows perm u).idxOf (i, rowIndex C rows perm i a, p.val)

/-- `slotIndex` is the occurrence-list index of the gate, enumerated row, and position. -/
theorem slotIndex_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) :
    slotIndex C rows perm u i a p =
      (GateOccurrences.occurrences C rows perm u).idxOf (i, rowIndex C rows perm i a, p.val) := rfl

/-- Every selected inactive argument has a slot strictly below the occurrence-list length.
Completeness supplies its row even when the assignment permutation is nontrivial.

**Proof sketch.** The inverse permutation supplies the row index, whose actual assignment
is `a`. Its argument and bit tests imply membership in the all-occurrence list. The library
index-of membership characterization places its index below that list's length. -/
theorem slotIndex_lt {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) (hargs : C.gates[i.val].args.Nodup)
    (hcomplete : ∀ a, a ∈ rows i) (hvertex : C.gates[i.val].args[p.val] = u)
    (hbit : a p = true) :
    slotIndex C rows perm u i a p < (GateOccurrences.occurrences C rows perm u).length := by
  rw [slotIndex_eq]
  apply List.idxOf_lt_length_iff.mpr
  apply (GateOccurrences.mem_occurrences_iff C rows perm u i _ p.val hargs).mpr
  refine ⟨rowIndex_lt C rows perm i a hcomplete, p.isLt, hvertex, ?_⟩
  rw [rowIndex_actual C rows perm i a hcomplete]
  exact hbit

section Fill

variable {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
  (s : GarbleSeed C K (ρ × ρ)) (u q : ℕ) (r : Fin (q + 1) → ρ)

/-- Fill the selected row's first nonce for argument position zero and its second nonce
for other positions, using that occurrence's challenge slot. Unselected rows and positions
whose slot is outside the supplied capacity retain their fixed nonce pair. -/
noncomputable def nonce (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) : ρ × ρ :=
  match GateOccurrences.selectedPosition C.gates[i.val] a u with
  | none => s.2.1 i a
  | some p =>
    let j := slotIndex C rows s.2.2 u i a p
    if h : j < q + 1 then
      if p.val = 0 then (r ⟨j, h⟩, (s.2.1 i a).2) else ((s.2.1 i a).1, r ⟨j, h⟩)
    else s.2.1 i a

/-- `nonce` changes exactly the selected argument's encryption-nonce half, reading the
independent nonce at its occurrence rank when that rank fits in `q+1` slots. -/
theorem nonce_eq (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
    nonce C rows s u q r i a =
      match GateOccurrences.selectedPosition C.gates[i.val] a u with
      | none => s.2.1 i a
      | some p =>
        let j := slotIndex C rows s.2.2 u i a p
        if h : j < q + 1 then
          if p.val = 0 then (r ⟨j, h⟩, (s.2.1 i a).2) else ((s.2.1 i a).1, r ⟨j, h⟩)
        else s.2.1 i a := rfl

/-- A row with no selected inactive argument retains both fixed nonce halves. -/
theorem nonce_of_none (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (h : GateOccurrences.selectedPosition C.gates[i.val] a u = none) :
    nonce C rows s u q r i a = s.2.1 i a := by
  rw [nonce_eq, h]

end Fill

/-- Replace only the inactive key at `u`, and fill one independent nonce for every selected
occurrence. All other keys, opposite nonce halves, and the complete row permutation remain
fixed. The selected key is not used to compute any occurrence address. [PS10, Theorem 163.7] -/
noncomputable def fill {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) : GarbleSeed C K (ρ × ρ) :=
  ((fun v b => if v = u ∧ b = true then k else s.1 v b),
    (nonce C rows s u.val q r, s.2.2))

/-- `fill` is the product of the one-label key replacement, occurrence-indexed nonce fill,
and the unchanged assignment permutation. -/
theorem fill_eq {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) :
    fill C rows s u q k r =
      ((fun v b => if v = u ∧ b = true then k else s.1 v b),
        (nonce C rows s u.val q r, s.2.2)) := rfl

/-- The filled key table changes just `(u,true)` to the independently supplied key `k`. -/
theorem fill_key {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (v : Fin C.size) (b : Bool) :
    (fill C rows s u q k r).1 v b = if v = u ∧ b = true then k else s.1 v b := rfl

/-- The filled row-coin table is exactly the occurrence-indexed `nonce` function. -/
theorem fill_nonce {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) :
    (fill C rows s u q k r).2.1 i a = nonce C rows s u.val q r i a := rfl

/-- The filled seed retains every original assignment permutation. -/
theorem fill_perm {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (i : Fin C.gates.length) :
    (fill C rows s u q k r).2.2 i = s.2.2 i := rfl

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed
