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

/-- The enumerated row of actual assignment `a` is the index of `perm.symm a` in `rows`.
`rowIndex C rows perm i a = (rows i).idxOf ((perm i).symm a)`. -/
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

/-- A complete assignment enumeration contains the row index of every actual assignment.
`rowIndex C rows perm i a < (rows i).length`. -/
theorem rowIndex_lt {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (hcomplete : ∀ a, a ∈ rows i) : rowIndex C rows perm i a < (rows i).length :=
  List.idxOf_lt_length_iff.mpr (hcomplete ((perm i).symm a))

/-- Reading the enumerated row at `rowIndex` and applying its permutation recovers the
prescribed actual assignment exactly.
`perm i ((rows i).getD (rowIndex C rows perm i a) (fun _ => false)) = a`. -/
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
of `(i,rowIndex a,p)` in the complete occurrence list.
`slotIndex C rows perm u i a p = @List.idxOf (Fin C.gates.length × ℕ × ℕ) instBEqOfDecidableEq (i,
rowIndex C rows perm i a, p.val) (GateOccurrences.occurrences C rows perm u)`. -/
noncomputable def slotIndex {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) : ℕ :=
  @List.idxOf (Fin C.gates.length × ℕ × ℕ) instBEqOfDecidableEq
    (i, rowIndex C rows perm i a, p.val) (GateOccurrences.occurrences C rows perm u)

/-- `slotIndex` is the occurrence-list index of the gate, enumerated row, and position.
`slotIndex C rows perm u i a p = @List.idxOf (Fin C.gates.length × ℕ × ℕ) instBEqOfDecidableEq (i,
rowIndex C rows perm i a, p.val) (GateOccurrences.occurrences C rows perm u)`. -/
theorem slotIndex_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) :
    slotIndex C rows perm u i a p =
      @List.idxOf (Fin C.gates.length × ℕ × ℕ) instBEqOfDecidableEq
    (i, rowIndex C rows perm i a, p.val) (GateOccurrences.occurrences C rows perm u) := rfl

/-- Every selected inactive argument has a slot strictly below the occurrence-list length.
Completeness supplies its row even when the assignment permutation is nontrivial.
`slotIndex C rows perm u i a p < (GateOccurrences.occurrences C rows perm u).length`.

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
  letI : BEq (Fin C.gates.length × ℕ × ℕ) := instBEqOfDecidableEq
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
whose slot is outside the supplied capacity retain their fixed nonce pair.
`nonce C rows s u q r i a = (GateOccurrences.selectedPosition C.gates[i.val] a u).elim (s.2.1 i a)
(fun p => let j := slotIndex C rows s.2.2 u i a p; if h : j < q + 1 then if p.val = 0 then (r ⟨j,
h⟩, (s.2.1 i a).2) else ((s.2.1 i a).1, r ⟨j, h⟩) else s.2.1 i a)`. -/
noncomputable def nonce (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) : ρ × ρ :=
  (GateOccurrences.selectedPosition C.gates[i.val] a u).elim (s.2.1 i a) fun p =>
    let j := slotIndex C rows s.2.2 u i a p
    if h : j < q + 1 then
      if p.val = 0 then (r ⟨j, h⟩, (s.2.1 i a).2) else ((s.2.1 i a).1, r ⟨j, h⟩)
    else s.2.1 i a

/-- `nonce` changes exactly the selected argument's encryption-nonce half, reading the
independent nonce at its occurrence rank when that rank fits in `q+1` slots.
`nonce C rows s u q r i a = (GateOccurrences.selectedPosition C.gates[i.val] a u).elim (s.2.1 i a)
(fun p => let j := slotIndex C rows s.2.2 u i a p; if h : j < q + 1 then if p.val = 0 then (r ⟨j,
h⟩, (s.2.1 i a).2) else ((s.2.1 i a).1, r ⟨j, h⟩) else s.2.1 i a)`. -/
theorem nonce_eq (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
    nonce C rows s u q r i a =
      (GateOccurrences.selectedPosition C.gates[i.val] a u).elim (s.2.1 i a) (fun p =>
        let j := slotIndex C rows s.2.2 u i a p
        if h : j < q + 1 then
          if p.val = 0 then (r ⟨j, h⟩, (s.2.1 i a).2) else ((s.2.1 i a).1, r ⟨j, h⟩)
        else s.2.1 i a) := rfl

/-- A row with no selected inactive argument retains both fixed nonce halves.
`nonce C rows s u q r i a = s.2.1 i a`. -/
theorem nonce_of_none (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (h : GateOccurrences.selectedPosition C.gates[i.val] a u = none) :
    nonce C rows s u q r i a = s.2.1 i a := by
  rw [nonce_eq, h, Option.elim_none]

/-- A selected row whose occurrence rank fits the capacity receives exactly that independent
nonce in its selected encryption layer, retaining the opposite fixed nonce half.
`nonce C rows s u q r i a = if p.val = 0 then (r ⟨slotIndex C rows s.2.2 u i a p, hslot⟩, (s.2.1 i
a).2) else ((s.2.1 i a).1, r ⟨slotIndex C rows s.2.2 u i a p, hslot⟩)`. -/
theorem nonce_of_some (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length)
    (h : GateOccurrences.selectedPosition C.gates[i.val] a u = some p)
    (hslot : slotIndex C rows s.2.2 u i a p < q + 1) :
    nonce C rows s u q r i a =
      if p.val = 0 then (r ⟨slotIndex C rows s.2.2 u i a p, hslot⟩, (s.2.1 i a).2)
      else ((s.2.1 i a).1, r ⟨slotIndex C rows s.2.2 u i a p, hslot⟩) := by
  rw [nonce_eq, h, Option.elim_some]
  exact dif_pos hslot

end Fill

/-- Replace only the inactive key at `u`, and fill one independent nonce for every selected
occurrence. All other keys, opposite nonce halves, and the complete row permutation remain
fixed. The selected key is not used to compute any occurrence address. [PS10, Theorem 163.7]
`fill C rows s u q k r = ((fun v b => if v = u ∧ b = true then k else s.1 v b), (nonce C rows s
u.val q r, s.2.2))`. -/
noncomputable def fill {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) : GarbleSeed C K (ρ × ρ) :=
  ((fun v b => if v = u ∧ b = true then k else s.1 v b),
    (nonce C rows s u.val q r, s.2.2))

/-- `fill` is the product of the one-label key replacement, occurrence-indexed nonce fill,
and the unchanged assignment permutation.
`fill C rows s u q k r = ((fun v b => if v = u ∧ b = true then k else s.1 v b), (nonce C rows s
u.val q r, s.2.2))`. -/
theorem fill_eq {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) :
    fill C rows s u q k r =
      ((fun v b => if v = u ∧ b = true then k else s.1 v b),
        (nonce C rows s u.val q r, s.2.2)) := rfl

/-- The filled key table changes just `(u,true)` to the independently supplied key `k`.
`(fill C rows s u q k r).1 v b = if v = u ∧ b = true then k else s.1 v b`. -/
theorem fill_key {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (v : Fin C.size) (b : Bool) :
    (fill C rows s u q k r).1 v b = if v = u ∧ b = true then k else s.1 v b := rfl

/-- The filled row-coin table is exactly the occurrence-indexed `nonce` function.
`(fill C rows s u q k r).2.1 i a = nonce C rows s u.val q r i a`. -/
theorem fill_nonce {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) :
    (fill C rows s u q k r).2.1 i a = nonce C rows s u.val q r i a := rfl

/-- The filled seed retains every original assignment permutation.
`(fill C rows s u q k r).2.2 i = s.2.2 i`. -/
theorem fill_perm {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (i : Fin C.gates.length) :
    (fill C rows s u q k r).2.2 i = s.2.2 i := rfl

/-- Reading the selected inactive coordinate of the filled key table returns `k`.
`(fill C rows s u q k r).1 u true = k`. -/
theorem fill_key_selected {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) : (fill C rows s u q k r).1 u true = k :=
  (fill_key C rows s u q k r u true).trans (if_pos ⟨rfl, rfl⟩)

/-- Every key coordinate with a different symbolic label retains its fixed value.
No inequality between key values is assumed.
`(fill C rows s u q k r).1 v b = s.1 v b`. -/
theorem fill_key_other {m : ℕ} {K ρ : Type} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (v : Fin C.size) (b : Bool) (h : (v, b) ≠ (u, true)) :
    (fill C rows s u q k r).1 v b = s.1 v b :=
  (fill_key C rows s u q k r v b).trans (if_neg (fun h' => h (Prod.ext h'.1 h'.2)))

/-- Total wire-key lookup in the filled seed changes exactly the symbolic label `(u,true)`,
including the default behavior beyond the circuit. Key values may collide.
`keyAt C (fill C rows s u q k r) v b = if (v, b) = (u.val, true) then k else keyAt C s v b`.

**Proof sketch.** At an in-range vertex, read the filled key table and identify equality of
finite vertex/bit coordinates with equality of natural vertex/bit labels. Outside the circuit,
both seeds return the default key, and the label cannot equal the in-range selected label. -/
theorem fill_keyAt {m : ℕ} {K ρ : Type} [Inhabited K] (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (v : ℕ) (b : Bool) :
    keyAt C (fill C rows s u q k r) v b =
      if (v, b) = (u.val, true) then k else keyAt C s v b := by
  by_cases hv : v < C.size
  · rw [keyAt_eq, dif_pos hv, keyAt_eq, dif_pos hv, fill_key]
    have hcond : ((⟨v, hv⟩ : Fin C.size) = u ∧ b = true) ↔ (v, b) = (u.val, true) :=
      ⟨fun h => Prod.ext (congrArg Fin.val h.1) h.2,
        fun h => ⟨Fin.ext (congrArg Prod.fst h), congrArg Prod.snd h⟩⟩
    simp only [hcond]
  · have hne : (v, b) ≠ (u.val, true) := by
      intro h
      have hval : v = u.val := congrArg Prod.fst h
      exact hv (hval.symm ▸ u.isLt)
    rw [keyAt_eq, dif_neg hv, if_neg hne, keyAt_eq, dif_neg hv]

/-- The filled argument-key list replaces exactly those coordinates bearing symbolic label
`(u,true)`, with all other wire-key values read from the fixed seed.
`argKeys C (fill C rows s u q k r) i a = List.ofFn (fun p => if (C.gates[i.val].args[p.val], a p) =
(u.val, true) then k else keyAt C s C.gates[i.val].args[p.val] (a p))`. -/
theorem fill_argKeys {m : ℕ} {K ρ : Type} [Inhabited K] (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) :
    argKeys C (fill C rows s u q k r) i a = List.ofFn (fun p =>
      if (C.gates[i.val].args[p.val], a p) = (u.val, true) then k
      else keyAt C s C.gates[i.val].args[p.val] (a p)) :=
  (argKeys_eq C _ i a).trans (congrArg List.ofFn (funext fun p =>
    fill_keyAt C rows s u q k r C.gates[i.val].args[p.val] (a p)))

/-- With distinct argument vertices, the selected inactive label occurs at exactly one
position: `(args[t],a t)=(u,true)` if and only if `t=p`. This excludes double use of the same
symbolic key within a row without excluding collisions between actual key values. -/
theorem argument_label_eq_iff (g : DAGGate) (a : Fin g.args.length → Bool) (u : ℕ)
    (hargs : g.args.Nodup) (p : Fin g.args.length) (hvertex : g.args[p.val] = u)
    (hbit : a p = true) (t : Fin g.args.length) :
    (g.args[t.val], a t) = (u, true) ↔ t = p := by
  constructor
  · intro h
    exact Fin.ext (hargs.getElem_inj_iff.mp ((congrArg Prod.fst h).trans hvertex.symm))
  · rintro rfl
    exact Prod.ext hvertex hbit

/-- A row with selected position `p` has exactly its `p`th argument key replaced by `k`.
The other argument key is fixed even if its value happens to equal `k`.
`argKeys C (fill C rows s u q k r) i a = (argKeys C s i a).set p.val k`.

**Proof sketch.** Compare entries of the two lists. The key-table reader changes an entry
exactly when its symbolic label is selected. Argument distinctness identifies that event
with equality to `p`. The list-update reader changes exactly this same position. -/
theorem fill_argKeys_some {m : ℕ} {K ρ : Type} [Inhabited K] (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) (p : Fin C.gates[i.val].args.length)
    (hargs : C.gates[i.val].args.Nodup)
    (h : GateOccurrences.selectedPosition C.gates[i.val] a u.val = some p) :
    argKeys C (fill C rows s u q k r) i a = (argKeys C s i a).set p.val k := by
  obtain ⟨hvertex, hbit⟩ :=
    (GateOccurrences.selectedPosition_eq_some_iff _ _ _ hargs p).mp h
  rw [fill_argKeys, argKeys_eq]
  simp only [Fin.getElem_fin]
  apply List.ext_getElem (by simp only [List.length_ofFn, List.length_set])
  intro j hj hj'
  have hjg : j < C.gates[i.val].args.length := by simpa only [List.length_ofFn] using hj
  simp only [List.getElem_ofFn, List.getElem_set]
  have hc := argument_label_eq_iff C.gates[i.val] a u.val hargs p hvertex hbit ⟨j, hjg⟩
  by_cases hjp : j = p.val
  · have hfin : (⟨j, hjg⟩ : Fin C.gates[i.val].args.length) = p := Fin.ext hjp
    rw [if_pos (hc.mpr hfin), if_pos hjp.symm]
  · have hfin : (⟨j, hjg⟩ : Fin C.gates[i.val].args.length) ≠ p :=
      fun h' => hjp (congrArg Fin.val h')
    rw [if_neg (fun h' => hfin (hc.mp h')), if_neg (Ne.symm hjp)]

/-- A row with no selected inactive argument keeps its entire argument-key list fixed.
`argKeys C (fill C rows s u q k r) i a = argKeys C s i a`.

**Proof sketch.** A position bearing the selected label would force the position search
to return that position, contrary to its `none` result. Thus every coordinate uses the
unchanged branch of the filled-key reader. -/
theorem fill_argKeys_none {m : ℕ} {K ρ : Type} [Inhabited K] (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
    (r : Fin (q + 1) → ρ) (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) (hargs : C.gates[i.val].args.Nodup)
    (h : GateOccurrences.selectedPosition C.gates[i.val] a u.val = none) :
    argKeys C (fill C rows s u q k r) i a = argKeys C s i a := by
  rw [fill_argKeys, argKeys_eq]
  simp only [Fin.getElem_fin]
  apply congrArg List.ofFn
  funext t
  have hne : (C.gates[i.val].args[t.val], a t) ≠ (u.val, true) := by
    intro hlabel
    have hs := (GateOccurrences.selectedPosition_eq_some_iff _ _ _ hargs t).mpr
      ⟨congrArg Prod.fst hlabel, congrArg Prod.snd hlabel⟩
    rw [h] at hs
    contradiction
  exact if_neg hne

/-- Applying a row permutation and then finding its enumerated row recovers the original
row index, when the enumeration has no repetitions.
`rowIndex C rows perm i (perm i ((rows i).getD r (fun _ => false))) = r`. -/
theorem rowIndex_of_row {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (i : Fin C.gates.length) (r : ℕ) (hr : r < (rows i).length) (hrows : (rows i).Nodup) :
    rowIndex C rows perm i (perm i ((rows i).getD r (fun _ => false))) = r := by
  rw [rowIndex_eq, Equiv.symm_apply_apply, List.getD_eq_getElem _ _ hr]
  exact List.idxOf_getElem hrows r hr

/-- An occurrence read at list index `j` maps back to exactly challenge index `j`.
The row enumeration's distinctness recovers its row index, and the occurrence enumeration's
distinctness recovers its challenge index.
`slotIndex C rows perm u i (perm i ((rows i).getD r (fun _ => false))) p = j`.

**Proof sketch.** The actual assignment at the stored row maps back to that row by the inverse
row-index reader. The slot index is therefore the index of the looked-up triple. Since the
occurrence list has no repetitions, index-of the entry at `j` is `j`. -/
theorem slotIndex_of_lookup {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (r j : ℕ) (p : Fin C.gates[i.val].args.length)
    (hr : r < (rows i).length) (hrows : (rows i).Nodup)
    (hlookup : (GateOccurrences.occurrences C rows perm u)[j]? = some (i, r, p.val)) :
    slotIndex C rows perm u i (perm i ((rows i).getD r (fun _ => false))) p = j := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hlookup
  rw [slotIndex_eq, rowIndex_of_row C rows perm i r hr hrows, ← hget]
  exact List.idxOf_getElem (GateOccurrences.occurrences_nodup C rows perm u) j hj

/-- Reading a selected argument's padded challenge slot returns its exact occurrence triple.
This is the forward inverse of the occurrence-rank map.
`GateOccurrences.padded q (GateOccurrences.occurrences C rows perm u) ⟨slotIndex C rows perm u i a
p, hslot⟩ = some (i, rowIndex C rows perm i a, p.val)`. -/
theorem slotIndex_padded {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) (hargs : C.gates[i.val].args.Nodup)
    (hcomplete : ∀ a, a ∈ rows i) (hvertex : C.gates[i.val].args[p.val] = u)
    (hbit : a p = true) (hslot : slotIndex C rows perm u i a p < q + 1) :
    GateOccurrences.padded q (GateOccurrences.occurrences C rows perm u)
      ⟨slotIndex C rows perm u i a p, hslot⟩ =
        some (i, rowIndex C rows perm i a, p.val) := by
  letI : BEq (Fin C.gates.length × ℕ × ℕ) := instBEqOfDecidableEq
  have hidx := slotIndex_lt C rows perm u i a p hargs hcomplete hvertex hbit
  rw [GateOccurrences.padded_eq]
  change (GateOccurrences.occurrences C rows perm u)[slotIndex C rows perm u i a p]? =
    some (i, rowIndex C rows perm i a, p.val)
  rw [slotIndex_eq]
  exact List.getElem?_idxOf (List.idxOf_lt_length_iff.mp hidx)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSeed
