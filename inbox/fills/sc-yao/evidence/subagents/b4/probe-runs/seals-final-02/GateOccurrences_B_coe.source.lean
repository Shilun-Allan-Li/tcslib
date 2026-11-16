/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.BigOperators
import TCSlib.Programs.Util.List
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
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
# All occurrences of a selected inactive wire label

The row enumeration and its assignment permutation are parameters. A selected wire
contributes at most one challenge occurrence per row, because a gate has distinct
arguments. Every row that uses its inactive label is enumerated, across every gate
that reads the wire. Fan-in two and a duplicate-free assignment enumeration give
at most four occurrences per gate. Fixed-width optional slots supply padding.

All no-dependence statements concern symbolic `(vertex, bit)` labels. A key-value
map may identify distinct labels; no inequality of actual keys is asserted.

## Main definitions

* `GateOccurrences.selectedPosition`: a row's selected inactive argument position.
* `GateOccurrences.rowSlots`: the selected positions of every row of one gate.
* `GateOccurrences.occurrences`: all gate/row/argument occurrences.
* `GateOccurrences.padded`: a fixed `q+1`-slot optional challenge vector.

## Main results

* Exact membership and exhaustion contracts for the occurrence list and padding.
* The fan-in-two occurrence bound and per-row uniqueness.
* Acyclicity, prior-fake-plaintext and sink-decoding label separation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (the hybrid over garbled gates).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences

open BoolCircuit

/-- Find an argument position whose vertex is `u` and whose actual assignment bit is
`true`, by searching `finRange g.args.length`. -/
def selectedPosition (g : DAGGate) (a : Fin g.args.length → Bool) (u : ℕ) :
    Option (Fin g.args.length) :=
  (List.finRange g.args.length).find? fun p => decide (g.args[p.val] = u ∧ a p = true)

/-- `selectedPosition g a u` searches all argument positions for
`g.args[p.val] = u ∧ a p = true`. -/
theorem selectedPosition_eq (g : DAGGate) (a : Fin g.args.length → Bool) (u : ℕ) :
    selectedPosition g a u =
      (List.finRange g.args.length).find? fun p => decide (g.args[p.val] = u ∧ a p = true) :=
  rfl

/-- For distinct gate arguments, the search returns `p` exactly when its vertex is `u`
and its actual row bit is `true`. Every qualifying position is therefore selected.

**Proof sketch.** A found position satisfies the search predicate. Conversely a qualifying
position makes the search succeed. Any found position has the same argument vertex;
distinctness of the argument list identifies its index with the qualifying position. -/
theorem selectedPosition_eq_some_iff (g : DAGGate) (a : Fin g.args.length → Bool) (u : ℕ)
    (hargs : g.args.Nodup) (p : Fin g.args.length) :
    selectedPosition g a u = some p ↔ g.args[p.val] = u ∧ a p = true := by
  rw [selectedPosition_eq]
  constructor
  · intro h
    exact of_decide_eq_true (List.find?_some
      (p := fun q : Fin g.args.length => decide (g.args[q.val] = u ∧ a q = true)) h)
  · intro hp
    have hex : ((List.finRange g.args.length).find?
        (fun p => decide (g.args[p.val] = u ∧ a p = true))).isSome :=
      List.find?_isSome.mpr ⟨p, List.mem_finRange p, decide_eq_true hp⟩
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hex
    have hqp : g.args[q.val] = u ∧ a q = true :=
      of_decide_eq_true (List.find?_some
        (p := fun q : Fin g.args.length => decide (g.args[q.val] = u ∧ a q = true)) hq)
    have heq : q = p := Fin.ext
      (hargs.getElem_inj_iff.mp (hqp.1.trans hp.1.symm))
    exact heq ▸ hq

/-- The row slots of `g` record each row index and the selected argument index after
applying the actual-assignment permutation `perm`. Rows without that occurrence are omitted. -/
def rowSlots (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ) : List (ℕ × ℕ) :=
  (List.range rows.length).filterMap fun r =>
    (selectedPosition g (perm (rows.getD r (fun _ => false))) u).map fun p => (r, p.val)

/-- `rowSlots` filters the row indices by the selected position and retains `(row, position)`. -/
theorem rowSlots_eq (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ) :
    rowSlots g rows perm u = (List.range rows.length).filterMap (fun r =>
      (selectedPosition g (perm (rows.getD r (fun _ => false))) u).map fun p => (r, p.val)) :=
  rfl

/-- The occurrence list concatenates every gate's row slots, retaining the gate index.
The row enumeration and the permutation describing its actual assignments are parameters. -/
def occurrences {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) : List (Fin C.gates.length × ℕ × ℕ) :=
  (List.finRange C.gates.length).flatMap fun i =>
    (rowSlots C.gates[i.val] (rows i) (perm i) u).map fun rp => (i, rp)

/-- `occurrences` is the concatenation of the indexed `rowSlots` over all gates. -/
theorem occurrences_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) :
    occurrences C rows perm u = (List.finRange C.gates.length).flatMap (fun i =>
      (rowSlots C.gates[i.val] (rows i) (perm i) u).map fun rp => (i, rp)) :=
  rfl

/-- A slot `(r,p)` occurs exactly when `r` is a row index, `p` is an argument index,
that argument is `u`, and its actual permuted assignment bit is `true`.

**Proof sketch.** Membership in a filtered map gives a row and a found position. The exact
search contract supplies the vertex and bit tests. Conversely those tests force the search
to select the given position, and the row index belongs to the enumerated range. -/
theorem mem_rowSlots_iff (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u r p : ℕ) (hargs : g.args.Nodup) :
    (r, p) ∈ rowSlots g rows perm u ↔ r < rows.length ∧
      ∃ hp : p < g.args.length, g.args[p] = u ∧
        perm (rows.getD r (fun _ => false)) ⟨p, hp⟩ = true := by
  rw [rowSlots_eq, List.mem_filterMap]
  constructor
  · rintro ⟨r', hr', h⟩
    obtain ⟨p', hp', hpair⟩ := Option.map_eq_some_iff.mp h
    cases hpair
    exact ⟨List.mem_range.mp hr', p'.isLt,
      (selectedPosition_eq_some_iff g _ u hargs p').mp hp'⟩
  · rintro ⟨hr, hp, hvertex, hbit⟩
    refine ⟨r, List.mem_range.mpr hr, Option.map_eq_some_iff.mpr ?_⟩
    exact ⟨⟨p, hp⟩, (selectedPosition_eq_some_iff g _ u hargs ⟨p, hp⟩).mpr
      ⟨hvertex, hbit⟩, rfl⟩

/-- A triple `(i,r,p)` occurs exactly when row `r` at gate `i` uses vertex `u` at
position `p` with actual assignment bit `true`. This lists occurrences across all gates.

**Proof sketch.** Flat-map membership selects a gate, and mapped-pair membership identifies
it with `i`. The one-gate slot contract gives the exact row, vertex, and assignment tests.
For the reverse direction, `i` belongs to the complete gate-index range. -/
theorem mem_occurrences_iff {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (r p : ℕ) (hargs : C.gates[i.val].args.Nodup) :
    (i, r, p) ∈ occurrences C rows perm u ↔ r < (rows i).length ∧
      ∃ hp : p < C.gates[i.val].args.length, C.gates[i.val].args[p] = u ∧
        perm i ((rows i).getD r (fun _ => false)) ⟨p, hp⟩ = true := by
  rw [occurrences_eq, List.mem_flatMap]
  constructor
  · rintro ⟨i', _, h⟩
    obtain ⟨rp, hrp, heq⟩ := List.mem_map.mp h
    cases heq
    exact (mem_rowSlots_iff _ _ _ _ _ _ hargs).mp hrp
  · intro h
    refine ⟨i, List.mem_finRange i, List.mem_map.mpr ?_⟩
    exact ⟨(r, p), (mem_rowSlots_iff _ _ _ _ _ _ hargs).mpr h, rfl⟩

/-- Every actual assignment with the selected inactive argument occurs at some row of its
gate, provided the row enumeration contains every assignment. The returned row's actual
assignment is exactly the prescribed one, even when `perm` is nontrivial.

**Proof sketch.** Enumerate the inverse image of the prescribed assignment under the row
permutation. A list-membership witness supplies its row index. Reading that row and applying
the permutation recovers the prescribed assignment. The membership contract then records
its selected argument position. -/
theorem exhaustive {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (hargs : C.gates[i.val].args.Nodup)
    (hcomplete : ∀ a, a ∈ rows i) (a : Fin C.gates[i.val].args.length → Bool)
    (p : Fin C.gates[i.val].args.length) (hvertex : C.gates[i.val].args[p.val] = u)
    (hbit : a p = true) :
    ∃ r, (i, r, p.val) ∈ occurrences C rows perm u ∧
      perm i ((rows i).getD r (fun _ => false)) = a := by
  obtain ⟨r, hr, hrow⟩ := List.mem_iff_getElem.mp (hcomplete ((perm i).symm a))
  have hactual : perm i ((rows i).getD r (fun _ => false)) = a := by
    rw [List.getD_eq_getElem _ _ hr, hrow, Equiv.apply_symm_apply]
  refine ⟨r, (mem_occurrences_iff C rows perm u i r p.val hargs).mpr ?_, hactual⟩
  exact ⟨hr, p.isLt, hvertex, hactual ▸ hbit⟩

/-- Two selected occurrences at the same gate and row have the same argument index,
because the gate's argument vertices are distinct. -/
theorem per_row_unique {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (i : Fin C.gates.length) (r p p' : ℕ) (hargs : C.gates[i.val].args.Nodup)
    (h : (i, r, p) ∈ occurrences C rows perm u)
    (h' : (i, r, p') ∈ occurrences C rows perm u) : p = p' := by
  obtain ⟨_, hp, hvertex, _⟩ := (mem_occurrences_iff C rows perm u i r p hargs).mp h
  obtain ⟨_, hp', hvertex', _⟩ := (mem_occurrences_iff C rows perm u i r p' hargs).mp h'
  exact hargs.getElem_inj_iff.mp (hvertex.trans hvertex'.symm)

/-- The row-slot list contains no duplicate pair, since its row indices come from a
range without repetitions. This holds even without distinct gate arguments. -/
theorem rowSlots_nodup (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ) :
    (rowSlots g rows perm u).Nodup := by
  rw [rowSlots_eq]
  apply List.Nodup.filterMap ?_ List.nodup_range
  intro r r' b hb hb'
  obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp (Option.mem_def.mp hb)
  obtain ⟨p', _, hp'⟩ := Option.map_eq_some_iff.mp (Option.mem_def.mp hb')
  exact (congrArg Prod.fst hp).trans (congrArg Prod.fst hp').symm

/-- The full occurrence list has no repeated gate/row/argument triple. Distinct gate
indices keep their row-slot lists disjoint.

**Proof sketch.** Each row-slot list has no repetitions and adding its gate index is
injective. The concatenated lists for distinct gates are disjoint because equality of
triples would identify their first coordinates. The gate-index enumeration has no repeats. -/
theorem occurrences_nodup {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) : (occurrences C rows perm u).Nodup := by
  rw [occurrences_eq, List.nodup_flatMap]
  constructor
  · intro i _
    exact (rowSlots_nodup _ _ _ _).map (fun _ _ h => congrArg Prod.snd h)
  · refine (List.nodup_finRange C.gates.length).imp ?_
    intro i j hij x hx hx'
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hx
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hx'
    exact hij ((congrArg Prod.fst ha).trans (congrArg Prod.fst hb).symm)

/-- A duplicate-free row enumeration for a gate of arity at most two contributes at
most four selected occurrences, for every assignment permutation.

**Proof sketch.** Filtering cannot increase the row count. A duplicate-free list of Boolean
assignments has length at most the cardinality `2^arity`. The arity bound makes this at most
four. The selected wire and the row permutation do not affect this count. -/
theorem length_rowSlots_le_four (g : DAGGate) (rows : List (Fin g.args.length → Bool))
    (perm : Equiv.Perm (Fin g.args.length → Bool)) (u : ℕ)
    (hrows : rows.Nodup) (hfanin : g.args.length ≤ 2) :
    (rowSlots g rows perm u).length ≤ 4 := by
  have hcard : rows.length ≤ 2 ^ g.args.length := by
    simpa only [Fintype.card_pi_const, Fintype.card_bool] using hrows.length_le_card
  calc
    (rowSlots g rows perm u).length ≤ rows.length := by
      rw [rowSlots_eq]
      simpa only [List.length_range] using List.length_filterMap_le
        (fun r => (selectedPosition g (perm (rows.getD r (fun _ => false))) u).map
          fun p => (r, p.val)) (List.range rows.length)
    _ ≤ 2 ^ g.args.length := hcard
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right Nat.zero_lt_two hfanin
    _ = 4 := rfl

/-- For a fan-in-two circuit with duplicate-free assignment rows, the complete occurrence
list has length at most `4 * C.gates.length`. [PS10, Theorem 163.7] This explicit bound
counts all uses of the selected wire, including uses in different gates.

**Proof sketch.** Each gate contributes at most four slots by the assignment-cardinality
bound. The concatenation length is the sum of these contributions. Bound the sum by four
times the length of the complete gate-index list, which has one index per gate. -/
theorem length_occurrences_le {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (hrows : ∀ i, (rows i).Nodup) (hfanin : C.IsFaninTwo) :
    (occurrences C rows perm u).length ≤ 4 * C.gates.length := by
  have hbound (i : Fin C.gates.length) :
      (rowSlots C.gates[i.val] (rows i) (perm i) u).length ≤ 4 :=
    length_rowSlots_le_four _ _ _ _ (hrows i)
      (((DAGCircuit.isFaninTwo_iff C).mp hfanin).2 _ (List.getElem_mem i.isLt))
  rw [occurrences_eq]
  have h := List.length_flatMap_le (List.finRange C.gates.length)
    (fun i => (rowSlots C.gates[i.val] (rows i) (perm i) u).map fun rp => (i, rp)) 4
    (fun i _ => by simpa only [List.length_map] using hbound i)
  simpa only [List.length_finRange, Nat.mul_comm] using h

/-- Pad `slots` to `q+1` optional entries by reading `slots[j.val]?`. Valid slots are
`some` values, and every index beyond the list is `none`. -/
def padded {α : Type*} (q : ℕ) (slots : List α) : Fin (q + 1) → Option α :=
  fun j => slots[j.val]?

/-- The `j`th padded entry is the optional list lookup `slots[j.val]?`. -/
theorem padded_eq {α : Type*} (q : ℕ) (slots : List α) (j : Fin (q + 1)) :
    padded q slots j = slots[j.val]? := rfl

/-- A value occurs in a padded vector exactly when it belongs to the original list,
provided the list fits in the `q+1` available slots.

**Proof sketch.** A successful padded lookup witnesses list membership. Conversely list
membership provides an index below the list length. The capacity bound places this index
in the finite padded domain, where the lookup returns the same value. -/
theorem padded_some_iff {α : Type*} (q : ℕ) (slots : List α)
    (hlen : slots.length ≤ q + 1) (a : α) :
    (∃ j, padded q slots j = some a) ↔ a ∈ slots := by
  constructor
  · rintro ⟨j, h⟩
    rw [padded_eq] at h
    exact List.mem_iff_getElem?.mpr ⟨j.val, h⟩
  · intro h
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
    refine ⟨⟨i, lt_of_lt_of_le hi hlen⟩, ?_⟩
    rw [padded_eq, List.getElem?_eq_getElem hi, hget]

/-- A padded entry is `none` exactly when its index is at least the original list length. -/
theorem padded_eq_none_iff {α : Type*} (q : ℕ) (slots : List α) (j : Fin (q + 1)) :
    padded q slots j = none ↔ slots.length ≤ j.val := by
  rw [padded_eq, List.getElem?_eq_none_iff]

/-- Padding the full occurrence list loses no occurrence when `q+1` is at least
`4 * C.gates.length`; padded `some` entries are exactly the original occurrences. -/
theorem padded_occurrences_some_iff {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u q : ℕ) (hrows : ∀ i, (rows i).Nodup) (hfanin : C.IsFaninTwo)
    (hbudget : 4 * C.gates.length ≤ q + 1) (s : Fin C.gates.length × ℕ × ℕ) :
    (∃ j, padded q (occurrences C rows perm u) j = some s) ↔
      s ∈ occurrences C rows perm u :=
  padded_some_iff q _ ((length_occurrences_le C rows perm u hrows hfanin).trans hbudget) s

/-- A wire used by gate `i₀` precedes that gate's output vertex `m+i₀`, by circuit
acyclicity. [PS10, Theorem 163.7] -/
theorem selected_wire_lt {m : ℕ} (C : DAGCircuit m) (i₀ : Fin C.gates.length)
    (u : ℕ) (hu : u ∈ C.gates[i₀.val].args) : u < m + i₀.val :=
  C.args_lt i₀.val i₀.isLt u hu

/-- Every hybrid plaintext label `(m+j, if j<i₀ then false else b)` differs from the
selected inactive label `(u,true)` whenever `u<m+i₀`. [PS10, Theorem 163.7] This is an
inequality of symbolic labels, so it makes no assumption about collisions of key values.

**Proof sketch.** Before gate `i₀` the plaintext label has bit `false`, which differs from
`true`. At gate `i₀` and later its vertex is at least `m+i₀`, strictly after `u`.
Thus in each case one coordinate differs. -/
theorem hybrid_plaintext_ne (m i₀ u j : ℕ) (hu : u < m + i₀) (b : Bool) :
    (m + j, if j < i₀ then false else b) ≠ (u, true) := by
  by_cases hj : j < i₀
  · intro h
    exact Bool.false_ne_true (by simpa only [if_pos hj] using congrArg Prod.snd h)
  · intro h
    have hv : m + j = u := congrArg Prod.fst h
    omega

/-- If gate `i₀` reads `u`, every hybrid plaintext label differs from `(u,true)`.
This is the circuit-indexed form of `hybrid_plaintext_ne`. [PS10, Theorem 163.7] -/
theorem hybrid_plaintext_ne_of_used {m : ℕ} (C : DAGCircuit m)
    (i₀ : Fin C.gates.length) (u : ℕ) (hu : u ∈ C.gates[i₀.val].args) (j : ℕ) (b : Bool) :
    (m + j, if j < i₀.val then false else b) ≠ (u, true) :=
  hybrid_plaintext_ne m i₀.val u j (selected_wire_lt C i₀ u hu) b

/-- Every active label `(v,false)` differs from the selected inactive label `(u,true)`,
including when the two labels refer to the same vertex. [PS10, Theorem 163.7] -/
theorem active_label_ne (v u : ℕ) : (v, false) ≠ (u, true) :=
  fun h => Bool.false_ne_true (congrArg Prod.snd h)

/-- If every designated output is a sink, a wire `u` read by gate `i₀` cannot occur in
any output decoding label `(outs j,b)`. [PS10, Theorem 163.7] The bit `b` is arbitrary,
so the statement covers both entries of every decoding pair.

**Proof sketch.** Equality of labels would identify the output vertex with `u`. The selected
gate reads `u`, whereas the sink hypothesis forbids this output vertex from belonging to
any gate's argument list. These two membership statements contradict one another. -/
theorem decoding_label_ne {m k : ℕ} (C : DAGCircuit m) (i₀ : Fin C.gates.length)
    (u : ℕ) (hu : u ∈ C.gates[i₀.val].args) (outs : Fin k → ℕ)
    (hsink : ∀ j g, g ∈ C.gates → outs j ∉ g.args) (j : Fin k) (b : Bool) :
    (outs j, b) ≠ (u, true) := by
  intro h
  have hv : outs j = u := congrArg Prod.fst h
  exact hsink j C.gates[i₀.val] (List.getElem_mem i₀.isLt) (hv.symm ▸ hu)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateOccurrences
