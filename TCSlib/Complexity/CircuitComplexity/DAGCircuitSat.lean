/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CKT-SAT over the book's circuits, and the Tseitin 3-CNF of Lemma 6.11

[AB09, Def 6.9] and the construction in the proof of [AB09, Lem 6.11], over the book's
circuit model `BoolCircuit.DAGCircuit` ([AB09, Def 6.1]).  `CircuitSat.lean` and
`Encoding.lean` do the same over the formula model `BoolCircuit.TreeCircuit`; this file
follows the book's proof literally: **one variable per vertex** of the DAG (inputs and
gates alike; a gate read by several later gates is still one variable — no unrolling
into a tree), the four book clauses for a fan-in-two `∧`, the four analogous clauses for
`∨`, the two clauses for `¬`, and the unit clause on the output.  The result is a genuine
3-CNF over the campaign's audited carrier `Std.Sat.CNF ℕ` (the formula type of
`Complexity.SAT3`); vertex `v` is variable `v`.  The string-level form (CKT-SAT as a
`Language Bool`, the decoder, and the string map to `Complexity.SAT3`) is in
`DAGCircuitSatLang.lean`.

## Main definitions

* `BoolCircuit.DAGCircuit.Satisfiable` — some input makes the circuit output `1`.
* `BoolCircuit.dagCktSat` — CKT-SAT: the satisfiable fan-in-two circuits, tagged with
  their number of inputs.  [AB09, Def 6.9]
* `BoolCircuit.DAGGate.tseitin` — the clauses of one gate, stating that the gate's
  variable equals the gate applied to its arguments' variables.
* `BoolCircuit.DAGCircuit.toCNF` — the 3-CNF of [AB09, Lem 6.11]: all gate clauses
  and the output unit clause.

## Main results

* `BoolCircuit.DAGCircuit.satisfiable_iff_toCNF_satisfiable` — a circuit of fan-in at
  most two is satisfiable iff its Tseitin formula is (both directions of the
  equisatisfiability in [AB09, Lem 6.11]);
  `BoolCircuit.DAGCircuit.satisfiable_iff_toCNF_satisfiable_of_isFaninTwo` — the same for
  fan-in-two circuits.
* `BoolCircuit.mem_dagCktSat_iff_toCNF` — a fan-in-two circuit is in CKT-SAT iff its
  Tseitin formula is a satisfiable 3-CNF.
* `BoolCircuit.DAGCircuit.toCNF_widthAtMost` — every clause has at most `3` literals.
* `BoolCircuit.DAGCircuit.toCNF_length_le` — at most `4 · size + 1` clauses.
* `BoolCircuit.DAGCircuit.toCNF_var_lt_size` — every variable is a vertex, i.e. `< size`.

## Divergences from [AB09, §6.1.2]

* **Equisatisfiability here, `≤p` elsewhere.**  [AB09, Lem 6.11] asserts
  `CKT-SAT ≤p 3SAT`.  This file proves the correctness half (and size bounds on the
  output); the polynomial-time computability of the string map by a Turing machine, and
  hence `CKT-SAT ≤p 3SAT`, is `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3` in
  `CircuitSatReduction.lean`.
* **Degenerate gates.**  The DAG model ([AB09, Def 6.1] as formalized in
  `DAGCircuit.lean`) allows `∧`/`∨` gates of fan-in `0` (the constants `1`/`0`) and `1`
  (identity gates), which the book does not have.  They get the clauses of their truth
  tables: the unit clause `(zᵢ)` for an empty `∧`, `(¬zᵢ)` for an empty `∨`, and
  `(¬zᵢ ∨ zⱼ) ∧ (zᵢ ∨ ¬zⱼ)` for an identity gate — all within three literals.  The
  semantics of `DAGGate.eval` also gives meaning to non-well-formed `¬` gates (`¬` of
  the conjunction of the arguments); `¬` of nothing gets `(¬zᵢ)` and `¬` of two
  arguments the four clauses of `zᵢ = ¬(zⱼ ∧ zₖ)`.  Gates with three or more
  arguments get **no clauses** (they cannot be expressed in three-literal clauses
  without fresh variables); that is why equisatisfiability is stated for circuits of
  fan-in at most two, the book's circuits.
* **CKT-SAT contains only fan-in-two circuits.**  [AB09]'s circuits have fan-in two, so
  `dagCktSat` requires `DAGCircuit.IsFaninTwo` (well formed and fan-in at most two).
  Equisatisfiability itself needs only the fan-in bound, not well-formedness.
* **The output unit clause** is placed first rather than last; clause order is
  immaterial.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1.2, Definition 6.9 and Lemma 6.11, pp. 110–111.)
-/

namespace BoolCircuit

open Std.Sat (CNF)

/-! ## CKT-SAT -/

namespace DAGCircuit

variable {n : ℕ}

/-- A circuit is *satisfiable* when some input `u ∈ {0,1}ⁿ` makes it output `1`.
[AB09, Def 6.9] -/
def Satisfiable (C : DAGCircuit n) : Prop :=
  ∃ x : Fin n → Bool, C.eval x = true

/-- Being fan-in two is decidable: it is a bounded check over the finite gate list. -/
instance decidableIsFaninTwo (C : DAGCircuit n) : Decidable C.IsFaninTwo := by
  unfold IsFaninTwo IsWellFormed
  infer_instance

end DAGCircuit

/-- **CKT-SAT** [AB09, Def 6.9]: the satisfiable circuits, each tagged with its number of
inputs.  Following the book's circuits (fan-in two, [AB09, Def 6.1]) the circuit must
also be fan-in two (`DAGCircuit.IsFaninTwo`: well formed, every gate reading at most two
vertices).  The string language is `BoolCircuit.dagCktSatLang`. -/
def dagCktSat : Set ((n : ℕ) × DAGCircuit n) :=
  {C | C.2.IsFaninTwo ∧ C.2.Satisfiable}

/-- Membership in `dagCktSat` unfolded. -/
@[simp]
theorem mem_dagCktSat_iff (C : (n : ℕ) × DAGCircuit n) :
    C ∈ dagCktSat ↔ C.2.IsFaninTwo ∧ C.2.Satisfiable :=
  Iff.rfl

/-! ## The Tseitin clauses -/

namespace DAGGate

/-- The clauses of gate `g` placed at vertex `z`, expressing `z = g(args)` over the
vertex variables, as in the proof of [AB09, Lem 6.11].  A literal `(v, b)` is `zᵥ` when
`b = true` and `¬zᵥ` when `b = false`.

* `∧` of `j, k`: the book's four clauses
  `(¬zᵢ ∨ ¬zⱼ ∨ zₖ) ∧ (¬zᵢ ∨ zⱼ ∨ ¬zₖ) ∧ (¬zᵢ ∨ zⱼ ∨ zₖ) ∧ (zᵢ ∨ ¬zⱼ ∨ ¬zₖ)`, one per
  row of the truth table violating `zᵢ = zⱼ ∧ zₖ`;
* `∨` of `j, k`: the four clauses for `zᵢ = zⱼ ∨ zₖ`, built the same way;
* `¬` of `j`: the book's `(zᵢ ∨ zⱼ) ∧ (¬zᵢ ∨ ¬zⱼ)`.

The model's extra gates (see the module docstring): `∧`/`∨` of nothing give `(zᵢ)`/`(¬zᵢ)`,
`∧`/`∨` of one vertex `(¬zᵢ ∨ zⱼ) ∧ (zᵢ ∨ ¬zⱼ)`, `¬` of nothing `(¬zᵢ)`, `¬` of two
vertices the four clauses of `zᵢ = ¬(zⱼ ∧ zₖ)`.  A gate with three or more arguments gets
no clauses. -/
def tseitin (z : ℕ) (g : DAGGate) : CNF ℕ :=
  match g.kind, g.args with
  | .and, [] => [[(z, true)]]
  | .or, [] => [[(z, false)]]
  | .not, [] => [[(z, false)]]
  | .and, [j] => [[(z, false), (j, true)], [(z, true), (j, false)]]
  | .or, [j] => [[(z, false), (j, true)], [(z, true), (j, false)]]
  | .not, [j] => [[(z, true), (j, true)], [(z, false), (j, false)]]
  | .and, [j, k] =>
    [[(z, false), (j, false), (k, true)], [(z, false), (j, true), (k, false)],
     [(z, false), (j, true), (k, true)], [(z, true), (j, false), (k, false)]]
  | .or, [j, k] =>
    [[(z, false), (j, true), (k, true)], [(z, true), (j, true), (k, false)],
     [(z, true), (j, false), (k, true)], [(z, true), (j, false), (k, false)]]
  | .not, [j, k] =>
    [[(z, true), (j, true), (k, true)], [(z, true), (j, true), (k, false)],
     [(z, true), (j, false), (k, true)], [(z, false), (j, false), (k, false)]]
  | _, _ => []

/-- The gate clauses hold exactly when the gate's variable carries the gate's value:
if a gate of fan-in at most two reads, at each argument `v`, the value `a v`, then its
clauses at vertex `z` are satisfied by `a` iff `a z` equals the gate's output.

**Proof sketch.** Split on the label and on the (at most two) arguments, and check the
eight (at most) combinations of truth values of `zᵢ, zⱼ, zₖ`: each clause rules out
exactly one row of the gate's truth table. -/
theorem eval_tseitin (z : ℕ) (g : DAGGate) (hg : g.args.length ≤ 2) (a : ℕ → Bool)
    (vals : List Bool) (hv : ∀ v ∈ g.args, vals.getD v false = a v) :
    (g.tseitin z).eval a = true ↔ a z = g.eval vals := by
  obtain ⟨k, args⟩ := g
  match args, hg, hv with
  | [], _, _ =>
    cases k <;> cases hz : a z <;> simp [tseitin, eval, hz]
  | [j], _, hv =>
    have hj : vals[j]?.getD false = a j := by simpa using hv j (by simp)
    cases k <;> cases hz : a z <;> cases hj' : a j <;>
      simp [tseitin, eval, hz, hj, hj']
  | [j, l], _, hv =>
    have hj : vals[j]?.getD false = a j := by simpa using hv j (by simp)
    have hl : vals[l]?.getD false = a l := by simpa using hv l (by simp)
    cases k <;> cases hz : a z <;> cases hj' : a j <;> cases hl' : a l <;>
      simp [tseitin, eval, hz, hj, hj', hl, hl']
  | _ :: _ :: _ :: _, hg, _ => simp at hg

/-- Every clause of a gate has at most three literals. -/
theorem length_le_of_mem_tseitin (z : ℕ) (g : DAGGate) :
    ∀ c ∈ g.tseitin z, c.length ≤ 3 := by
  obtain ⟨k, args⟩ := g
  match args with
  | [] => cases k <;> simp [tseitin]
  | [_] => cases k <;> simp [tseitin]
  | [_, _] => cases k <;> simp [tseitin]
  | _ :: _ :: _ :: _ => cases k <;> simp [tseitin]

/-- A gate contributes at most four clauses. -/
theorem length_tseitin_le (z : ℕ) (g : DAGGate) : (g.tseitin z).length ≤ 4 := by
  obtain ⟨k, args⟩ := g
  match args with
  | [] => cases k <;> simp [tseitin]
  | [_] => cases k <;> simp [tseitin]
  | [_, _] => cases k <;> simp [tseitin]
  | _ :: _ :: _ :: _ => cases k <;> simp [tseitin]

/-- A gate's clauses mention only its own vertex `z` and the vertices it reads. -/
theorem var_mem_of_mem_tseitin (z : ℕ) (g : DAGGate) :
    ∀ c ∈ g.tseitin z, ∀ l ∈ c, l.1 = z ∨ l.1 ∈ g.args := by
  obtain ⟨k, args⟩ := g
  match args with
  | [] => cases k <;> simp [tseitin]
  | [_] => cases k <;> simp [tseitin] <;> aesop
  | [_, _] => cases k <;> simp [tseitin] <;> aesop
  | _ :: _ :: _ :: _ => cases k <;> simp [tseitin]

end DAGGate

/-- The clauses of a gate list whose first gate sits at vertex `z`: gate `i` of the list
sits at vertex `z + i`. -/
def tseitinGates (z : ℕ) : List DAGGate → CNF ℕ
  | [] => []
  | g :: gs => g.tseitin z ++ tseitinGates (z + 1) gs

/-- A gate list's clauses are satisfied iff every gate's clauses are. -/
theorem eval_tseitinGates (a : ℕ → Bool) (z : ℕ) (gs : List DAGGate) :
    (tseitinGates z gs).eval a = true ↔
      ∀ (i : ℕ) (h : i < gs.length), (gs[i].tseitin (z + i)).eval a = true := by
  induction gs generalizing z with
  | nil => simp [tseitinGates]
  | cons g gs ih =>
    simp only [tseitinGates, CNF.eval_append, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      match i, hi with
      | 0, _ => simpa using h0
      | i + 1, hi =>
        have := hs i (by simpa using hi)
        rwa [show z + 1 + i = z + (i + 1) by omega] at this
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      rwa [show z + (i + 1) = z + 1 + i by omega] at this

/-- Every clause of a gate list's clauses is a clause of one of its gates. -/
theorem exists_of_mem_tseitinGates {c : CNF.Clause ℕ} (z : ℕ) (gs : List DAGGate)
    (hc : c ∈ tseitinGates z gs) :
    ∃ (i : ℕ) (h : i < gs.length), c ∈ gs[i].tseitin (z + i) := by
  induction gs generalizing z with
  | nil => simp [tseitinGates] at hc
  | cons g gs ih =>
    simp only [tseitinGates, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨0, by simp, by simpa using hc⟩
    · obtain ⟨i, hi, hci⟩ := ih (z + 1) hc
      exact ⟨i + 1, by simpa using hi, by
        rwa [show z + (i + 1) = z + 1 + i by omega]⟩

/-- A gate list contributes at most four clauses per gate. -/
theorem length_tseitinGates_le (z : ℕ) (gs : List DAGGate) :
    (tseitinGates z gs).length ≤ 4 * gs.length := by
  induction gs generalizing z with
  | nil => simp [tseitinGates]
  | cons g gs ih =>
    have h1 := DAGGate.length_tseitin_le z g
    have h2 := ih (z + 1)
    simp only [tseitinGates, List.length_append, List.length_cons]
    omega

namespace DAGCircuit

variable {n : ℕ}

/-- **The Tseitin formula** of [AB09, Lem 6.11]: one variable per vertex (vertex `v` is
variable `v`; inputs are `0, …, n - 1` and gate `i` is `n + i`), the clauses
`DAGGate.tseitin` of every gate, and the unit clause `(z_out)` on the output vertex. -/
def toCNF (C : DAGCircuit n) : CNF ℕ :=
  [(C.output, true)] :: tseitinGates n C.gates

/-- Every clause of the Tseitin formula has at most three literals: it is a 3-CNF.
[AB09, Lem 6.11] -/
theorem toCNF_widthAtMost (C : DAGCircuit n) : C.toCNF.WidthAtMost 3 := by
  intro c hc
  simp only [toCNF, List.mem_cons] at hc
  rcases hc with rfl | hc
  · simp
  · obtain ⟨i, hi, hci⟩ := exists_of_mem_tseitinGates n C.gates hc
    exact DAGGate.length_le_of_mem_tseitin _ _ c hci

/-- The Tseitin formula has at most four clauses per gate, plus the output clause. -/
theorem toCNF_length_le_gates (C : DAGCircuit n) :
    C.toCNF.length ≤ 4 * C.gates.length + 1 := by
  have := length_tseitinGates_le n C.gates
  simp only [toCNF, List.length_cons]
  omega

/-- The Tseitin formula has at most `4 · size + 1` clauses, the size counting every
vertex, inputs included ([AB09, Def 6.1]). -/
theorem toCNF_length_le (C : DAGCircuit n) : C.toCNF.length ≤ 4 * C.size + 1 := by
  have := C.toCNF_length_le_gates
  simp only [size]
  omega

/-- Every variable of the Tseitin formula is a vertex of the circuit: it is below the
size. -/
theorem toCNF_var_lt_size (C : DAGCircuit n) : ∀ c ∈ C.toCNF, ∀ l ∈ c, l.1 < C.size := by
  intro c hc l hl
  simp only [toCNF, List.mem_cons] at hc
  rcases hc with rfl | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl
    exact C.output_lt
  · obtain ⟨i, hi, hci⟩ := exists_of_mem_tseitinGates n C.gates hc
    rcases DAGGate.var_mem_of_mem_tseitin _ _ c hci l hl with h | h
    · simp only [size, h]
      omega
    · have := C.args_lt i hi _ h
      simp only [size]
      omega

/-- The vertex values on input `x` satisfy every gate clause (fan-in at most two). -/
private theorem eval_tseitinGates_values (C : DAGCircuit n)
    (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) (x : Fin n → Bool) :
    (tseitinGates n C.gates).eval (fun v => (C.values x).getD v false) = true := by
  rw [eval_tseitinGates]
  intro i hi
  rw [DAGGate.eval_tseitin _ _ (hC _ (List.getElem_mem hi)) _ (C.values x) (fun _ _ => rfl)]
  exact C.values_getD_gate x hi

/-- An assignment satisfying every gate clause agrees, at every vertex, with the circuit's
values on the input it assigns to the input vertices (fan-in at most two). -/
private theorem values_getD_eq_of_eval_tseitinGates (C : DAGCircuit n)
    (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) (a : ℕ → Bool)
    (ha : (tseitinGates n C.gates).eval a = true) :
    ∀ v, v < n + C.gates.length → (C.values fun i => a i).getD v false = a v := by
  rw [eval_tseitinGates] at ha
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hvn : v < n
    · simpa using C.values_getD_input (fun i => a i) ⟨v, hvn⟩
    · obtain ⟨i, rfl⟩ : ∃ i, v = n + i := ⟨v - n, by omega⟩
      have hi : i < C.gates.length := by omega
      rw [C.values_getD_gate _ hi]
      refine ((DAGGate.eval_tseitin _ _ (hC _ (List.getElem_mem hi)) a _ ?_).mp
        (ha i hi)).symm
      intro u hu
      have hlt := C.args_lt i hi u hu
      exact ih u hlt (by omega)

/-- **Equisatisfiability** [AB09, Lem 6.11]: a circuit of fan-in at most two is
satisfiable iff its Tseitin formula is.  (`IsFaninTwo` also asks for well-formedness,
which is not needed here.)

**Proof sketch.** Forward: from an input `x` with `C(x) = 1`, assign each vertex variable
the value of that vertex on `x`; every gate's clauses hold because the vertex values obey
the gate recurrence (`DAGGate.eval_tseitin`), and the output clause holds because the
output vertex is `1`.  Backward: from a satisfying assignment `a`, read the input
`x = a` off the input vertices; by strong induction on the vertex number, `a` agrees with
the vertex values of `C` on `x` — inputs by definition, a gate because its clauses force
its variable to be the gate applied to its arguments' variables, which are earlier
vertices.  The output clause then says `C(x) = 1`. -/
theorem satisfiable_iff_toCNF_satisfiable (C : DAGCircuit n)
    (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) :
    C.Satisfiable ↔ C.toCNF.Satisfiable := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun v => (C.values x).getD v false, ?_⟩
    simp only [toCNF, CNF.eval_cons, eval_tseitinGates_values C hC x, Bool.and_true]
    simpa [CNF.Clause.eval] using hx
  · rintro ⟨a, ha⟩
    simp only [toCNF, CNF.eval_cons, Bool.and_eq_true] at ha
    obtain ⟨hout, hgates⟩ := ha
    refine ⟨fun i => a i, ?_⟩
    rw [eval, values_getD_eq_of_eval_tseitinGates C hC a hgates _ C.output_lt]
    simpa [CNF.Clause.eval] using hout

/-- Equisatisfiability for the circuits of CKT-SAT: a fan-in-two circuit is satisfiable
iff its Tseitin formula is. [AB09, Lem 6.11] -/
theorem satisfiable_iff_toCNF_satisfiable_of_isFaninTwo (C : DAGCircuit n)
    (hC : C.IsFaninTwo) : C.Satisfiable ↔ C.toCNF.Satisfiable :=
  C.satisfiable_iff_toCNF_satisfiable hC.2

end DAGCircuit

/-- **[AB09, Lem 6.11], formula level**: a fan-in-two circuit is in CKT-SAT iff its
Tseitin formula is a satisfiable 3-CNF.  (Equisatisfiability; the polynomial-time half
is `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`, `CircuitSatReduction.lean`.) -/
theorem mem_dagCktSat_iff_toCNF (C : (n : ℕ) × DAGCircuit n) (hC : C.2.IsFaninTwo) :
    C ∈ dagCktSat ↔ C.2.toCNF.WidthAtMost 3 ∧ C.2.toCNF.Satisfiable := by
  rw [mem_dagCktSat_iff, C.2.satisfiable_iff_toCNF_satisfiable_of_isFaninTwo hC]
  exact ⟨fun h => ⟨C.2.toCNF_widthAtMost, h.2⟩, fun h => ⟨hC, h.2⟩⟩

end BoolCircuit
