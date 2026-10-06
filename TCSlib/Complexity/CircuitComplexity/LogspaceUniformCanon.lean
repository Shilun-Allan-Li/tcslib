/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdj

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Canonicalizing circuits for the adjacency representation

The equivalence `BoolCircuit.DAGCircuitFamily.isLogspaceUniform_iff` of [AB09, p. 112]
needs canonical circuits: arguments in increasing order, output last. The first condition
is harmless. Listing every gate's arguments in increasing order without repetitions
(`BoolCircuit.DAGCircuit.canon`) changes neither the function computed nor the adjacency
representation. So every family whose output is its last vertex and whose adjacency
representation is logspace computable has a logspace-uniform canonical equivalent.

## Main definitions

* `BoolCircuit.DAGGate.canon`, `BoolCircuit.DAGCircuit.canon`,
  `BoolCircuit.DAGCircuitFamily.canon` — sorted, duplicate-free argument lists.

## Main results

* `BoolCircuit.DAGCircuitFamily.HasLogspaceAdjacency.exists_canonical_isLogspaceUniform` —
  a family with logspace adjacency representation and output last has a logspace-uniform
  canonical family computing the same functions. [AB09, p. 112]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.1, Definition 6.1; §6.2.1, p. 112.)
-/

namespace BoolCircuit

open Complexity

namespace DAGGate

/-- The canonical form of a gate: the same label, its arguments listed in increasing order
without repetitions. -/
def canon (g : DAGGate) : DAGGate :=
  ⟨g.kind, (List.range (g.args.foldr max 0 + 1)).filter (· ∈ g.args)⟩

/-- Every element of a list of naturals is at most its `foldr max`. -/
private lemma le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- The canonical form has the same arguments. -/
@[simp] lemma mem_canon_args {g : DAGGate} {a : ℕ} : a ∈ g.canon.args ↔ a ∈ g.args := by
  simp only [canon, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (le_foldr_max h), h⟩⟩

/-- The canonical form has the same label. -/
@[simp] lemma canon_kind (g : DAGGate) : g.canon.kind = g.kind := rfl

/-- The canonical form lists its arguments in strictly increasing order. -/
lemma canon_sorted (g : DAGGate) : g.canon.args.Sorted (· < ·) :=
  (List.sorted_lt_range _).filter _

/-- The canonical form computes the same value: a gate's value depends only on the set of
its arguments. -/
lemma eval_canon (g : DAGGate) (vals : List Bool) : g.canon.eval vals = g.eval vals := by
  have hall : (g.canon.args.all fun a => vals.getD a false) =
      g.args.all fun a => vals.getD a false := by
    rw [Bool.eq_iff_iff]; simp [List.all_eq_true]
  have hany : (g.canon.args.any fun a => vals.getD a false) =
      g.args.any fun a => vals.getD a false := by
    rw [Bool.eq_iff_iff]; simp [List.any_eq_true]
  unfold eval
  rw [canon_kind]
  split <;> simp only [hall, hany]

end DAGGate

/-- Running gate lists related by a value-preserving map gives the same values. -/
lemma runWith_map {β : Type} (f : DAGGate → List β → β) (h : DAGGate → DAGGate)
    (hf : ∀ g vs, f (h g) vs = f g vs) (gs : List DAGGate) (init : List β) :
    runWith f (gs.map h) init = runWith f gs init := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, runWith_cons, hf, ih]

namespace DAGCircuit

variable {n : ℕ}

/-- The canonical form of a circuit: every gate in canonical form, same output. -/
def canon (C : DAGCircuit n) : DAGCircuit n where
  gates := C.gates.map DAGGate.canon
  output := C.output
  args_lt := fun i hi a ha => by
    simp only [List.getElem_map, DAGGate.mem_canon_args] at ha
    exact C.args_lt i (by simpa using hi) a ha
  output_lt := by simpa using C.output_lt

/-- Canonicalization preserves the size. -/
@[simp] lemma size_canon (C : DAGCircuit n) : C.canon.size = C.size := by
  simp [canon, size]

/-- Canonicalization preserves the function computed. -/
lemma eval_canon (C : DAGCircuit n) : C.canon.eval = C.eval := by
  funext x
  simp only [eval, values, canon]
  rw [runWith_map _ _ DAGGate.eval_canon]

/-- Canonicalization preserves vertex types. -/
@[simp] lemma vtype_canon (C : DAGCircuit n) (i : ℕ) : C.canon.vtype i = C.vtype i := by
  simp only [vtype, canon, List.getElem?_map]
  split <;> simp [Option.map_map, Function.comp_def]

/-- Canonicalization preserves edges. -/
@[simp] lemma edge_canon (C : DAGCircuit n) (i j : ℕ) : C.canon.Edge i j ↔ C.Edge i j := by
  simp only [Edge, canon, List.getElem?_map]
  constructor
  · rintro ⟨hj, g, hg, hi⟩
    obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.mp hg
    exact ⟨hj, g', hg', DAGGate.mem_canon_args.mp hi⟩
  · rintro ⟨hj, g, hg, hi⟩
    exact ⟨hj, g.canon, by simp [hg], DAGGate.mem_canon_args.mpr hi⟩

/-- A circuit whose output is its last vertex has a canonical canonicalization. -/
lemma isCanonical_canon (C : DAGCircuit n) (h : C.output + 1 = C.size) : C.canon.IsCanonical :=
  ⟨fun g hg => by
    obtain ⟨g', -, rfl⟩ := List.mem_map.mp hg
    exact g'.canon_sorted, by rw [size_canon]; exact h⟩

end DAGCircuit

namespace DAGCircuitFamily

/-- The canonical form of a family: every circuit canonicalized. -/
def canon (C : DAGCircuitFamily) : DAGCircuitFamily := ⟨fun n => (C.circuit n).canon⟩

/-- Canonicalization preserves the adjacency representation (and the size bound). -/
lemma hasLogspaceAdjacency_canon {C : DAGCircuitFamily} (h : C.HasLogspaceAdjacency) :
    C.canon.HasLogspaceAdjacency := by
  obtain ⟨⟨a, k, hsz⟩, hS, hT, hE⟩ := h
  have e1 : C.canon.sizeLang = C.sizeLang := by
    ext y; simp [sizeLang, canon]
  have e2 : ∀ t, C.canon.typeLang t = C.typeLang t := by
    intro t; ext y; simp [typeLang, canon]
  have e3 : C.canon.edgeLang = C.edgeLang := by
    ext y; simp [edgeLang, canon]
  exact ⟨⟨a, k, fun n => by simpa [canon] using hsz n⟩, e1 ▸ hS, fun t => (e2 t) ▸ hT t,
    e3 ▸ hE⟩

/-- **Canonical logspace-uniform equivalents** [AB09, p. 112]: if a family has a logspace
adjacency representation and each circuit's output is its last vertex, then some canonical
family computing the same functions is logspace-uniform.

**Proof sketch.** Canonicalize every gate (sort and deduplicate its arguments). A gate's
value depends only on the set of its arguments (`DAGGate.eval_canon`), so the functions are
unchanged. Sizes, vertex types and edges are unchanged too, so the adjacency languages are
the same (`hasLogspaceAdjacency_canon`). The canonicalized family is canonical, and
`isLogspaceUniform_iff` applies. -/
theorem HasLogspaceAdjacency.exists_canonical_isLogspaceUniform {C : DAGCircuitFamily}
    (h : C.HasLogspaceAdjacency) (hout : ∀ n, (C.circuit n).output + 1 = (C.circuit n).size) :
    ∃ C' : DAGCircuitFamily, C'.IsCanonical ∧ (∀ n, (C'.circuit n).eval = (C.circuit n).eval) ∧
      C'.IsLogspaceUniform := by
  have hcan : C.canon.IsCanonical := fun n => (C.circuit n).isCanonical_canon (hout n)
  exact ⟨C.canon, hcan, fun n => (C.circuit n).eval_canon,
    (isLogspaceUniform_iff hcan).mpr (hasLogspaceAdjacency_canon h)⟩

end DAGCircuitFamily

end BoolCircuit
