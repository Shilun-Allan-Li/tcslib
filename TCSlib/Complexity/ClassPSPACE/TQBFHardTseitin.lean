/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSat
import TCSlib.Complexity.Formulas.QBF
import TCSlib.Complexity.Formulas.CNFEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tseitin after the prefix, for circuits

[AB09, §4.2, p. 83]: a quantified formula whose matrix is a circuit becomes one with a CNF
matrix by the auxiliary variables of the Cook-Levin proof (Tseitin's transformation),
quantified existentially **after** the whole prefix. This file supplies the pointwise fact
that `Complexity.QBF.truth_exSuffix_of_pointwise` asks for, for the Tseitin formula
`BoolCircuit.DAGCircuit.toCNF` of a fan-in-two circuit (inputs are variables `0, …, n - 1`,
gate `i` is variable `n + i`): for **every** assignment `σ`, some assignment agreeing with
`σ` on the inputs satisfies the Tseitin formula iff the circuit outputs `1` on `σ`'s inputs.
It also bounds the variables of a CNF by the length of its serialization, which is how the
reduction counts the auxiliary variables.

Both directions cite `TCSlib.Complexity.CircuitComplexity.DAGCircuitSat`: the circuit's values
satisfy the gate clauses (`BoolCircuit.DAGCircuit.eval_tseitinGates_values`), and an assignment
satisfying them carries the circuit's values
(`BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates`).

## Main definitions

* none (theorems about the Tseitin formula `BoolCircuit.DAGCircuit.toCNF` and the
  serialization `Std.Sat.CNF.serialize`).

## Main results

* `Complexity.TQBFHard.toCNF_extension_iff` — the pointwise Tseitin lemma. [AB09, §4.2,
  p. 83; Lemma 6.11's construction]
* `Complexity.TQBFHard.numVars_le_length_serialize` — a CNF has fewer variables than its
  serialization has letters.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, p. 83; §6.1.2, Lemma 6.11.)
-/

namespace Complexity

namespace TQBFHard

open BoolCircuit Std.Sat

/-- **Tseitin after the prefix, pointwise** ([AB09, §4.2, p. 83], with the Tseitin formula of
Lemma 6.11): for a circuit of fan-in at most two and **any** assignment `σ`, some assignment
agreeing with `σ` on the input variables `0, …, n - 1` satisfies the Tseitin formula iff the
circuit outputs `1` on the inputs `σ 0, …, σ (n - 1)`.

**Proof sketch.** (⇐) Assign every vertex its value on `σ`'s inputs: the inputs agree with `σ`
(`values_getD_input`), the gate clauses hold
(`BoolCircuit.DAGCircuit.eval_tseitinGates_values`), and the output clause is the output. (⇒) By
`BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates` the satisfying assignment carries
the circuit's values on its own inputs, which are `σ`'s; the output clause makes the output
`1`. -/
theorem toCNF_extension_iff {n : ℕ} (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.args.length ≤ 2)
    (σ : ℕ → Bool) :
    (∃ τ : ℕ → Bool, (∀ v < n, τ v = σ v) ∧ C.toCNF.eval τ = true) ↔
      C.eval (fun i => σ i) = true := by
  constructor
  · rintro ⟨τ, hag, hτ⟩
    simp only [DAGCircuit.toCNF, CNF.eval_cons, Bool.and_eq_true] at hτ
    obtain ⟨hout, hgates⟩ := hτ
    have hin : (fun i : Fin n => σ i.val) = fun i : Fin n => τ i.val :=
      funext fun (i : Fin n) => (hag i.val i.isLt).symm
    rw [hin, DAGCircuit.eval,
      DAGCircuit.values_getD_eq_of_eval_tseitinGates C hC τ hgates _ C.output_lt]
    simpa [CNF.Clause.eval] using hout
  · intro h
    refine ⟨fun v => (C.values fun i => σ i).getD v false, fun v hv => ?_, ?_⟩
    · simpa using C.values_getD_input (fun i => σ i) ⟨v, hv⟩
    · simp only [DAGCircuit.toCNF, CNF.eval_cons, Bool.and_eq_true]
      exact ⟨by simpa [CNF.Clause.eval, DAGCircuit.eval] using h,
        DAGCircuit.eval_tseitinGates_values C hC (fun i => σ i)⟩

/-- A list's image under a member of a family is no longer than the flattened family. -/
private theorem length_le_length_flatMap {α β : Type} {f : α → List β} {a : α} {l : List α}
    (h : a ∈ l) : (f a).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- A right fold of `max` from `0` is at most a common bound of the list. -/
private theorem foldr_max_le {L : List ℕ} {B : ℕ} (h : ∀ a ∈ L, a ≤ B) : L.foldr max 0 ≤ B := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- **A CNF has fewer variables than its serialization has letters**: every literal `(v, b)`
is serialized as `1^(v+1) 0 b` (`Std.Sat.CNF.serializeLit`), so `numVars ≤ |serialize φ|`.

**Proof sketch.** `numVars` is a right fold of `max` over the literals of `φ` (each variable
plus one), so it suffices to bound each term (`foldr_max_le`). A literal `(v, b)` of a clause
`C` serializes to `v + 3` letters, which lie inside the serialization of `C`, itself inside
that of `φ` (`length_le_length_flatMap`, twice). -/
theorem numVars_le_length_serialize (φ : CNF ℕ) : φ.numVars ≤ (CNF.serialize φ).length := by
  unfold CNF.numVars
  apply foldr_max_le
  intro a ha
  obtain ⟨C, hC, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  have h1 : (CNF.serializeLit l).length ≤ (C.flatMap CNF.serializeLit).length :=
    length_le_length_flatMap hl
  have h2 : (true :: CNF.serializeClause C).length ≤
      (φ.flatMap fun C => true :: CNF.serializeClause C).length :=
    length_le_length_flatMap (f := fun C => true :: CNF.serializeClause C) hC
  have h3 : (φ.flatMap fun C => true :: CNF.serializeClause C).length ≤
      (CNF.serialize φ).length := by
    simp [CNF.serialize]
  have h4 : (C.flatMap CNF.serializeLit).length ≤ (true :: CNF.serializeClause C).length := by
    simp only [CNF.serializeClause, List.length_cons, List.length_append]
    omega
  have h5 : (CNF.serializeLit l).length = l.1 + 3 := by
    simp [CNF.serializeLit]
  omega

end TQBFHard

end Complexity
