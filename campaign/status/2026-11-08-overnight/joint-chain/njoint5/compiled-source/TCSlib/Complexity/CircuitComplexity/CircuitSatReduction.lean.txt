/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionMachine
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionValid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lemma 6.11: CKT-SAT ≤p 3SAT

[AB09, Lem 6.11]: `CKT-SAT ≤p 3SAT`.  The correctness half — the string map
`BoolCircuit.dagCktSatToSAT3` (decode the circuit, build its Tseitin 3-CNF, serialize)
maps CKT-SAT exactly onto 3SAT — is `BoolCircuit.mem_dagCktSatLang_iff_mem_SAT3`
(`DAGCircuitSatLang.lean`).  This file proves the other half, "Clearly, the reduction
also runs in time polynomial in the input size" ([AB09, p. 111]): `dagCktSatToSAT3` is
polynomial-time computable, by a Turing machine of the campaign's model.

The map is decomposed as

  `dagCktSatToSAT3 w = if isValid w then outPrefix w ++ gateClauses w else serialize [[]]`

(`BoolCircuit.CktSatReduction.dagCktSatToSAT3_eq`), where

* `isValid w` (`w` describes a fan-in-two circuit) is polynomial-time by the circuit-value
  machine and De Morgan duality (`CircuitSatReductionValid.lean`);
* `outPrefix w` is the serialized output clause `(z_out)`, read off the end of the
  description by a one-pass transducer (`ClassNP/Transducer.lean`);
* `gateClauses w` is the serialized gate clauses, written by the three-counter emitter
  machine (`CircuitSatReductionSpec.lean`, `CircuitSatReductionMachine.lean`, time
  `200 (n + 1)²`);

and the pieces are assembled with the proved closure lemmas of FP: concatenation and the
timed conditional `Turing.FinTM.computesFunInTime_cond`.

## Main definitions

* `BoolCircuit.CktSatReduction.outPrefix` — the serialized output clause, from the
  description's output field.

## Main results

* `BoolCircuit.CktSatReduction.dagCktSatToSAT3_eq` — the decomposition above.
* `BoolCircuit.polyTimeComputable_dagCktSatToSAT3` — the reduction map is in FP.
* `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3` — **CKT-SAT ≤p 3SAT**.
  [AB09, Lem 6.11]

## Divergences from [AB09, §6.1.2]

* The circuit model, the circuit description and the 3SAT language are those of
  `DAGCircuitSatLang.lean` (see its divergences): CKT-SAT is the set of descriptions
  `DAGCircuit.encode` (unary numbers) of satisfiable fan-in-two circuits, and 3SAT is the
  campaign's `Complexity.SAT3` over `Std.Sat.CNF.serialize`.
* The polynomial is explicit but not optimized: the emitter prints a unary vertex index
  for every literal, so the output (and the running time) is quadratic in the
  description length.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1.2, Lemma 6.11, p. 111.)
-/

namespace BoolCircuit

open Std.Sat (CNF)

namespace CktSatReduction

open Emitter
open Complexity (polyTimeComputable_transduce)

/-- The serialized output clause read off a description: `1 1 · descTail w · 1 0`, which
on the description of a circuit with output vertex `o` is `1 · 1^(o+1) 0 1 · 0`, the
serialization of the clause `(z_o)` followed by the clause terminator. -/
def outPrefix (w : List Bool) : List Bool := [true, true] ++ descTail w ++ [true, false]

/-- The output-clause stage is polynomial-time (a transducer between two constants). -/
theorem polyTimeComputable_outPrefix : Complexity.PolyTimeComputable outPrefix :=
  ((Complexity.polyTimeComputable_const [true, true]).append
    (polyTimeComputable_transduce _ _ _)).append (Complexity.polyTimeComputable_const _)

/-- The gate-clause stage is polynomial-time: the emitter machine runs within
`200 (n + 1)²` steps. -/
theorem polyTimeComputable_gateClauses : Complexity.PolyTimeComputable gateClauses :=
  ⟨emTM, 200, 2, emTM_computes⟩

/-- **The decomposition of the reduction map**: on a description of a fan-in-two circuit
it is the serialized output clause followed by the serialized gate clauses, and
otherwise the serialization of `[[]]`.

**Proof sketch.** If `w` decodes to a fan-in-two circuit `C`, then `w = encode C`, the
Tseitin formula is the output clause `(z_out)` followed by the gate clauses, and the
serialization of a formula with a first clause is that clause's record followed by the
serialization of the rest; the two stages compute exactly these
(`descTail_encode`, `gateClauses_encode`).  Otherwise both sides are the fallback. -/
theorem dagCktSatToSAT3_eq (w : List Bool) :
    dagCktSatToSAT3 w =
      if isValid w then outPrefix w ++ gateClauses w else CNF.serialize [[]] := by
  unfold dagCktSatToSAT3 dagCktSatToCNF isValid
  cases hd : DAGCircuit.decode w with
  | none => simp
  | some C =>
    obtain ⟨n, C⟩ := C
    have hw := DAGCircuit.encode_of_decode hd
    simp only at hw
    by_cases hC : C.IsFaninTwo
    · simp only [hC, if_true, decide_true]
      subst hw
      rw [outPrefix, descTail_encode, gateClauses_encode C hC.2, DAGCircuit.toCNF]
      simp [CNF.serialize, CNF.serializeClause, CNF.serializeLit, encodeNat,
        List.replicate_succ]
    · simp [hC]

end CktSatReduction

open CktSatReduction CktSatReduction.Emitter

/-- **The reduction map of [AB09, Lem 6.11] is polynomial-time computable**: some Turing
machine computes `dagCktSatToSAT3` within a polynomial number of steps.  [AB09, p. 111:
"Clearly, the reduction also runs in time polynomial in the input size."]

**Proof sketch.** By `dagCktSatToSAT3_eq` the map is a conditional on `isValid`
(polynomial-time, `polyTimeComputable_isValid`) between the concatenation of the
output-clause and gate-clause stages (polynomial-time, `PolyTimeComputable.append`) and
a constant.  The timed conditional `Turing.FinTM.computesFunInTime_cond` runs the
selected branch after the test, within a constant times the sum of the three
polynomial bounds, which is again of the form `C (n + 1)^c`. -/
theorem polyTimeComputable_dagCktSatToSAT3 : Complexity.PolyTimeComputable dagCktSatToSAT3 := by
  obtain ⟨D, C₀, c₀, hD⟩ := polyTimeComputable_isValid
  obtain ⟨M₁, C₁, c₁, h₁⟩ := polyTimeComputable_outPrefix.append polyTimeComputable_gateClauses
  obtain ⟨M₂, C₂, h₂⟩ := Turing.FinTM.computesFunInTime_const (CNF.serialize [[]])
  obtain ⟨M, a, hM⟩ := Turing.FinTM.computesFunInTime_cond hD h₁ h₂
  refine ⟨M, a * (C₀ + C₁ + C₂ + 1), c₀ + c₁ + 1, fun x => ?_⟩
  rw [dagCktSatToSAT3_eq]
  refine (hM x).mono ?_
  set N := x.length + 1
  have hN : 1 ≤ N := by omega
  have e₀ : N ^ c₀ ≤ N ^ (c₀ + c₁ + 1) := Nat.pow_le_pow_right hN (by omega)
  have e₁ : N ^ c₁ ≤ N ^ (c₀ + c₁ + 1) := Nat.pow_le_pow_right hN (by omega)
  have e₂ : N ≤ N ^ (c₀ + c₁ + 1) := by
    simpa using Nat.pow_le_pow_right hN (show 1 ≤ c₀ + c₁ + 1 by omega)
  have e₃ : 1 ≤ N ^ (c₀ + c₁ + 1) := Nat.one_le_pow _ _ hN
  have hmax : max (C₁ * N ^ c₁) (C₂ * N) ≤ C₁ * N ^ c₁ + C₂ * N := by omega
  calc a * (C₀ * N ^ c₀ + max (C₁ * N ^ c₁) (C₂ * N) + 1)
      ≤ a * (C₀ * N ^ (c₀ + c₁ + 1) + (C₁ * N ^ (c₀ + c₁ + 1) + C₂ * N ^ (c₀ + c₁ + 1)) +
          N ^ (c₀ + c₁ + 1)) := by
        apply Nat.mul_le_mul_left
        have := Nat.mul_le_mul_left C₀ e₀
        have := Nat.mul_le_mul_left C₁ e₁
        have := Nat.mul_le_mul_left C₂ e₂
        omega
    _ = a * (C₀ + C₁ + C₂ + 1) * N ^ (c₀ + c₁ + 1) := by ring

/-- **[AB09, Lem 6.11]: CKT-SAT ≤p 3SAT.**  The language of descriptions of satisfiable
fan-in-two circuits (`dagCktSatLang`) Karp-reduces in polynomial time to the campaign's
3SAT (`Complexity.SAT3`), via the Tseitin map `dagCktSatToSAT3`.

**Proof sketch.** The map is polynomial-time computable
(`polyTimeComputable_dagCktSatToSAT3`) and is a many-one reduction
(`mem_dagCktSatLang_iff_mem_SAT3`: a description is in CKT-SAT iff its Tseitin formula
is a satisfiable 3-CNF). -/
theorem dagCktSatLang_polyTimeReducible_SAT3 :
    Complexity.PolyTimeReducible dagCktSatLang Complexity.SAT3 :=
  ⟨dagCktSatToSAT3, polyTimeComputable_dagCktSatToSAT3, mem_dagCktSatLang_iff_mem_SAT3⟩

end BoolCircuit
