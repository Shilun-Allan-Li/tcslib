/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Languages with P-uniform circuits are in P

[AB09, Thm 6.13] states that a language is computable by a P-uniform circuit family
[AB09, Def 6.12] if and only if it is in `P`. This file proves the direction
"P-uniform circuits ⇒ `P`", following the book's proof sketch (p. 111–112): on input `x`,
run the uniformity machine on `1^|x|` to obtain the description of `C_|x|`, then evaluate
that circuit on `x`. Formally this is a polynomial-time Karp reduction to the
circuit-value language `BoolCircuit.CVAL`, which is in `P` (`BoolCircuit.CVAL_mem_P`).

## Main definitions

None (the reduction function is `fun x => Turing.pairEncode (f (1^|x|)) x` for the
uniformity function `f`; it is not given a name).

## Main results

* `BoolCircuit.DAGCircuitFamily.mem_language_iff_pairEncode_mem_CVAL` — for a fan-in-two
  family, `x` is in the family's language iff `⟨C_|x|, x⟩ ∈ CVAL`.
* `BoolCircuit.DAGCircuitFamily.IsPUniform.polyTimeReducible_CVAL` — the language of a
  P-uniform fan-in-two family Karp-reduces to `CVAL`.
* `BoolCircuit.DAGCircuitFamily.IsPUniform.language_mem_P` — the language of a P-uniform
  fan-in-two family is in `P`.
* `Language.mem_P_of_isPUniform` — a language decided by a P-uniform fan-in-two circuit
  family is in `P`. [AB09, Thm 6.13, "if" direction]

## Divergences from [AB09, Thm 6.13]

* **One direction here.** The converse ("`L ∈ P` ⇒ `L` has P-uniform circuits") needs the
  P-uniform form of [AB09, Thm 6.6] (the circuit produced from a machine's tableau is
  computable from `1ⁿ` in polynomial time, [AB09, Remark 6.7]); it is
  `Language.exists_isPUniform_of_mem_P` in `CircuitComplexity/UniformTableau.lean`, where
  the full equivalence `Language.mem_P_iff_exists_isPUniform` is stated.
* **Fan-in two is a hypothesis.** [AB09, Def 6.1] builds fan-in two into the notion of a
  circuit; in `BoolCircuit.DAGCircuit` it is the separate predicate
  `DAGCircuitFamily.HasFaninTwo`, which this theorem assumes (the circuit evaluator, and
  `CVAL`, are for fan-in-two circuits).
* **The circuit description** is `BoolCircuit.DAGCircuit.encode` (see `Uniform.lean`), and
  `⟨C, x⟩` is `Turing.pairEncode C.encode x` (see `CircuitEval.lean`).
* The language is given as `C.language = L` so the theorem applies to any presentation
  of `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.2, Definition 6.12, Theorem 6.13.)
-/

namespace BoolCircuit

open Turing Complexity

/-! ## The reduction to the circuit-value problem -/

namespace DAGCircuitFamily

/-- On a family whose circuits all have fan-in two, membership of `x` in the family's
language is membership of the pair `⟨C_|x|, x⟩` in the circuit-value language `CVAL`.

**Proof sketch.** Forward: `C_|x|` itself witnesses membership. Backward: a witness
`(y, D)` has `pairEncode D.encode y = pairEncode C_|x|.encode x`, so `y = x` and (by
injectivity of the pairing and of the description, `DAGCircuit.encode_injective`)
`D = C_|x|`. -/
theorem mem_language_iff_pairEncode_mem_CVAL (C : DAGCircuitFamily) (hF : C.HasFaninTwo)
    (x : List Bool) :
    x ∈ C.language ↔ pairEncode (C.circuit x.length).encode x ∈ CVAL := by
  constructor
  · intro hx
    exact ⟨x, C.circuit x.length, hF _, hx, rfl⟩
  · rintro ⟨y, D, -, hev, heq⟩
    obtain ⟨he, rfl⟩ := Prod.mk.inj (pairEncode_injective (a₁ := (_, x)) (a₂ := (_, y)) heq)
    have hD : C.circuit x.length = D := DAGCircuit.encode_injective _ he
    rw [mem_language_iff, hD]
    exact hev

/-- **A P-uniform fan-in-two family reduces to circuit evaluation** [AB09, proof of
Thm 6.13]: its language Karp-reduces to `CVAL` via `x ↦ ⟨C_|x|, x⟩`.

**Proof sketch.** With `f` the uniformity function (`f (1ⁿ) = C_n.encode`), the
reduction is `x ↦ pairEncode (f (1^|x|)) x`: polynomial-time by
`Complexity.polyTimeComputable_unary`, composition, and
`Complexity.PolyTimeComputable.pairEncode` (`ClassNP/PolyTimePairing.lean`); correct by
`mem_language_iff_pairEncode_mem_CVAL`. -/
theorem IsPUniform.polyTimeReducible_CVAL {C : DAGCircuitFamily} (hU : C.IsPUniform)
    (hF : C.HasFaninTwo) : PolyTimeReducible C.language CVAL := by
  obtain ⟨f, hf, hC⟩ := hU
  refine ⟨fun x => pairEncode (f (List.replicate x.length true)) x,
    (hf.comp polyTimeComputable_unary).pairEncode polyTimeComputable_id,
    fun x => ?_⟩
  dsimp only
  rw [hC]
  exact mem_language_iff_pairEncode_mem_CVAL C hF x

/-- The language of a P-uniform fan-in-two family is in `P` (`Language.mem_P_of_isPUniform`
for the family's own language). [AB09, Thm 6.13, "if" direction] -/
theorem IsPUniform.language_mem_P {C : DAGCircuitFamily} (hU : C.IsPUniform)
    (hF : C.HasFaninTwo) : C.language ∈ Complexity.P :=
  mem_P_of_polyTimeReducible (hU.polyTimeReducible_CVAL hF) CVAL_mem_P

end DAGCircuitFamily

end BoolCircuit

/-- **Languages with P-uniform circuits are in P** [AB09, Thm 6.13, "if" direction]: if
`L` is decided by a P-uniform family of fan-in-two circuits, then `L ∈ P`.

Divergences: the converse direction of Thm 6.13 (every `L ∈ P` has P-uniform circuits)
is `Language.exists_isPUniform_of_mem_P` (`CircuitComplexity/UniformTableau.lean`); fan-in
two, part of [AB09, Def 6.1], is the explicit hypothesis `hF` in this circuit model.

**Proof sketch** ([AB09, p. 111–112]). On input `x`, compute `1^|x|`, run the uniformity
machine on it to obtain the description of `C_|x|`, and evaluate that circuit on `x`.
Formally: `x ↦ ⟨C_|x|, x⟩` is a polynomial-time Karp reduction from `L` to the
circuit-value language `CVAL`
(`BoolCircuit.DAGCircuitFamily.IsPUniform.polyTimeReducible_CVAL`), `CVAL ∈ P`
(`BoolCircuit.CVAL_mem_P`), and `P` is closed under Karp reductions
(`Complexity.mem_P_of_polyTimeReducible`). -/
theorem Language.mem_P_of_isPUniform {L : Language Bool} (C : BoolCircuit.DAGCircuitFamily)
    (hU : C.IsPUniform) (hF : C.HasFaninTwo) (hL : C.language = L) : L ∈ Complexity.P :=
  hL ▸ hU.language_mem_P hF
