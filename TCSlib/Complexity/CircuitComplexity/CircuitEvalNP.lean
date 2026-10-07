/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSatLang
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CKT-SAT is in NP

[AB09, p. 111]: "CKT-SAT is clearly in NP" — a satisfying assignment is a certificate,
checked by evaluating the circuit. This file proves it for the string language
`BoolCircuit.dagCktSatLang` of `DAGCircuitSatLang.lean` (descriptions
`BoolCircuit.DAGCircuit.encode` of satisfiable fan-in-two circuits of the book's model),
in the campaign's class `Complexity.NP`, from `BoolCircuit.CVALPrefix_mem_P`.

## Main results

* `BoolCircuit.dagCktSatLang_mem_NP` — CKT-SAT is in `NP`. [AB09, p. 111]

## Divergences from [AB09]

* **Certificates are paired, of bounded length.** We use the bounded-length paired
  characterization `Complexity.mem_NP_iff_exists_length_le` ([AB09, Exercise 2.1]):
  the certificate is the satisfying assignment `u ∈ {0,1}ⁿ` itself, of length
  `n ≤ |w|` (`n` is at most the size of the circuit, hence at most the length of its
  description, `DAGCircuit.size_le_length_encode`), and the verifier is the
  circuit-value language on a prefix of the input, `BoolCircuit.CVALPrefix`, applied to
  `Turing.pairEncode w u`.

## Length

Kept apart from `CircuitEval` (rather than folded into it) so that the `CVAL ∈ P` layer does
not import the CKT-SAT / `SAT` development pulled in by `DAGCircuitSatLang`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.1.2, Definition 6.9, p. 111; Exercise 2.1.)
-/

namespace BoolCircuit

open Turing Complexity

/-- **CKT-SAT is in NP** [AB09, p. 111]: the certificate is a satisfying assignment,
and the verifier evaluates the circuit on it.

**Proof sketch.** By the bounded-length paired form of `NP`
(`Complexity.mem_NP_iff_exists_length_le`) with bound `1 · (|w| + 1)¹` and verifier
`CVALPrefix ∈ P`. Forward: a satisfying assignment `a ∈ {0,1}ⁿ` of the described
circuit has length `n ≤ size ≤ |w|`, and `pairEncode w (ofFn a) ∈ CVALPrefix`. Backward:
`pairEncode w u ∈ CVALPrefix` gives a fan-in-two circuit described by `w` (the pairing
is injective) that outputs `1` on the first `n` bits of `u`, a satisfying input. -/
theorem dagCktSatLang_mem_NP : dagCktSatLang ∈ NP := by
  refine mem_NP_iff_exists_length_le.mpr ⟨1, 1, CVALPrefix, CVALPrefix_mem_P, fun w => ?_⟩
  constructor
  · rintro ⟨⟨n, C⟩, ⟨hfan, a, ha⟩, rfl⟩
    have := C.size_le_length_encode
    simp only [DAGCircuit.size] at this
    refine ⟨List.ofFn a, by simp; omega, List.ofFn a, n, C, hfan, by simp, ?_, rfl⟩
    have : (fun i : Fin n => (List.ofFn a).getD i false) = a := by
      funext i; simp [List.getD_eq_getElem?_getD]
    rw [this]; exact ha
  · rintro ⟨u, -, x, n, C, hfan, -, hev, heq⟩
    have hinj := @pairEncode_injective (w, u) (C.encode, x) heq
    simp only [Prod.mk.injEq] at hinj
    exact ⟨⟨n, C⟩, ⟨hfan, _, hev⟩, hinj.1.symm⟩

end BoolCircuit
