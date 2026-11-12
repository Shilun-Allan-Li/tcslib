/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace-uniform circuit families

[AB09, §6.2.1, Def 6.14]: a circuit family `{Cₙ}` is *logspace-uniform* if some implicitly
logspace computable function [AB09, Def 4.16] maps `1ⁿ` to the description of `Cₙ`.
"Since logspace computations run in polynomial time, logspace-uniform circuits are also
P-uniform" [AB09, p. 112].

## Main definitions

* `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform` — [AB09, Def 6.14].

## Main results

* `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPUniform` — logspace-uniform families are
  P-uniform. [AB09, p. 112]
* `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPolySize` — and so have polynomial size.

## Design and divergences from [AB09]

* **The description** is the binary encoding `BoolCircuit.DAGCircuit.encode` of
  `TCSlib.Complexity.CircuitComplexity.Uniform` (the same one P-uniformity uses), so the two
  notions are directly comparable. [AB09] leaves the description unspecified and remarks
  that Def 6.14 is robust to the choice; the adjacency-matrix characterization is in
  `TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdj`.
* **Implicit logspace computability** is `Complexity.ImplicitlyLogspaceComputable`, with the
  conventions recorded there (pairs via `Turing.pairEncode`, `0`-based binary indices, the
  `(n + 1)^c` polynomial bound).
* **Only `1ⁿ` is constrained**: the function's values on other strings are arbitrary, as in
  `BoolCircuit.DAGCircuitFamily.IsPUniform`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16; §6.2.1, Definition 6.14.)
-/

namespace BoolCircuit

namespace DAGCircuitFamily

open Complexity

/-- **Logspace-uniform circuit families** [AB09, Def 6.14]: an implicitly logspace
computable function (`Complexity.ImplicitlyLogspaceComputable`, [AB09, Def 4.16]) maps `1ⁿ`
to the description `BoolCircuit.DAGCircuit.encode` of the `n`-th circuit. -/
def IsLogspaceUniform (C : DAGCircuitFamily) : Prop :=
  ∃ f : List Bool → List Bool, ImplicitlyLogspaceComputable f ∧
    ∀ n, f (List.replicate n true) = (C.circuit n).encode

/-- **Logspace-uniform families are P-uniform** [AB09, p. 112: "Since logspace computations
run in polynomial time, logspace-uniform circuits are also P-uniform"].

**Proof sketch.** The same function works: implicitly logspace computable functions are
polynomial-time computable (`Complexity.ImplicitlyLogspaceComputable.polyTimeComputable`:
the enumeration of the output bits runs in logarithmic space, hence, by configuration
counting, in polynomial time). -/
theorem IsLogspaceUniform.isPUniform {C : DAGCircuitFamily} (h : C.IsLogspaceUniform) :
    C.IsPUniform := by
  obtain ⟨f, hf, hC⟩ := h
  exact ⟨f, hf.polyTimeComputable, hC⟩

/-- A logspace-uniform family has polynomial size. -/
theorem IsLogspaceUniform.isPolySize {C : DAGCircuitFamily} (h : C.IsLogspaceUniform) :
    C.IsPolySize :=
  h.isPUniform.isPolySize

end DAGCircuitFamily

end BoolCircuit
