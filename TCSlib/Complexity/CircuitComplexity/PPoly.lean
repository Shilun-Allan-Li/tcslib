/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit

/-!
# `SIZE(T)` and `P/poly`

The circuit size classes of [AB09, Defs 6.2 and 6.5], over the book's circuit model
`BoolCircuit.DAGCircuit`: fan-in-two DAGs whose size counts every vertex, inputs included.

## Main definitions

* `Language.InSIZE` — [AB09, Def 6.2].
* `Language.InPPoly` — [AB09, Def 6.5], `P/poly = ⋃_c SIZE(n^c)`.
* `BoolCircuit.PPoly` — the same class as a `Set (Language Bool)`.

## Main results

* `Language.InSIZE.mono`, `Language.InSIZE.inPPoly` — monotonicity, and polynomial
  `SIZE` classes lie in `P/poly`.
* `Language.inPPoly_iff` — `P/poly` membership as one family carrying its own size bound.

The same class over the layered model of the Razborov–Smolensky development is
`Language.InLayeredPPoly`; `LayeredDAG.lean` proves the two coincide.

## Divergences from [AB09, Defs 6.2 and 6.5]

* The model's own divergences (fan-in at most two rather than exactly two, constants via
  fan-in-zero gates, a single output) are listed in `DAGCircuit.lean`.
* [AB09] writes `P/poly = ⋃_c SIZE(n^c)`; we write `∃ a k, SIZE(a * (n + 1) ^ k)`.  Since a
  circuit has at least one vertex, `n ^ c` would force `|C_0| ≤ 0`, so the literal form
  excludes every language at length `0`; `a * (n + 1) ^ k` repairs that and is otherwise
  the same union.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definitions 6.2 and 6.5.)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- `L ∈ SIZE(T)`: some fan-in-two circuit family decides `L` with the length-`n` circuit
of size at most `T n`.  [AB09, Def 6.2] -/
def Language.InSIZE (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.DAGCircuitFamily,
    C.HasFaninTwo ∧ (∀ n, (C.circuit n).size ≤ T n) ∧ C.language = L

/-- `L ∈ P/poly`: some polynomial-size fan-in-two circuit family decides `L`.
[AB09, Def 6.5] -/
def Language.InPPoly (L : Language Bool) : Prop :=
  ∃ a k : ℕ, L.InSIZE (fun n => a * (n + 1) ^ k)

/-- `SIZE(T) ⊆ SIZE(T')` whenever `T ≤ T'` pointwise. -/
theorem Language.InSIZE.mono {T T' : ℕ → ℕ} {L : Language Bool} (hL : L.InSIZE T)
    (h : ∀ n, T n ≤ T' n) : L.InSIZE T' := by
  obtain ⟨C, hG, hS, hC⟩ := hL
  exact ⟨C, hG, fun n => (hS n).trans (h n), hC⟩

/-- A language in `SIZE(T)` for a polynomially bounded `T` is in `P/poly`. -/
theorem Language.InSIZE.inPPoly {T : ℕ → ℕ} {L : Language Bool} {a k : ℕ}
    (hL : L.InSIZE T) (hT : ∀ n, T n ≤ a * (n + 1) ^ k) : L.InPPoly :=
  ⟨a, k, hL.mono hT⟩

/-- `P/poly` membership as one family carrying its own size bound. -/
theorem Language.inPPoly_iff (L : Language Bool) :
    L.InPPoly ↔ ∃ C : BoolCircuit.DAGCircuitFamily,
      C.HasFaninTwo ∧ C.IsPolySize ∧ C.language = L := by
  constructor
  · rintro ⟨a, k, C, hG, hS, hL⟩
    exact ⟨C, hG, ⟨a, k, hS⟩, hL⟩
  · rintro ⟨C, hG, ⟨a, k, hS⟩, hL⟩
    exact ⟨a, k, C, hG, hS, hL⟩

namespace BoolCircuit

/-- `P/poly` as a set of languages.  [AB09, Def 6.5] -/
def PPoly : Set (Language Bool) :=
  {L | L.InPPoly}

/-- Set membership in `PPoly` agrees with the predicate `Language.InPPoly`. -/
@[simp]
theorem mem_PPoly_iff (L : Language Bool) : L ∈ PPoly ↔ L.InPPoly :=
  Iff.rfl

end BoolCircuit
