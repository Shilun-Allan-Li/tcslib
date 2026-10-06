/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.PolyHierarchy.Defs
import TCSlib.Complexity.PolyHierarchy.Padding
import TCSlib.Complexity.PolyHierarchy.Normalize
import TCSlib.Complexity.PolyHierarchy.Levels
import TCSlib.Complexity.PolyHierarchy.Collapse

/-!
# The polynomial hierarchy

The classes `Σᵢᵖ`, `Πᵢᵖ` and `PH` of [AB09, §5.2, Definition 5.3] in the campaign's
machine framework (verifiers in `Complexity.P`, certificate blocks of exact explicit
polynomial length, tuples built with `Turing.pairEncode`), the structure of the levels,
and the collapse theorem [AB09, Theorem 5.4].

## Contents

- `PolyHierarchy.Defs`: `altQuant` (alternating quantifier prefix), `SigmaP`, `PiP`, `PH`;
  `Σ₀ᵖ = Π₀ᵖ = P`; the `∀`-first form of `Πᵢᵖ`.
- `PolyHierarchy.Padding`: polynomial-time toolkit — pair projections, `P` closed under
  preimages, branching, length tests, total surjective certificate un-padding, block-wise
  tuple decoding, unary length functions.
- `PolyHierarchy.Normalize`: quantifier prefixes with polynomial (non-normal-form) block
  lengths and transformed verifier input still define the class; closure under
  polynomial-time preimages.
- `PolyHierarchy.Levels`: `Σ₁ᵖ = NP`, `Π₁ᵖ = coNP`, `Σᵢ₊₁ᵖ = ∃·Πᵢᵖ`, `Πᵢ₊₁ᵖ = ∀·Σᵢᵖ`,
  merging an outer `∃` block, `Σᵢᵖ ∪ Πᵢᵖ ⊆ Σᵢ₊₁ᵖ ∩ Πᵢ₊₁ᵖ`, `P ⊆ Σᵢᵖ`, `PH` membership.
- `PolyHierarchy.Collapse`: [AB09, Theorem 5.4] (`Σᵢᵖ = Πᵢᵖ ⇒ PH = Σᵢᵖ`;
  `P = NP ⇒ PH = P`) and the `Σ₂ᵖ = ∃·coNP`, `Π₂ᵖ = ∀·NP` characterizations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§5.2.)
-/
