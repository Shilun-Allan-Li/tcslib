/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding transfers space bounds down

Padding a language by a polynomial number of ones lowers the space it needs, measured in the
padded length: if `L ∈ SPACE S`, the language of its members padded by `C · (|x| + 1)^d` ones,
`padLang L (fun n => C * (n + 1) ^ d)`, lies in `SPACE T` for every `T` that is at least linear
and dominates `S` at the padded length. This is the space form of the padding argument
[AB09, Exercise 3.2] calls for; `Complexity.SPACE_linear_ne_NP` uses it at `S n = n² + 1`,
`T n = n + 1` and the pad `(|x| + 1)²`.

## Main definitions

* `Complexity.padLang` — the members `x` of `L`, each padded by `pad |x|` ones:
  `pairEncode x 1^{pad |x|}`.

## Main results

* `Complexity.mem_padLang_iff` — `padLang`'s defining formula.
* `Complexity.mem_SPACE_padLang` — the padded language is in `SPACE T`. (Statement; its proof is
  a fill.)

## Implementation notes

The pad is a unary block after `pairEncode`, so a member's first component and its length are
recovered from the padded word (`Turing.length_pairEncode`). The lower bound `m + 1 ≤ T m` pays
for checking that the input is a padded word at all, and for the copy of its first component;
`S n ≤ T (2n + 2 + C (n + 1)^d)` pays for deciding `L` on that component.

## References

* [AB09] S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009.
-/

namespace Complexity

open Turing

/-- **The padded language**: the members `x` of `L`, each followed by `pad |x|` ones, as the
pair `pairEncode x 1^{pad |x|}`. [AB09, Exercise 3.2] -/
def padLang (L : Language Bool) (pad : ℕ → ℕ) : Language Bool :=
  {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}

/-- **Membership in `padLang`, unfolded**: `y ∈ padLang L pad` exactly when `y` is a member `x`
of `L` paired with `pad |x|` ones. -/
theorem mem_padLang_iff {L : Language Bool} {pad : ℕ → ℕ} {y : List Bool} :
    y ∈ padLang L pad ↔ ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true) :=
  Iff.rfl

/-- **Padding transfers space bounds down** ([AB09, Exercise 3.2], the padding argument in space
form): if `L ∈ SPACE S`, then the language of `L`'s members padded by `C · (|x| + 1)^d` ones lies
in `SPACE T` for every `T` with `m + 1 ≤ T m` (room to validate the padding and to copy the first
component) and `S n ≤ T (2n + 2 + C (n + 1)^d)` (room for `L`'s decider, at the padded length
`|pairEncode x 1^{C (|x|+1)^d}| = 2|x| + 2 + C (|x| + 1)^d`).

**Proof sketch.** Let `M` decide `L` within `c · S` cells. On input `y`, first check that `y` is a
pair `pairEncode x w` whose second component `w` consists of exactly `C (|x| + 1)^d` ones;
reject otherwise. That needs `O(|y|)` cells. Then run `M` on `x` (copied to a work tape, or read
in place through a bounded input device) and answer as `M` does, within `c · S |x|` cells. For a
validated `y`, `|y| = 2|x| + 2 + C (|x| + 1)^d`, so both phases fit in `O(T |y|)`. -/
theorem mem_SPACE_padLang {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => C * (n + 1) ^ d) ∈ SPACE T := by
  sorry

end Complexity
