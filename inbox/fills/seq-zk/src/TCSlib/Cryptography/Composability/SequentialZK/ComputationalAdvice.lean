/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Advice
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One negligible bound for all bounded advice and arbitrary witnesses

## Main definitions

This module introduces no definitions.

## Main results

* `exists_uniform_negligible_bound` selects finite advice pointwise before requesting its
  negligible bound, then obtains a uniform bound for every valid advice and witness.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (the nonuniform hybrid reduction for sequential zero knowledge).
-/

namespace TCSlib.Cryptography.SequentialZK

/-- Let `A n` be finite nonempty metadata types, `W` an arbitrary witness type, and
`gap n a w ≤ 1`. Suppose every choice `choice : ∀ n, A n` has one negligible `ε` bounding
`gap n (choice n) w` for all valid witnesses and all `n`. Then one negligible `ε` satisfies
`gap n a w ≤ |ε n|` for every `n,a,w` with `valid n a w`.
Neither the metadata choice nor its negligible bound encodes a witness.
[PS10, Theorem 175.1, advice selection before the negligible bound].

**Proof sketch.** Gate the gap by validity, assigning zero to invalid pairs. At every
length apply the bounded-family selector to this gated family and choose its finite
metadata value. Request the negligible bound for that single metadata function. Its
absolute value bounds every gated value at the selected metadata, including invalid
pairs. The selector then bounds every gated value at that length, hence every valid gap.
The argument uses no witness-length bound and no attained witness maximum. -/
theorem exists_uniform_negligible_bound {A : ℕ → Type*} {W : Type*}
    [∀ n, Finite (A n)] [∀ n, Nonempty (A n)]
    (gap : (n : ℕ) → A n → W → ℝ) (valid : (n : ℕ) → A n → W → Prop)
    (hgap : ∀ n a w, gap n a w ≤ 1)
    (hchoice : ∀ choice : (n : ℕ) → A n, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n w, valid n (choice n) w → gap n (choice n) w ≤ ε n) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n a w, valid n a w → gap n a w ≤ |ε n| := by
  classical
  let g (n : ℕ) (a : A n) (w : W) : ℝ := if valid n a w then gap n a w else 0
  have hbounded (n : ℕ) (a : A n) (w : W) : g n a w ≤ 1 := by
    dsimp only [g]
    split_ifs
    · exact hgap n a w
    · exact zero_le_one
  have hselector (n : ℕ) :=
    Composability.exists_uniform_bound_selector (g n) 1 zero_le_one (hbounded n)
  choose choice hselect using hselector
  obtain ⟨ε, hε, hselected⟩ := hchoice choice
  refine ⟨ε, hε, ?_⟩
  intro n a w hvalid
  have hchosen (v : W) : g n (choice n) v ≤ |ε n| := by
    by_cases hv : valid n (choice n) v
    · exact (show g n (choice n) v = gap n (choice n) v from if_pos hv).le.trans
        ((hselected n v hv).trans (le_abs_self _))
    · exact (show g n (choice n) v = 0 from if_neg hv).le.trans (abs_nonneg _)
  have hall := hselect n (|ε n|) (abs_nonneg _) hchosen a w
  simpa only [g, if_pos hvalid] using hall

end TCSlib.Cryptography.SequentialZK
