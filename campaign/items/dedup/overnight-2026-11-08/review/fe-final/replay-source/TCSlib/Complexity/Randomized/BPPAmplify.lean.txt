/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.PTMEquiv
import TCSlib.Complexity.Randomized.Reductions
import Mathlib.Algebra.Order.Archimedean.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lemma 7.9 and error reduction for BPP, for polynomial-time PTMs

[AB09, Lemma 7.9] (`BPP_{1/2+n^{-c}} = BPP`) and [AB09, Theorem 7.10] (error reduction for
`BPP`) are stated in the book for polynomial-time PTMs. `Randomized.inBPPWeak_iff_inBPP` and
`Randomized.bpp_error_reduction` prove them for an abstract verifier model closed under
majority repetition. Here they are instantiated at `polyTimeModel` and transferred to the PTM
classes of [AB09, Def 7.2] through `Randomized.mem_BPP_PTMWith_iff`, the threshold-`p` form
of the equivalence `Randomized.mem_BPP_PTM_iff` (both in `Randomized.PTMEquiv`, with the
threshold classes `Randomized.BPP_PTMWith` and `Randomized.InBPPWith`).

## Main results

* `Randomized.bpp_error_reduction_polyTime`, `Randomized.inBPPWeak_polyTimeModel_iff_inBPP` —
  [AB09, Theorem 7.10] and [AB09, Lemma 7.9] over polynomial-time verifiers.
* `Randomized.BPP_PTMWith_error_reduction` — [AB09, Theorem 7.10], PTM form.
* `Randomized.BPP_PTMWith_weakAdv_eq_BPP_PTM` — [AB09, Lemma 7.9], PTM form.
* `Randomized.BPP_PTMWith_const_eq_BPP_PTM` — any constant threshold in `(1/2, 1)` gives `BPP`
  [AB09, p. 132].

## Divergences

* The printed threshold `1/2 + |x|^{-c}` exceeds `1` at `|x| = 1` and is undefined at
  `|x| = 0`, so the printed class `BPP_{1/2+n^{-c}}` is empty as written. We use
  `1/2 + weakAdv c n` with `weakAdv c n = min (1/6) ((n+1)^{-c}) ≤ n^{-c}` (for `n ≥ 1`), the
  convention of `Randomized.InBPPWeak`: the hypothesis is weaker than the book's wherever the
  book's is meaningful. On the empty input, where the book's bound is undefined, we demand
  advantage `weakAdv c 0 = 1/6`.
* The book's exponent is a real `c > 0`; ours is `c : ℕ`. The book's hypothesis for `c`
  implies ours for `⌈c⌉`, since `n^{-c} ≥ n^{-⌈c⌉}` for `n ≥ 1`.
* Theorem 7.10 concludes success `1 − 2^{-((|x|+1)^d+1)} ≥ 1 − 2^{-|x|^d}`, the
  `Randomized.InBPPStrong` convention.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity Turing

/-! ### Threshold-`p` classes -/

/-- Lowering the threshold enlarges the class. -/
theorem BPP_PTMWith_mono {p q : ℕ → ℚ} (h : ∀ n, q n ≤ p n) :
    BPP_PTMWith p ⊆ BPP_PTMWith q := by
  intro L hL
  obtain ⟨e, K, N, hN⟩ := Set.mem_iUnion.mp hL
  exact Set.mem_iUnion.mpr ⟨e, K, N, fun x => ⟨(hN x).1, (h _).trans (hN x).2⟩⟩

/-- `InBPPWeak polyTimeModel c` is the threshold `1/2 + weakAdv c n`. -/
theorem inBPPWith_iff_inBPPWeak (c : ℕ) (L : Language Bool) :
    InBPPWith (fun n => 1/2 + weakAdv c n) L ↔ InBPPWeak polyTimeModel c L := Iff.rfl

/-- `InBPPStrong polyTimeModel d` is the threshold `1 − 2^{-((n+1)^d+1)}`. -/
theorem inBPPWith_iff_inBPPStrong (d : ℕ) (L : Language Bool) :
    InBPPWith (fun n => 1 - (1/2 : ℚ) ^ ((n + 1) ^ d + 1)) L ↔
      InBPPStrong polyTimeModel d L := Iff.rfl

/-! ### Lemma 7.9 and Theorem 7.10 over polynomial-time verifiers -/

/-- **Error reduction for `BPP`** ([AB09, Theorem 7.10]) over polynomial-time verifiers. -/
theorem bpp_error_reduction_polyTime {c : ℕ} {L : Language Bool}
    (hL : InBPPWeak polyTimeModel c L) (d : ℕ) : InBPPStrong polyTimeModel d L :=
  bpp_error_reduction polyTimeModel polyTimeModel_closedUnderMajority hL d

/-- **`BPP_{1/2+n^{-c}} = BPP`** ([AB09, Lemma 7.9]) over polynomial-time verifiers. -/
theorem inBPPWeak_polyTimeModel_iff_inBPP (c : ℕ) (L : Language Bool) :
    InBPPWeak polyTimeModel c L ↔ InBPP polyTimeModel L :=
  inBPPWeak_iff_inBPP polyTimeModel polyTimeModel_closedUnderMajority c L

/-! ### PTM forms -/

/-- **Error reduction for `BPP`** (PTM form, [AB09, Theorem 7.10]): a polynomial-time PTM
with `Pr[N(x) = L(x)] ≥ 1/2 + weakAdv c |x|` yields one with
`Pr[N'(x) = L(x)] ≥ 1 − 2^{-((|x|+1)^d+1)}`, for every `d`. -/
theorem BPP_PTMWith_error_reduction (c d : ℕ) :
    BPP_PTMWith (fun n => 1/2 + weakAdv c n) ⊆
      BPP_PTMWith fun n => 1 - (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := fun L h =>
  (mem_BPP_PTMWith_iff _ L).mpr
    (bpp_error_reduction_polyTime ((mem_BPP_PTMWith_iff _ L).mp h) d)

/-- **`BPP_{1/2+n^{-c}} = BPP`** (PTM form, [AB09, Lemma 7.9]): success probability
`1/2 + weakAdv c |x|` for a polynomial-time PTM already gives `BPP`. -/
theorem BPP_PTMWith_weakAdv_eq_BPP_PTM (c : ℕ) :
    BPP_PTMWith (fun n => 1/2 + weakAdv c n) = BPP_PTM :=
  Set.ext fun L => (mem_BPP_PTMWith_iff _ L).trans
    ((inBPPWeak_polyTimeModel_iff_inBPP c L).trans (mem_BPP_PTM_iff L).symm)

/-- A constant number of majority votes suffices for any target error `η > 0` from any
advantage `0 < ε ≤ 1/2`. -/
private theorem exists_majority_count {ε η : ℚ} (hε : 0 < ε) (hε' : ε ≤ 1/2) (hη : 0 < η) :
    ∃ K : ℕ, 2 * (1 - 4 * ε ^ 2) ^ (K / 2) ≤ η := by
  have h0 : 0 ≤ 1 - 4 * ε ^ 2 := by nlinarith
  have h1 : 1 - 4 * ε ^ 2 < 1 := by nlinarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hη) h1
  refine ⟨2 * n, ?_⟩
  rw [Nat.mul_div_cancel_left n two_pos]
  linarith

/-- **Any constant threshold in `(1/2, 1)` gives `BPP`** (PTM form). [AB09, p. 132: "we can
replace `2/3` with any constant larger than `1/2`"]

**Proof sketch.** `InBPPWith (fun _ => ρ)` is `InBPPAt polyTimeModel ρ`; a constant number of
majority votes (`InBPPAt.amplify`, `exists_majority_count`) moves between success `ρ` and
success `2/3` in either direction. -/
theorem BPP_PTMWith_const_eq_BPP_PTM {ρ : ℚ} (h1 : 1/2 < ρ) (h2 : ρ < 1) :
    BPP_PTMWith (fun _ => ρ) = BPP_PTM := by
  refine Set.ext fun L => (mem_BPP_PTMWith_iff _ L).trans (Iff.trans ?_ (mem_BPP_PTM_iff L).symm)
  show InBPPAt polyTimeModel ρ L ↔ InBPPAt polyTimeModel (2/3) L
  constructor
  · intro h
    have hε : 0 < ρ - 1/2 := by linarith
    obtain ⟨K, hK⟩ := exists_majority_count hε (by linarith) (by norm_num : (0 : ℚ) < 1/3)
    have h' : InBPPAt polyTimeModel (1/2 + (ρ - 1/2)) L := h.mono (by linarith)
    exact (h'.amplify polyTimeModel_closedUnderMajority K hε.le hK).mono (by norm_num)
  · intro h
    obtain ⟨K, hK⟩ := exists_majority_count (ε := 1/6) (by norm_num) (by norm_num)
      (by linarith : 0 < 1 - ρ)
    have h' : InBPPAt polyTimeModel (1/2 + 1/6) L := h.mono (by norm_num)
    exact (h'.amplify polyTimeModel_closedUnderMajority K (by norm_num) hK).mono (by linarith)

end Randomized
