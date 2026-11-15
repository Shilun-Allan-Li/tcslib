/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hybrid bounds from conditional continuation gaps

## Main definitions

This module introduces no definitions.

## Main results

* `hybrid_recursion_gap_le` bounds the difference between the final real execution's
  expected continuation potential and the initial potential by the number of phase updates
  times their uniform conditional gap bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of zero knowledge).
-/

namespace TCSlib.Cryptography.SequentialZK

/-- Let `realFamily` start at `initial` and satisfy its displayed `Fin.snoc` equation for
`realStep`. For a real-valued continuation potential `C`, suppose `0 ≤ ε` and each actual
real prefix at `i<q` satisfies
`|E_a[C (i+1) (realStep i (realFamily i r) a)] - C i (realFamily i r)| ≤ ε`.
Then `|E_r[C q (realFamily q r)] - C 0 initial| ≤ q*ε`.
The state type is arbitrary; no finite witness or state-space assumption is required.
[PS10, Theorem 175.1, conditional hybrid argument].

**Proof sketch.** For each phase count, average the continuation potential over the real
prefix's independent coins. The snoc equivalence and uniform-product averaging identify
the next average with the average of its conditional next-step expectations. Averaging
the supplied local bounds therefore bounds each adjacent difference by `ε`. Apply the
published telescoping hybrid inequality and bound its `q` summands by `ε`. -/
theorem hybrid_recursion_gap_le {A State : Type*} [Fintype A] [Nonempty A]
    (realFamily : (i : ℕ) → (Fin i → A) → State) (initial : State)
    (realStep : ℕ → State → A → State)
    (real_zero : ∀ r, realFamily 0 r = initial)
    (real_snoc : ∀ i r a, realFamily (i + 1) (Fin.snoc r a) =
      realStep i (realFamily i r) a)
    (C : ℕ → State → ℝ) (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ i < q, ∀ r : Fin i → A,
      |uexp (fun a => C (i + 1) (realStep i (realFamily i r) a)) -
        C i (realFamily i r)| ≤ ε) :
    |uexp (fun r : Fin q → A => C q (realFamily q r)) - C 0 initial| ≤
      (q : ℝ) * ε := by
  -- Average the continuation potential over each real prefix coin table.
  let P : ℕ → ℝ := fun i => uexp (fun r : Fin i → A => C i (realFamily i r))
  have hzero : P 0 = C 0 initial := by
    simp only [P, real_zero, HardcoreBit.uexp_const]
  -- Reindex the next table as a prefix and fresh coin, then average the local gap.
  have hgap (i : ℕ) (hi : i < q) : |P i - P (i + 1)| ≤ ε := by
    let e : (Fin (i + 1) → A) ≃ (Fin i → A) × A :=
      (Fin.snocEquiv (fun _ : Fin (i + 1) => A)).symm.trans
        (Equiv.prodComm A (Fin i → A))
    have hfamily (r : Fin (i + 1) → A) :
        realFamily (i + 1) r = realStep i (realFamily i (e r).1) (e r).2 := by
      change realFamily (i + 1) r =
        realStep i (realFamily i (Fin.init r)) (r (Fin.last i))
      simpa only [Fin.snoc_init_self] using real_snoc i (Fin.init r) (r (Fin.last i))
    have hnext : P (i + 1) = uexp (fun r : Fin i → A =>
        uexp (fun a => C (i + 1) (realStep i (realFamily i r) a))) := by
      have hpoint : (fun r : Fin (i + 1) → A => C (i + 1) (realFamily (i + 1) r)) =
          (fun r => C (i + 1) (realStep i (realFamily i (e r).1) (e r).2)) :=
        funext fun r => congrArg (C (i + 1)) (hfamily r)
      change uexp (fun r : Fin (i + 1) → A => C (i + 1) (realFamily (i + 1) r)) = _
      rw [hpoint, HardcoreBit.uexp_comp_equiv e
        (fun z : (Fin i → A) × A => C (i + 1) (realStep i (realFamily i z.1) z.2)),
        HardcoreBit.uexp_prod]
    rw [hnext, abs_sub_comm]
    exact abs_uexp_sub_le hε (fun r => hlocal i hi r)
  -- Apply the published telescope and bound each adjacent gap by the same error.
  have hsum : ∑ i ∈ Finset.range q, |P i - P (i + 1)| ≤ (q : ℝ) * ε := by
    calc
      _ ≤ ∑ _i ∈ Finset.range q, ε :=
        Finset.sum_le_sum fun i hi => hgap i (Finset.mem_range.mp hi)
      _ = (q : ℝ) * ε := by simp
  have hbound := (abs_sub_le_sum_hybrids P q).trans hsum
  rw [hzero, abs_sub_comm] at hbound
  exact hbound

end TCSlib.Cryptography.SequentialZK
