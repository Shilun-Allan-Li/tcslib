/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra.RootCube

/-!
# Splitting a multilinear polynomial at half degree

On `{1, ω}^n`, a squarefree polynomial is its low-degree part plus the top
monomial times a low-degree polynomial in the affine coordinates
`x ↦ 1 + ω⁻¹ - ω⁻¹ x`.

## Main definitions

* `RazborovSmolensky.affineInvPoly` — the affine coordinate transform as a polynomial.
* `RazborovSmolensky.affineSquarefreeMonomial` — a squarefree monomial after that
  substitution.

## Main results

* `RazborovSmolensky.split_multilinear_at_half_degree`,
  `RazborovSmolensky.split_multilinear_at_half_degree_direct` — the split.
-/

open Finset
open scoped BigOperators

namespace RazborovSmolensky

open BoolCircuit

variable (p : ℕ) [Fact (Nat.Prime p)]

section ModqRoadmap

variable {K : Type*} [Field K]
variable (ω : K)

/-- Split a squarefree multilinear polynomial at degree `n / 2` by factoring
out the top monomial on the high-degree monomials and rewriting complement
variables as `x⁻¹ = 1 + ω⁻¹ - ω⁻¹ x` on `{1, ω}`.

This is the precise version of the slide's split after the preceding
multilinearization step has already expressed the function as
`∑_S c_S ∏_{i∈S} x_i`. -/
theorem split_multilinear_at_half_degree
    {n : ℕ} (hω0 : ω ≠ 0)
    (c : Finset (Fin n) → K) :
    ∃ P₁ P₂ : MvPolynomial (Fin n) K,
      P₁.totalDegree ≤ n / 2 ∧
      P₂.totalDegree ≤ n / 2 ∧
      ∀ x : rootCube ω n,
        (squarefreePolynomial (K := K) c).eval x.1 =
          P₁.eval x.1 +
            (∏ i, x.1 i) *
              P₂.eval (fun i => 1 + ω⁻¹ - ω⁻¹ * x.1 i) := by
  classical
  let low : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun s : Finset (Fin n) => s.card ≤ n / 2)
  let high : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun s : Finset (Fin n) => ¬ s.card ≤ n / 2)
  let term : Finset (Fin n) → MvPolynomial (Fin n) K := fun s =>
    MvPolynomial.C (c s) * squarefreeMonomial (K := K) s
  let P₁ : MvPolynomial (Fin n) K := low.sum term
  let P₂ : MvPolynomial (Fin n) K :=
    high.sum (fun s : Finset (Fin n) =>
      MvPolynomial.C (c s) * squarefreeMonomial (K := K) (sᶜ))
  refine ⟨P₁, P₂, ?_, ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le (s := low) (f := term) ?_
    intro s hs
    have hs_card : s.card ≤ n / 2 := by
      simpa [low] using hs
    have hmono : (squarefreeMonomial (K := K) s).totalDegree ≤ s.card :=
      squarefreeMonomial_totalDegree_le_card (K := K) s
    calc
      (term s).totalDegree
          ≤ (MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree +
              (squarefreeMonomial (K := K) s).totalDegree := by
                simpa [term] using
                  (MvPolynomial.totalDegree_mul
                    (MvPolynomial.C (c s) : MvPolynomial (Fin n) K)
                    (squarefreeMonomial (K := K) s))
      _ ≤ 0 + s.card := by
                simpa using
                  (Nat.add_le_add_left hmono
                    ((MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree))
      _ ≤ n / 2 := by
                simpa using hs_card
  · refine MvPolynomial.totalDegree_finsetSum_le (s := high)
      (f := fun s : Finset (Fin n) =>
        MvPolynomial.C (c s) * squarefreeMonomial (K := K) (sᶜ)) ?_
    intro s hs
    have hs_high : ¬ s.card ≤ n / 2 := by
      simpa [high] using hs
    have hs_gt : n / 2 < s.card := Nat.lt_of_not_ge hs_high
    have hs_le_n : s.card ≤ n := by
      simpa using (Finset.card_le_univ (s := s))
    have hcompl_card : (sᶜ).card ≤ n / 2 := by
      have hcard : (sᶜ).card = n - s.card := by
        simpa [Fintype.card_fin] using (Finset.card_compl (s := s))
      omega
    have hmono : (squarefreeMonomial (K := K) (sᶜ)).totalDegree ≤ (sᶜ).card :=
      squarefreeMonomial_totalDegree_le_card (K := K) (sᶜ)
    calc
      (MvPolynomial.C (c s) * squarefreeMonomial (K := K) (sᶜ)).totalDegree
          ≤ (MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree +
              (squarefreeMonomial (K := K) (sᶜ)).totalDegree := by
                simpa using
                  (MvPolynomial.totalDegree_mul
                    (MvPolynomial.C (c s) : MvPolynomial (Fin n) K)
                    (squarefreeMonomial (K := K) (sᶜ)))
      _ ≤ 0 + (sᶜ).card := by
                simpa using
                  (Nat.add_le_add_left hmono
                    ((MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree))
      _ ≤ n / 2 := by
                simpa using hcompl_card
  · intro x
    let y : Fin n → K := fun i => 1 + ω⁻¹ - ω⁻¹ * x.1 i
    have hy : ∀ i : Fin n, y i = (x.1 i)⁻¹ := by
      intro i
      exact rootCube_affine_inverse (ω := ω) hω0 x i
    let highPoly : MvPolynomial (Fin n) K := high.sum term
    have hpartition : P₁ + highPoly = squarefreePolynomial (K := K) c := by
      have hsum :=
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Finset (Fin n))))
          (f := term)
          (p := fun s : Finset (Fin n) => s.card ≤ n / 2))
      simpa [P₁, highPoly, low, high, term, squarefreePolynomial] using hsum
    have hhigh_eval :
        highPoly.eval x.1 = (∏ i : Fin n, x.1 i) * P₂.eval y := by
      calc
        highPoly.eval x.1
            = high.sum (fun s : Finset (Fin n) =>
                c s * s.prod (fun i : Fin n => x.1 i)) := by
                  simp [highPoly, term, squarefreeMonomial]
        _ = high.sum (fun s : Finset (Fin n) =>
                (∏ i : Fin n, x.1 i) *
                  (c s * (sᶜ).prod (fun i : Fin n => y i))) := by
                  refine Finset.sum_congr rfl ?_
                  intro s hs
                  have hcomp :
                      (sᶜ).prod (fun i : Fin n => y i) =
                        (sᶜ).prod (fun i : Fin n => (x.1 i)⁻¹) := by
                    refine Finset.prod_congr rfl ?_
                    intro i hi
                    exact hy i
                  calc
                    c s * s.prod (fun i : Fin n => x.1 i)
                        = c s * ((∏ i : Fin n, x.1 i) *
                            (sᶜ).prod (fun i : Fin n => (x.1 i)⁻¹)) := by
                              rw [rootCube_top_mul_compl_inverse (ω := ω) hω0 x s]
                    _ = (∏ i : Fin n, x.1 i) *
                          (c s * (sᶜ).prod (fun i : Fin n => y i)) := by
                              rw [hcomp]
                              ring
        _ = (∏ i : Fin n, x.1 i) * P₂.eval y := by
                  simp [P₂, squarefreeMonomial, Finset.mul_sum]
    calc
      (squarefreePolynomial (K := K) c).eval x.1
          = (P₁ + highPoly).eval x.1 := by rw [hpartition]
      _ = P₁.eval x.1 + highPoly.eval x.1 := by simp
      _ = P₁.eval x.1 + (∏ i : Fin n, x.1 i) * P₂.eval y := by rw [hhigh_eval]


/-- The affine coordinate transform `x ↦ 1 + ω⁻¹ - ω⁻¹ x`, as an actual
polynomial.  On `{1,ω}` with `ω ≠ 0` this evaluates to `x⁻¹`. -/
noncomputable def affineInvPoly {n : ℕ} (i : Fin n) : MvPolynomial (Fin n) K :=
  MvPolynomial.C (1 + ω⁻¹) + MvPolynomial.C (-ω⁻¹) * MvPolynomial.X i

@[simp] theorem affineInvPoly_eval {n : ℕ} (i : Fin n) (x : Fin n → K) :
    (affineInvPoly (K := K) ω i).eval x = 1 + ω⁻¹ - ω⁻¹ * x i := by
  simp [affineInvPoly, sub_eq_add_neg, mul_comm]

/-- The affine inverse coordinate polynomial has degree at most one. -/
theorem affineInvPoly_totalDegree_le_one {n : ℕ} (i : Fin n) :
    (affineInvPoly (K := K) ω i).totalDegree ≤ 1 := by
  classical
  unfold affineInvPoly
  calc
    (MvPolynomial.C (1 + ω⁻¹) + MvPolynomial.C (-ω⁻¹) * MvPolynomial.X i :
        MvPolynomial (Fin n) K).totalDegree
        ≤ max (MvPolynomial.C (1 + ω⁻¹) : MvPolynomial (Fin n) K).totalDegree
            (MvPolynomial.C (-ω⁻¹) * MvPolynomial.X i : MvPolynomial (Fin n) K).totalDegree := by
              exact MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
          refine max_le ?_ ?_
          · have hconst :
                (1 + MvPolynomial.C ω⁻¹ : MvPolynomial (Fin n) K).totalDegree ≤ 1 := by
              calc
                (1 + MvPolynomial.C ω⁻¹ : MvPolynomial (Fin n) K).totalDegree
                    ≤ max (1 : MvPolynomial (Fin n) K).totalDegree
                        (MvPolynomial.C ω⁻¹ : MvPolynomial (Fin n) K).totalDegree := by
                          exact MvPolynomial.totalDegree_add _ _
                _ ≤ 1 := by simp
            simpa using hconst
          · calc
              (MvPolynomial.C (-ω⁻¹) * MvPolynomial.X i : MvPolynomial (Fin n) K).totalDegree
                  ≤ (MvPolynomial.C (-ω⁻¹) : MvPolynomial (Fin n) K).totalDegree +
                      (MvPolynomial.X i : MvPolynomial (Fin n) K).totalDegree := by
                        exact MvPolynomial.totalDegree_mul _ _
              _ ≤ 0 + 1 := by
                    simp
              _ = 1 := by simp

/-- Squarefree monomial after the affine inverse substitution. -/
noncomputable def affineSquarefreeMonomial {n : ℕ} (s : Finset (Fin n)) :
    MvPolynomial (Fin n) K :=
  s.prod (fun i : Fin n => affineInvPoly (K := K) ω i)

@[simp] theorem affineSquarefreeMonomial_eval {n : ℕ}
    (s : Finset (Fin n)) (x : Fin n → K) :
    (affineSquarefreeMonomial (K := K) ω s).eval x =
      s.prod (fun i : Fin n => 1 + ω⁻¹ - ω⁻¹ * x i) := by
  simp [affineSquarefreeMonomial]

/-- The affine-substituted squarefree monomial indexed by `s` still has degree
at most `s.card`. -/
theorem affineSquarefreeMonomial_totalDegree_le_card
    {n : ℕ} (s : Finset (Fin n)) :
    (affineSquarefreeMonomial (K := K) ω s).totalDegree ≤ s.card := by
  classical
  calc
    (affineSquarefreeMonomial (K := K) ω s).totalDegree
        ≤ s.sum (fun i : Fin n =>
            (affineInvPoly (K := K) ω i).totalDegree) := by
          simpa [affineSquarefreeMonomial] using
            (MvPolynomial.totalDegree_finset_prod
              (R := K) (σ := Fin n) s
              (fun i : Fin n => affineInvPoly (K := K) ω i))
    _ ≤ s.sum (fun _ : Fin n => 1) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact affineInvPoly_totalDegree_le_one (K := K) (ω := ω) i
    _ = s.card := by simp

/-- A direct version of the split lemma whose second polynomial is already
composed with the affine inverse substitution.  This is the form needed to
multiply by an approximant to the top monomial. -/
theorem split_multilinear_at_half_degree_direct
    {n : ℕ} (hω0 : ω ≠ 0)
    (c : Finset (Fin n) → K) :
    ∃ P₁ R : MvPolynomial (Fin n) K,
      P₁.totalDegree ≤ n / 2 ∧
      R.totalDegree ≤ n / 2 ∧
      ∀ x : rootCube ω n,
        (squarefreePolynomial (K := K) c).eval x.1 =
          P₁.eval x.1 + (∏ i, x.1 i) * R.eval x.1 := by
  classical
  let low : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun s : Finset (Fin n) => s.card ≤ n / 2)
  let high : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun s : Finset (Fin n) => ¬ s.card ≤ n / 2)
  let term : Finset (Fin n) → MvPolynomial (Fin n) K := fun s =>
    MvPolynomial.C (c s) * squarefreeMonomial (K := K) s
  let P₁ : MvPolynomial (Fin n) K := low.sum term
  let R : MvPolynomial (Fin n) K :=
    high.sum (fun s : Finset (Fin n) =>
      MvPolynomial.C (c s) * affineSquarefreeMonomial (K := K) ω (sᶜ))
  refine ⟨P₁, R, ?_, ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le (s := low) (f := term) ?_
    intro s hs
    have hs_card : s.card ≤ n / 2 := by
      simpa [low] using hs
    have hmono : (squarefreeMonomial (K := K) s).totalDegree ≤ s.card :=
      squarefreeMonomial_totalDegree_le_card (K := K) s
    calc
      (term s).totalDegree
          ≤ (MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree +
              (squarefreeMonomial (K := K) s).totalDegree := by
                simpa [term] using
                  (MvPolynomial.totalDegree_mul
                    (MvPolynomial.C (c s) : MvPolynomial (Fin n) K)
                    (squarefreeMonomial (K := K) s))
      _ ≤ 0 + s.card := by
                simpa using
                  (Nat.add_le_add_left hmono
                    ((MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree))
      _ ≤ n / 2 := by
                simpa using hs_card
  · refine MvPolynomial.totalDegree_finsetSum_le (s := high)
      (f := fun s : Finset (Fin n) =>
        MvPolynomial.C (c s) * affineSquarefreeMonomial (K := K) ω (sᶜ)) ?_
    intro s hs
    have hs_high : ¬ s.card ≤ n / 2 := by
      simpa [high] using hs
    have hs_gt : n / 2 < s.card := Nat.lt_of_not_ge hs_high
    have hs_le_n : s.card ≤ n := by
      simpa using (Finset.card_le_univ (s := s))
    have hcompl_card : (sᶜ).card ≤ n / 2 := by
      have hcard : (sᶜ).card = n - s.card := by
        simpa [Fintype.card_fin] using (Finset.card_compl (s := s))
      omega
    have hmono :
        (affineSquarefreeMonomial (K := K) ω (sᶜ)).totalDegree ≤ (sᶜ).card :=
      affineSquarefreeMonomial_totalDegree_le_card (K := K) (ω := ω) (sᶜ)
    calc
      (MvPolynomial.C (c s) * affineSquarefreeMonomial (K := K) ω (sᶜ)).totalDegree
          ≤ (MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree +
              (affineSquarefreeMonomial (K := K) ω (sᶜ)).totalDegree := by
                simpa using
                  (MvPolynomial.totalDegree_mul
                    (MvPolynomial.C (c s) : MvPolynomial (Fin n) K)
                    (affineSquarefreeMonomial (K := K) ω (sᶜ)))
      _ ≤ 0 + (sᶜ).card := by
                simpa using
                  (Nat.add_le_add_left hmono
                    ((MvPolynomial.C (c s) : MvPolynomial (Fin n) K).totalDegree))
      _ ≤ n / 2 := by
                simpa using hcompl_card
  · intro x
    let highPoly : MvPolynomial (Fin n) K := high.sum term
    have hpartition : P₁ + highPoly = squarefreePolynomial (K := K) c := by
      have hsum :=
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Finset (Fin n))))
          (f := term)
          (p := fun s : Finset (Fin n) => s.card ≤ n / 2))
      simpa [P₁, highPoly, low, high, term, squarefreePolynomial] using hsum
    have hy : ∀ i : Fin n, 1 + ω⁻¹ - ω⁻¹ * x.1 i = (x.1 i)⁻¹ := by
      intro i
      exact rootCube_affine_inverse (ω := ω) hω0 x i
    have hhigh_eval :
        highPoly.eval x.1 = (∏ i : Fin n, x.1 i) * R.eval x.1 := by
      calc
        highPoly.eval x.1
            = high.sum (fun s : Finset (Fin n) =>
                c s * s.prod (fun i : Fin n => x.1 i)) := by
                  simp [highPoly, term, squarefreeMonomial]
        _ = high.sum (fun s : Finset (Fin n) =>
                (∏ i : Fin n, x.1 i) *
                  (c s * (sᶜ).prod
                    (fun i : Fin n => 1 + ω⁻¹ - ω⁻¹ * x.1 i))) := by
                  refine Finset.sum_congr rfl ?_
                  intro s hs
                  have hcomp :
                      (sᶜ).prod (fun i : Fin n => 1 + ω⁻¹ - ω⁻¹ * x.1 i) =
                        (sᶜ).prod (fun i : Fin n => (x.1 i)⁻¹) := by
                    refine Finset.prod_congr rfl ?_
                    intro i hi
                    exact hy i
                  calc
                    c s * s.prod (fun i : Fin n => x.1 i)
                        = c s * ((∏ i : Fin n, x.1 i) *
                            (sᶜ).prod (fun i : Fin n => (x.1 i)⁻¹)) := by
                              rw [rootCube_top_mul_compl_inverse (ω := ω) hω0 x s]
                    _ = (∏ i : Fin n, x.1 i) *
                          (c s * (sᶜ).prod
                            (fun i : Fin n => 1 + ω⁻¹ - ω⁻¹ * x.1 i)) := by
                              rw [hcomp]
                              ring
        _ = (∏ i : Fin n, x.1 i) * R.eval x.1 := by
                  simp [R, affineSquarefreeMonomial, Finset.mul_sum]
    calc
      (squarefreePolynomial (K := K) c).eval x.1
          = (P₁ + highPoly).eval x.1 := by rw [hpartition]
      _ = P₁.eval x.1 + highPoly.eval x.1 := by simp
      _ = P₁.eval x.1 + (∏ i : Fin n, x.1 i) * R.eval x.1 := by rw [hhigh_eval]

end ModqRoadmap

end RazborovSmolensky
