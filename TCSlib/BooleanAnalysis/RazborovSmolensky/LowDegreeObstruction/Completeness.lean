/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.LowDegreeObstruction.SquarefreeRepresentative

/-!
# Degree-preserving multilinearization on the root cube

On `{1, ω}^n`, a polynomial of degree at most `D` agrees with a squarefree
polynomial whose supports have size at most `D`.

## Main results

* `RazborovSmolensky.monomial_lowDegree_squarefree_complete_on_rootCube` — the
  monomial case.
* `RazborovSmolensky.lowDegreeSquarefreePolynomial_add`, `_zero`, `_sum` —
  linearity in the coefficients.
* `RazborovSmolensky.lowDegree_squarefree_complete_on_rootCube` — the general case.
-/

open Finset
open scoped BigOperators

set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RazborovSmolensky

section RemainingRootCubeRoadmap

variable {K : Type*} [Field K]
variable (ω : K)

/- Degree-preserving multilinearization on `{1,ω}^n`: every polynomial of
ordinary degree at most `D` agrees on the root cube with a squarefree polynomial
whose supports all have size at most `D`.

This is where the one-variable fact from the slide is used: on `{1,ω}`, each
power `x^k` is replaced by an affine-linear function of `x`, and doing this in
each variable does not increase the number of variables in a monomial. -/
/-- Monomial-level degree-preserving multilinearization on `{1,ω}^n`.

A monomial whose total exponent sum is at most `D` agrees on the root cube with
a squarefree polynomial using only supports of size at most `D`.  This is the
atomic version of the slide note: every positive power of a coordinate can be
replaced by its affine interpolant on the two-point set `{1,ω}`. -/
theorem monomial_lowDegree_squarefree_complete_on_rootCube
    {n D : ℕ} (hω : ω ≠ 1)
    (m : Fin n →₀ ℕ) (a : K)
    (hmD : m.sum (fun _ e => e) ≤ D) :
    ∃ c : LowDegreeSupport n D → K,
      ∀ x : rootCube ω n,
        (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1 =
          ((MvPolynomial.monomial m) a).eval x.1 := by
  classical
  let S : Finset (Fin n) := m.support
  have hS_card : S.card ≤ D := by
    have hcard_le_sum : S.card ≤ S.sum (fun i : Fin n => m i) := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum ?_
      intro i hi
      have hne : m i ≠ 0 := by
        simpa [S] using hi
      exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hne)
    calc
      S.card ≤ S.sum (fun i : Fin n => m i) := hcard_le_sum
      _ = m.sum (fun _ e => e) := by
            change m.support.sum (fun i : Fin n => m i) = m.sum (fun _ e => e)
            rw [Finsupp.sum]
      _ ≤ D := hmD
  have hωm1 : ω - 1 ≠ 0 := sub_ne_zero.mpr hω
  let A : Fin n → K := fun i => (ω ^ (m i) - 1) * (ω - 1)⁻¹
  let B : Fin n → K := fun i => 1 - A i
  have hA_mul : ∀ i : Fin n, A i * (ω - 1) = ω ^ (m i) - 1 := by
    intro i
    dsimp [A]
    calc
      ((ω ^ (m i) - 1) * (ω - 1)⁻¹) * (ω - 1)
          = (ω ^ (m i) - 1) * ((ω - 1)⁻¹ * (ω - 1)) := by ring
      _ = (ω ^ (m i) - 1) * 1 := by rw [inv_mul_cancel₀ hωm1]
      _ = ω ^ (m i) - 1 := by ring
  let c : LowDegreeSupport n D → K := fun t =>
    if ht : t.1 ⊆ S then
      a * (t.1.prod fun i : Fin n => A i) *
        ((S \ t.1).prod fun i : Fin n => B i)
    else 0
  refine ⟨c, ?_⟩
  intro x
  have hcoord : ∀ i : Fin n, A i * x.1 i + B i = x.1 i ^ (m i) := by
    intro i
    rcases x.2 i with hx1 | hxω
    · calc
        A i * x.1 i + B i = A i * 1 + (1 - A i) := by simp [B, hx1]
        _ = 1 := by ring
        _ = x.1 i ^ (m i) := by simp [hx1]
    · calc
        A i * x.1 i + B i = A i * ω + (1 - A i) := by simp [B, hxω]
        _ = A i * (ω - 1) + 1 := by ring
        _ = (ω ^ (m i) - 1) + 1 := by rw [hA_mul]
        _ = ω ^ (m i) := by ring
        _ = x.1 i ^ (m i) := by simp [hxω]
  have heval_low :
      (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1 =
        (S.powerset.sum
          (fun t : Finset (Fin n) =>
            (a * (t.prod fun i : Fin n => A i) *
                ((S \ t).prod fun i : Fin n => B i)) *
              t.prod (fun i : Fin n => x.1 i))) := by
    unfold lowDegreeSquarefreePolynomial
    rw [MvPolynomial.eval_sum]
    have hsubset_univ : S.powerset ⊆ (Finset.univ : Finset (Finset (Fin n))) := by
      intro t ht
      simp
    calc
      (Finset.univ : Finset (Finset (Fin n))).sum
          (fun t : Finset (Fin n) =>
            (MvPolynomial.eval x.1)
              (if ht : t.card ≤ D then
                MvPolynomial.C (c ⟨t, ht⟩) * squarefreeMonomial (K := K) t
              else 0))
          = S.powerset.sum
              (fun t : Finset (Fin n) =>
                (MvPolynomial.eval x.1)
                  (if ht : t.card ≤ D then
                    MvPolynomial.C (c ⟨t, ht⟩) * squarefreeMonomial (K := K) t
                  else 0)) := by
              refine (Finset.sum_subset hsubset_univ ?_).symm
              intro t ht_univ ht_not
              have hnot_subset : ¬ t ⊆ S := by
                intro hts
                exact ht_not (by simpa [Finset.mem_powerset] using hts)
              by_cases htD : t.card ≤ D
              · simp [htD, c, hnot_subset]
              · simp [htD]
      _ = S.powerset.sum
            (fun t : Finset (Fin n) =>
              (a * (t.prod fun i : Fin n => A i) *
                  ((S \ t).prod fun i : Fin n => B i)) *
                t.prod (fun i : Fin n => x.1 i)) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have hts : t ⊆ S := by
                simpa [Finset.mem_powerset] using ht
              have htD : t.card ≤ D := le_trans (Finset.card_le_card hts) hS_card
              simp [htD, c, hts, squarefreeMonomial, mul_assoc]
  have hprod_expand :
      S.powerset.sum
        (fun t : Finset (Fin n) =>
          (a * (t.prod fun i : Fin n => A i) *
              ((S \ t).prod fun i : Fin n => B i)) *
            t.prod (fun i : Fin n => x.1 i)) =
        a * S.prod (fun i : Fin n => A i * x.1 i + B i) := by
    have hprodadd :=
      (Finset.prod_add
        (f := fun i : Fin n => A i * x.1 i)
        (g := fun i : Fin n => B i)
        (s := S))
    calc
      S.powerset.sum
        (fun t : Finset (Fin n) =>
          (a * (t.prod fun i : Fin n => A i) *
              ((S \ t).prod fun i : Fin n => B i)) *
            t.prod (fun i : Fin n => x.1 i))
          = a * S.powerset.sum
              (fun t : Finset (Fin n) =>
                (t.prod (fun i : Fin n => A i * x.1 i)) *
                  ((S \ t).prod fun i : Fin n => B i)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro t ht
              have hAx :
                  t.prod (fun i : Fin n => A i * x.1 i) =
                    t.prod (fun i : Fin n => A i) *
                      t.prod (fun i : Fin n => x.1 i) := by
                simpa using
                  (Finset.prod_mul_distrib :
                    t.prod (fun i : Fin n => A i * x.1 i) =
                      t.prod (fun i : Fin n => A i) *
                        t.prod (fun i : Fin n => x.1 i))
              rw [hAx]
              ring
      _ = a * S.prod (fun i : Fin n => A i * x.1 i + B i) := by
              rw [hprodadd]
  have hprod_coord :
      S.prod (fun i : Fin n => A i * x.1 i + B i) =
        S.prod (fun i : Fin n => x.1 i ^ (m i)) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    exact hcoord i
  calc
    (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1
        = S.powerset.sum
            (fun t : Finset (Fin n) =>
              (a * (t.prod fun i : Fin n => A i) *
                  ((S \ t).prod fun i : Fin n => B i)) *
                t.prod (fun i : Fin n => x.1 i)) := heval_low
    _ = a * S.prod (fun i : Fin n => A i * x.1 i + B i) := hprod_expand
    _ = a * S.prod (fun i : Fin n => x.1 i ^ (m i)) := by rw [hprod_coord]
    _ = a * m.prod (fun i e => x.1 i ^ e) := by
          congr 1
    _ = ((MvPolynomial.monomial m) a).eval x.1 := by
          rw [MvPolynomial.eval_monomial]

/-- Linearity of the concrete squarefree-polynomial constructor in its
coefficient function. -/
theorem lowDegreeSquarefreePolynomial_add
    {n D : ℕ} (c₁ c₂ : LowDegreeSupport n D → K) :
    lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D)
        (fun s => c₁ s + c₂ s) =
      lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c₁ +
        lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c₂ := by
  classical
  unfold lowDegreeSquarefreePolynomial
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsD : s.card ≤ D
  · simp [hsD, add_mul]
  · simp [hsD]

/-- The concrete squarefree-polynomial constructor sends the zero coefficient
function to the zero polynomial. -/
theorem lowDegreeSquarefreePolynomial_zero
    {n D : ℕ} :
    lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D)
        (fun _ : LowDegreeSupport n D => (0 : K)) = 0 := by
  classical
  unfold lowDegreeSquarefreePolynomial
  refine Finset.sum_eq_zero ?_
  intro s hs
  by_cases hsD : s.card ≤ D <;> simp [hsD]

/-- Finite-sum version of coefficient linearity for
`lowDegreeSquarefreePolynomial`. -/
theorem lowDegreeSquarefreePolynomial_sum
    {n D : ℕ} {ι : Type*} (S : Finset ι)
    (c : ι → LowDegreeSupport n D → K) :
    lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D)
        (fun s => S.sum (fun i => c i s)) =
      S.sum (fun i =>
        lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) (c i)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp [lowDegreeSquarefreePolynomial_zero (K := K) (n := n) (D := D)]
  | insert a S ha ih =>
      calc
        lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D)
            (fun s => (insert a S).sum (fun i => c i s))
            = lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D)
                (fun s => c a s + S.sum (fun i => c i s)) := by
                  refine congrArg
                    (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D)) ?_
                  funext s
                  simp [ha]
        _ = lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) (c a) +
              lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D)
                (fun s => S.sum (fun i => c i s)) := by
                  rw [lowDegreeSquarefreePolynomial_add]
        _ = (insert a S).sum (fun i =>
              lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) (c i)) := by
                  rw [ih]
                  simp [ha]

theorem lowDegree_squarefree_complete_on_rootCube
    {n D : ℕ} (hω : ω ≠ 1)
    (Q : MvPolynomial (Fin n) K) (hQdeg : Q.totalDegree ≤ D) :
    ∃ c : LowDegreeSupport n D → K,
      ∀ x : rootCube ω n,
        (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1 =
          Q.eval x.1 := by
  classical
  let rep : (m : Fin n →₀ ℕ) → LowDegreeSupport n D → K := fun m =>
    if hm : m ∈ Q.support then
      Classical.choose
        (monomial_lowDegree_squarefree_complete_on_rootCube
          (K := K) (ω := ω) (n := n) (D := D) hω m
          (MvPolynomial.coeff m Q)
          (le_trans (MvPolynomial.le_totalDegree (p := Q) hm) hQdeg))
    else 0
  let c : LowDegreeSupport n D → K := fun s =>
    Q.support.sum (fun m => rep m s)
  refine ⟨c, ?_⟩
  intro x
  have hrep : ∀ m ∈ Q.support,
      (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) (rep m)).eval x.1 =
        ((MvPolynomial.monomial m) (MvPolynomial.coeff m Q)).eval x.1 := by
    intro m hm
    have hchoose :=
      (Classical.choose_spec
        (monomial_lowDegree_squarefree_complete_on_rootCube
          (K := K) (ω := ω) (n := n) (D := D) hω m
          (MvPolynomial.coeff m Q)
          (le_trans (MvPolynomial.le_totalDegree (p := Q) hm) hQdeg))) x
    have hcoeff_ne : ¬ MvPolynomial.coeff m Q = 0 := by
      have hcoeff_ne' : MvPolynomial.coeff m Q ≠ 0 := by
        simpa [MvPolynomial.mem_support_iff] using hm
      exact hcoeff_ne'
    simpa [rep, hm, hcoeff_ne] using hchoose
  calc
    (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1
        = (Q.support.sum (fun m =>
            lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) (rep m))).eval x.1 := by
              have hpoly := lowDegreeSquarefreePolynomial_sum
                (K := K) (n := n) (D := D) (S := Q.support) (c := rep)
              simpa [c] using congrArg (fun P : MvPolynomial (Fin n) K => P.eval x.1) hpoly
    _ = Q.support.sum (fun m =>
            (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) (rep m)).eval x.1) := by
              simp
    _ = Q.support.sum (fun m =>
            ((MvPolynomial.monomial m) (MvPolynomial.coeff m Q)).eval x.1) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              exact hrep m hm
    _ = Q.eval x.1 := by
              rw [← map_sum]
              exact congrArg (fun P : MvPolynomial (Fin n) K => P.eval x.1)
                (MvPolynomial.support_sum_monomial_coeff Q)

end RemainingRootCubeRoadmap

end RazborovSmolensky
