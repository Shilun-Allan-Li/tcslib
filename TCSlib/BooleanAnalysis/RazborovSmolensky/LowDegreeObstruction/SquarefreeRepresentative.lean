/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-!
# Low-degree squarefree polynomials on the root cube

Squarefree polynomials with supports of size at most `D`, indexed by their
coefficients, and the squarefree representative of a function on `{1, ω}^n`.

## Main definitions

* `RazborovSmolensky.LowDegreeSupport` — supports of size at most `D`.
* `RazborovSmolensky.lowDegreeSquarefreePolynomial` — the polynomial with given
  coefficients on those supports.

## Main results

* `RazborovSmolensky.exists_squarefree_representative_on_rootCube` — every function
  on `{1, ω}^n` agrees with a squarefree polynomial.
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

/-!
## Concrete low-degree squarefree candidate family
-/

/-- Supports of squarefree monomials of degree at most `D`. -/
def LowDegreeSupport (n D : ℕ) :=
  {s : Finset (Fin n) // s.card ≤ D}

noncomputable instance lowDegreeSupportFintype (n D : ℕ) :
    Fintype (LowDegreeSupport n D) := by
  classical
  unfold LowDegreeSupport
  infer_instance

noncomputable instance lowDegreeSupportDecidableEq (n D : ℕ) :
    DecidableEq (LowDegreeSupport n D) := by
  classical
  infer_instance

/-- A local/global convenience instance: once the field is finite, the root cube
is finite.  This keeps the later roadmap theorem statements readable. -/
noncomputable instance rootCubeFintypeOfFintype [Fintype K] (ω : K) (n : ℕ) :
    Fintype (rootCube ω n) := by
  classical
  unfold rootCube
  infer_instance

/-- Function spaces out of the finite root cube are finite.  We define this as
an actual `Pi`-fintype instance, rather than via `Fintype.ofFinite`, so the
standard theorem `Fintype.card_fun` can still rewrite goals involving this
instance. -/
noncomputable instance rootCubeFunctionFintypeOfFintype [Fintype K] (ω : K) (n : ℕ) :
    Fintype (rootCube ω n → K) := by
  classical
  letI : Fintype (rootCube ω n) := rootCubeFintypeOfFintype (K := K) ω n
  exact Pi.instFintype

/-- A degree-`≤ D` squarefree polynomial, represented by its coefficients on
subsets of size at most `D`. -/
noncomputable def lowDegreeSquarefreePolynomial {n D : ℕ}
    (c : LowDegreeSupport n D → K) : MvPolynomial (Fin n) K := by
  classical
  exact
    (Finset.univ : Finset (Finset (Fin n))).sum
      (fun s : Finset (Fin n) =>
        if hs : s.card ≤ D then
          MvPolynomial.C (c ⟨s, hs⟩) * squarefreeMonomial (K := K) s
        else 0)

/- The squarefree interpolation lemma in the coefficient form needed by the
split lemma.  This should ultimately replace the explicit `hrepr` hypothesis in
`rootProd_approx_implies_all_functions_approx`.

The proof is the same two-point Lagrange interpolation used in
`exists_multilinear_representative_on_rootCube` (`SmolenskyAlgebra`), but the
interpolating polynomial is expanded in the squarefree monomial basis.  For
`ω ≠ 1`, the coefficient of `∏ i∈t Xᵢ` is obtained by expanding the product of
one affine Lagrange factor in each coordinate. -/
set_option maxHeartbeats 1000000 in
-- The explicit interpolation proof expands several nested finite sums/products.
theorem exists_squarefree_representative_on_rootCube
    {n : ℕ} (f : rootCube ω n → K) :
    ∃ c : Finset (Fin n) → K,
      ∀ x : rootCube ω n,
        (squarefreePolynomial (K := K) c).eval x.1 = f x := by
  classical
  by_cases hω1 : ω = 1
  · let x0 : rootCube ω n := ⟨fun _ => 1, by
      intro i
      left
      rfl⟩
    let c : Finset (Fin n) → K := fun s => if s = ∅ then f x0 else 0
    refine ⟨c, ?_⟩
    intro x
    have hx : x = x0 := by
      apply Subtype.ext
      funext i
      rcases x.2 i with hx1 | hxω
      · exact hx1
      · simpa [hω1] using hxω
    have hsum :
        ((Finset.univ : Finset (Finset (Fin n))).sum
          (fun s : Finset (Fin n) => if s = ∅ then f x0 else 0)) = f x0 := by
      simpa using
        (Finset.sum_eq_single_of_mem
          (s := (Finset.univ : Finset (Finset (Fin n))))
          (f := fun s : Finset (Fin n) => if s = ∅ then f x0 else 0)
          (a := (∅ : Finset (Fin n)))
          (by simp)
          (by
            intro s hs hne
            simp [hne]))
    calc
      (squarefreePolynomial (K := K) c).eval x.1
          = ((Finset.univ : Finset (Finset (Fin n))).sum
              (fun s : Finset (Fin n) => if s = ∅ then f x0 else 0)) := by
              subst x
              simp [c, squarefreePolynomial, squarefreeMonomial, x0]
      _ = f x0 := hsum
      _ = f x := by simp [hx]
  · have hωm1 : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
    have hone_ne_ω : (1 : K) ≠ ω := by
      intro h1ω
      exact hω1 h1ω.symm
    let a : K := (ω - 1)⁻¹
    have ha_mul : a * (ω - 1) = 1 := by
      dsimp [a]
      rw [mul_comm]
      exact mul_inv_cancel₀ hωm1
    let point : Finset (Fin n) → rootCube ω n := fun s =>
      ⟨fun i => if i ∈ s then ω else 1, by
        intro i
        by_cases hi : i ∈ s <;> simp [hi]⟩
    let code : rootCube ω n → Finset (Fin n) := fun x =>
      Finset.univ.filter (fun i : Fin n => x.1 i = ω)
    let A : Finset (Fin n) → Fin n → K := fun s i =>
      if i ∈ s then a else -a
    let B : Finset (Fin n) → Fin n → K := fun s i =>
      if i ∈ s then -a else a * ω
    let c : Finset (Fin n) → K := fun t =>
      (Finset.univ : Finset (Finset (Fin n))).sum
        (fun s : Finset (Fin n) =>
          f (point s) *
            (t.prod fun i : Fin n => A s i) *
            (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i))
    refine ⟨c, ?_⟩
    intro x
    have hx1_of_ne_ω : ∀ i : Fin n, x.1 i ≠ ω → x.1 i = 1 := by
      intro i hne
      rcases x.2 i with hx1 | hxω
      · exact hx1
      · exact False.elim (hne hxω)
    have hpoint_code : point (code x) = x := by
      apply Subtype.ext
      funext i
      by_cases hxi : x.1 i = ω
      · have hmem : i ∈ code x := by
          simp [code, hxi]
        simp [point, hmem, hxi]
      · have hx1 : x.1 i = 1 := hx1_of_ne_ω i hxi
        have hnotmem : i ∉ code x := by
          simp [code, hxi]
        simp [point, hnotmem, hx1]
    have hcoordinate :
        ∀ (s : Finset (Fin n)) (i : Fin n),
          A s i * x.1 i + B s i =
            if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0 := by
      intro s i
      by_cases his : i ∈ s
      · by_cases hxi : x.1 i = ω
        · calc
            A s i * x.1 i + B s i
                = a * ω + (-a) := by simp [A, B, his, hxi]
            _ = a * (ω - 1) := by ring
            _ = 1 := ha_mul
            _ = (if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) := by
                  simp [his, hxi]
        · have hx1 : x.1 i = 1 := hx1_of_ne_ω i hxi
          calc
            A s i * x.1 i + B s i
                = a * 1 + (-a) := by simp [A, B, his, hx1]
            _ = 0 := by ring
            _ = (if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) := by
                  simp [his, hxi]
      · by_cases hxi : x.1 i = ω
        · calc
            A s i * x.1 i + B s i
                = (-a) * ω + a * ω := by simp [A, B, his, hxi]
            _ = 0 := by ring
            _ = (if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) := by
                  simp [his, hxi]
        · have hx1 : x.1 i = 1 := hx1_of_ne_ω i hxi
          calc
            A s i * x.1 i + B s i
                = (-a) * 1 + a * ω := by simp [A, B, his, hx1]
            _ = a * (ω - 1) := by ring
            _ = 1 := ha_mul
            _ = (if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) := by
                  simp [his, hxi]
    have hprod_indicator :
        ∀ s : Finset (Fin n),
          (∏ i : Fin n, (A s i * x.1 i + B s i)) =
            if s = code x then (1 : K) else 0 := by
      intro s
      have hEq :
          (∀ i : Fin n, i ∈ s ↔ x.1 i = ω) ↔ s = code x := by
        constructor
        · intro hs
          ext i
          simp [code, hs i]
        · intro hs
          subst s
          intro i
          simp [code]
      have hprod_bool :
          (∏ i : Fin n,
              if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) =
            if (∀ i : Fin n, i ∈ s ↔ x.1 i = ω) then (1 : K) else 0 := by
        by_cases hall : ∀ i : Fin n, i ∈ s ↔ x.1 i = ω
        · have hprod :
              (∏ i : Fin n,
                  if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) = 1 := by
            simp [hall]
          rw [hprod, if_pos hall]
        · rcases not_forall.mp hall with ⟨i, hi⟩
          have hprod :
              (∏ j : Fin n,
                  if (j ∈ s ↔ x.1 j = ω) then (1 : K) else 0) = 0 := by
            change
              ((Finset.univ : Finset (Fin n)).prod fun j : Fin n =>
                if (j ∈ s ↔ x.1 j = ω) then (1 : K) else 0) = 0
            exact Finset.prod_eq_zero
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n => if (j ∈ s ↔ x.1 j = ω) then (1 : K) else 0)
              (i := i) (by simp) (by simp [hi])
          rw [hprod, if_neg hall]
      calc
        (∏ i : Fin n, (A s i * x.1 i + B s i))
            = ∏ i : Fin n,
                (if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) := by
                  simp [hcoordinate]
        _ = if (∀ i : Fin n, i ∈ s ↔ x.1 i = ω) then (1 : K) else 0 := hprod_bool
        _ = if s = code x then (1 : K) else 0 := by
              by_cases hs : s = code x
              · have hall : ∀ i : Fin n, i ∈ s ↔ x.1 i = ω := hEq.mpr hs
                rw [if_pos hall, if_pos hs]
              · have hnotall : ¬ ∀ i : Fin n, i ∈ s ↔ x.1 i = ω := by
                  intro hall
                  exact hs (hEq.mp hall)
                rw [if_neg hnotall, if_neg hs]
    have hinner :
        ∀ s : Finset (Fin n),
          ((Finset.univ : Finset (Finset (Fin n))).sum
            (fun t : Finset (Fin n) =>
              ((t.prod fun i : Fin n => A s i) * t.prod (fun i : Fin n => x.1 i)) *
                (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i))) =
            if s = code x then (1 : K) else 0 := by
      intro s
      have hprodadd :=
        (Finset.prod_add
          (f := fun i : Fin n => A s i * x.1 i)
          (g := fun i : Fin n => B s i)
          (s := (Finset.univ : Finset (Fin n))))
      have hsum_powerset :
          (((Finset.univ : Finset (Fin n)).powerset).sum
            (fun t : Finset (Fin n) =>
              (t.prod (fun i : Fin n => A s i * x.1 i)) *
                (((Finset.univ : Finset (Fin n)) \ t).prod
                  (fun i : Fin n => B s i)))) =
            ((Finset.univ : Finset (Fin n)).prod
              (fun i : Fin n => A s i * x.1 i + B s i)) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprodadd.symm
      calc
        ((Finset.univ : Finset (Finset (Fin n))).sum
            (fun t : Finset (Fin n) =>
              ((t.prod fun i : Fin n => A s i) * t.prod (fun i : Fin n => x.1 i)) *
                (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i)))
            = (((Finset.univ : Finset (Fin n)).powerset).sum
                (fun t : Finset (Fin n) =>
                  (t.prod (fun i : Fin n => A s i * x.1 i)) *
                    (((Finset.univ : Finset (Fin n)) \ t).prod
                      (fun i : Fin n => B s i)))) := by
                simp [Finset.prod_mul_distrib, mul_comm, mul_assoc]
        _ = ((Finset.univ : Finset (Fin n)).prod
              (fun i : Fin n => A s i * x.1 i + B s i)) := hsum_powerset
        _ = ∏ i : Fin n, (A s i * x.1 i + B s i) := by simp
        _ = if s = code x then (1 : K) else 0 := hprod_indicator s
    have heval0 :
        (squarefreePolynomial (K := K) c).eval x.1 =
          (Finset.univ : Finset (Finset (Fin n))).sum
            (fun t : Finset (Fin n) =>
              c t * t.prod (fun i : Fin n => x.1 i)) := by
      simp [squarefreePolynomial, squarefreeMonomial]
    have heval_expand :
        (squarefreePolynomial (K := K) c).eval x.1 =
          (Finset.univ : Finset (Finset (Fin n))).sum
            (fun s : Finset (Fin n) =>
              f (point s) *
                ((Finset.univ : Finset (Finset (Fin n))).sum
                  (fun t : Finset (Fin n) =>
                    ((t.prod fun i : Fin n => A s i) * t.prod (fun i : Fin n => x.1 i)) *
                      (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i)))) := by
      calc
        (squarefreePolynomial (K := K) c).eval x.1
            = (Finset.univ : Finset (Finset (Fin n))).sum
                (fun t : Finset (Fin n) =>
                  c t * t.prod (fun i : Fin n => x.1 i)) := heval0
        _ = (Finset.univ : Finset (Finset (Fin n))).sum
              (fun t : Finset (Fin n) =>
                ((Finset.univ : Finset (Finset (Fin n))).sum
                  (fun s : Finset (Fin n) =>
                    f (point s) *
                      (t.prod fun i : Fin n => A s i) *
                      (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i))) *
                  t.prod (fun i : Fin n => x.1 i)) := by
            simp [c]
        _ = (Finset.univ : Finset (Finset (Fin n))).sum
              (fun t : Finset (Fin n) =>
                (Finset.univ : Finset (Finset (Fin n))).sum
                  (fun s : Finset (Fin n) =>
                    (f (point s) *
                      (t.prod fun i : Fin n => A s i) *
                      (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i)) *
                        t.prod (fun i : Fin n => x.1 i))) := by
            simp [Finset.sum_mul]
        _ = (Finset.univ : Finset (Finset (Fin n))).sum
              (fun s : Finset (Fin n) =>
                (Finset.univ : Finset (Finset (Fin n))).sum
                  (fun t : Finset (Fin n) =>
                    (f (point s) *
                      (t.prod fun i : Fin n => A s i) *
                      (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i)) *
                        t.prod (fun i : Fin n => x.1 i))) := by
            rw [Finset.sum_comm]
        _ = (Finset.univ : Finset (Finset (Fin n))).sum
              (fun s : Finset (Fin n) =>
                f (point s) *
                  ((Finset.univ : Finset (Finset (Fin n))).sum
                    (fun t : Finset (Fin n) =>
                      ((t.prod fun i : Fin n => A s i) * t.prod (fun i : Fin n => x.1 i)) *
                        (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i)))) := by
            apply Finset.sum_congr rfl
            intro s hs
            calc
              (Finset.univ : Finset (Finset (Fin n))).sum
                  (fun t : Finset (Fin n) =>
                    (f (point s) *
                      (t.prod fun i : Fin n => A s i) *
                      (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i)) *
                        t.prod (fun i : Fin n => x.1 i))
                  = (Finset.univ : Finset (Finset (Fin n))).sum
                      (fun t : Finset (Fin n) =>
                        f (point s) *
                          (((t.prod fun i : Fin n => A s i) *
                              t.prod (fun i : Fin n => x.1 i)) *
                            (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i))) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    ring
              _ = f (point s) *
                    ((Finset.univ : Finset (Finset (Fin n))).sum
                      (fun t : Finset (Fin n) =>
                        ((t.prod fun i : Fin n => A s i) * t.prod (fun i : Fin n => x.1 i)) *
                          (((Finset.univ : Finset (Fin n)) \ t).prod fun i : Fin n => B s i))) := by
                    rw [Finset.mul_sum]
    calc
      (squarefreePolynomial (K := K) c).eval x.1
          = (Finset.univ : Finset (Finset (Fin n))).sum
              (fun s : Finset (Fin n) => f (point s) *
                (if s = code x then (1 : K) else 0)) := by
              rw [heval_expand]
              simp [hinner]
      _ = f x := by
          simpa [hpoint_code] using
            (Finset.sum_eq_single_of_mem
              (s := (Finset.univ : Finset (Finset (Fin n))))
              (f := fun s : Finset (Fin n) => f (point s) *
                (if s = code x then (1 : K) else 0))
              (a := code x)
              (by simp)
              (by
                intro s hs hne
                simp [hne]))

end RemainingRootCubeRoadmap

end RazborovSmolensky
