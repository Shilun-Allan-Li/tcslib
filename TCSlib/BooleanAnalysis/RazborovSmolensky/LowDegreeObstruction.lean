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
# Roadmap file for the remaining Razborov--Smolensky MOD q lower bound

This file deliberately imports the checked checkpoint
`RazborovSmolenskyModqLowerBound_v19` and only adds the remaining theorem
interfaces.  The long algebraic reduction and abstract counting lemmas stay in
`v19`; the statements below can now be proved one by one without making that
file longer.
-/

open Finset
open scoped BigOperators

set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ACP

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

The proof is the same two-point Lagrange interpolation used in `v19`, but the
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

/-- The polynomial represented by low-degree squarefree coefficients really has
total degree at most `D`. -/
theorem lowDegreeSquarefreePolynomial_totalDegree_le
    {n D : ℕ} (c : LowDegreeSupport n D → K) :
    (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).totalDegree ≤ D := by
  classical
  unfold lowDegreeSquarefreePolynomial
  refine MvPolynomial.totalDegree_finsetSum_le
    (s := (Finset.univ : Finset (Finset (Fin n))))
    (f := fun s : Finset (Fin n) =>
      if hs : s.card ≤ D then
        MvPolynomial.C (c ⟨s, hs⟩) * squarefreeMonomial (K := K) s
      else 0) ?_
  intro s hs_univ
  by_cases hsD : s.card ≤ D
  · have hmono : (squarefreeMonomial (K := K) s).totalDegree ≤ s.card :=
      squarefreeMonomial_totalDegree_le_card (K := K) s
    calc
      (if hs : s.card ≤ D then
          MvPolynomial.C (c ⟨s, hs⟩) * squarefreeMonomial (K := K) s
        else 0 : MvPolynomial (Fin n) K).totalDegree
          = (MvPolynomial.C (c ⟨s, hsD⟩) * squarefreeMonomial (K := K) s).totalDegree := by
              simp [hsD]
      _ ≤ (MvPolynomial.C (c ⟨s, hsD⟩) : MvPolynomial (Fin n) K).totalDegree +
            (squarefreeMonomial (K := K) s).totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + s.card := by
          simpa using
            (Nat.add_le_add_left hmono
              ((MvPolynomial.C (c ⟨s, hsD⟩) : MvPolynomial (Fin n) K).totalDegree))
      _ ≤ D := by
          simpa using hsD
  · simp [hsD]

/-- Send a low-degree support to its exact cardinality together with the
underlying finset.  We use this as an injection for the binomial-sum bound,
rather than as a full equivalence, to avoid dependent equality bookkeeping in
the inverse direction. -/
noncomputable def lowDegreeSupportSigmaMap (n D : ℕ) :
    LowDegreeSupport n D →
      Sigma (fun t : Fin (D + 1) => {s : Finset (Fin n) // s.card = t.1}) :=
  fun s => ⟨⟨s.1.card, Nat.lt_succ_of_le s.2⟩, ⟨s.1, rfl⟩⟩

/-- The number of possible low-degree squarefree supports is bounded by the
usual binomial sum. -/
theorem lowDegreeSupport_card_le_binomial_sum
    {n D : ℕ} :
    Fintype.card (LowDegreeSupport n D) ≤
      (Finset.range (D + 1)).sum (fun t : ℕ => Nat.choose n t) := by
  classical
  let T := Sigma (fun t : Fin (D + 1) =>
    {s : Finset (Fin n) // s.card = t.1})
  have hinj : Function.Injective (lowDegreeSupportSigmaMap n D) := by
    intro a b h
    apply Subtype.ext
    have hfinset :
        (lowDegreeSupportSigmaMap n D a).2.1 =
          (lowDegreeSupportSigmaMap n D b).2.1 := by
      exact congrArg (fun z : T => z.2.1) h
    simpa [lowDegreeSupportSigmaMap] using hfinset
  have hcard_le :
      Fintype.card (LowDegreeSupport n D) ≤ Fintype.card T := by
    exact Fintype.card_le_of_injective (lowDegreeSupportSigmaMap n D) hinj
  calc
    Fintype.card (LowDegreeSupport n D)
        ≤ Fintype.card T := hcard_le
    _ = ∑ t : Fin (D + 1),
          Fintype.card {s : Finset (Fin n) // s.card = t.1} := by
          exact Fintype.card_sigma
    _ = ∑ t : Fin (D + 1), Nat.choose n t.1 := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simpa using (Fintype.card_finset_len (α := Fin n) t.1)
    _ = (Finset.range (D + 1)).sum (fun t : ℕ => Nat.choose n t) := by
          simpa using
            (Fin.sum_univ_eq_sum_range (fun t : ℕ => Nat.choose n t) (D + 1))


/-- Cardinality of the coefficient family for degree-`≤ D` squarefree
polynomials. -/
theorem lowDegreeCoeff_card
    {K₀ : Type*} {n D : ℕ} [Fintype K₀] :
    Fintype.card (LowDegreeSupport n D → K₀) =
      Fintype.card K₀ ^ Fintype.card (LowDegreeSupport n D) := by
  classical
  simpa using (Fintype.card_fun :
    Fintype.card (LowDegreeSupport n D → K₀) =
      Fintype.card K₀ ^ Fintype.card (LowDegreeSupport n D))

/-- If `ω ≠ 1`, the root cube is equivalent to Boolean strings: record the
coordinates whose value is `ω`. -/
noncomputable def rootCubeEquivFinTwo {n : ℕ} (hω : ω ≠ 1) :
    rootCube ω n ≃ (Fin n → Fin 2) := by
  classical
  refine
    { toFun := fun x i => if x.1 i = 1 then 0 else 1
      invFun := fun b =>
        ⟨fun i => if b i = 0 then 1 else ω, by
          intro i
          by_cases h : b i = 0 <;> simp [h]⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    funext i
    by_cases hx1 : x.1 i = 1
    · simp [hx1]
    · have hxω : x.1 i = ω := by
        rcases x.2 i with h1 | hωi
        · exact False.elim (hx1 h1)
        · exact hωi
      by_cases hωeq1 : ω = 1
      · exact False.elim (hω hωeq1)
      · simp [hxω, hωeq1]
  · intro b
    funext i
    by_cases h0 : b i = 0
    · simp [h0]
    · have h1 : b i = 1 := by
        apply Fin.ext
        have hne0 : (b i).val ≠ 0 := by
          intro hv
          exact h0 (Fin.ext hv)
        have hlt : (b i).val < 2 := (b i).2
        omega
      simp [h1, hω]

/-- If `ω ≠ 1`, the root cube has exactly `2^n` points. -/
theorem rootCube_card_of_ne_one
    {n : ℕ} [Fintype K] (hω : ω ≠ 1) :
    Fintype.card (rootCube ω n) = 2 ^ n := by
  classical
  calc
    Fintype.card (rootCube ω n)
        = Fintype.card (Fin n → Fin 2) :=
          Fintype.card_congr (rootCubeEquivFinTwo (ω := ω) hω)
    _ = 2 ^ n := by
          simpa [Fintype.card_fun]

/-- Consequently, the number of all functions `{1,ω}^n → K` is `|K|^(2^n)`. -/
theorem rootCube_function_card_of_ne_one
    {n : ℕ} [Fintype K] (hω : ω ≠ 1) :
    Fintype.card (rootCube ω n → K) = Fintype.card K ^ (2 ^ n) := by
  classical
  letI : Fintype (rootCube ω n) := rootCubeFintypeOfFintype (K := K) ω n
  change @Fintype.card (rootCube ω n → K) (Pi.instFintype) = Fintype.card K ^ (2 ^ n)
  rw [Fintype.card_fun]
  rw [rootCube_card_of_ne_one (ω := ω) hω]

section FiniteFieldCounting

variable [Finite K]

/-- A purely finite Hamming-ball bound for functions `α → β`.

The usual sharper form has `(card β - 1)^t`; for the Smolensky counting step the
slightly coarser `card β^t` is enough and is much easier to reuse.  The proof
encodes a function in the ball by the set of coordinates where it differs from
the center, together with arbitrary replacement values on that set. -/
theorem function_hammingBall_card_le_binomial
    {α β : Type*} [Fintype α] [Fintype β] [Fintype (α → β)] [DecidableEq β]
    (center : α → β) (e : ℕ) :
    (Finset.univ.filter (fun f : α → β =>
      (Finset.univ.filter (fun a : α => center a ≠ f a)).card ≤ e)).card ≤
      (Finset.range (e + 1)).sum
        (fun t : ℕ => Nat.choose (Fintype.card α) t * Fintype.card β ^ t) := by
  classical
  let Ball : Type _ :=
    {f : α → β //
      (Finset.univ.filter (fun a : α => center a ≠ f a)).card ≤ e}
  let Enc : Type _ :=
    Sigma (fun t : Fin (e + 1) =>
      Sigma (fun S : {S : Finset α // S.card = t.1} =>
        ({a : α // a ∈ S.1} → β)))
  let decode : Enc → Ball := fun z =>
    match z with
    | ⟨t, ⟨S, vals⟩⟩ =>
        let g : α → β := fun a =>
          if ha : a ∈ S.1 then vals ⟨a, ha⟩ else center a
        ⟨g, by
          have hsubset :
              (Finset.univ.filter (fun a : α => center a ≠ g a)) ⊆ S.1 := by
            intro a ha
            by_contra hnot
            have hg : g a = center a := by
              simp [g, hnot]
            have hne : center a ≠ g a := (Finset.mem_filter.mp ha).2
            exact hne hg.symm
          calc
            (Finset.univ.filter (fun a : α => center a ≠ g a)).card ≤ S.1.card :=
              Finset.card_le_card hsubset
            _ = t.1 := S.2
            _ ≤ e := Nat.le_of_lt_succ t.2⟩
  have hdecode_surj : Function.Surjective decode := by
    intro f
    let S0 : Finset α := Finset.univ.filter (fun a : α => center a ≠ f.1 a)
    have hS0le : S0.card ≤ e := by
      simpa [S0] using f.2
    let t : Fin (e + 1) := ⟨S0.card, Nat.lt_succ_of_le hS0le⟩
    let S : {S : Finset α // S.card = t.1} := ⟨S0, rfl⟩
    let vals : ({a : α // a ∈ S.1} → β) := fun a => f.1 a.1
    refine ⟨⟨t, ⟨S, vals⟩⟩, ?_⟩
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ S0
    · simp [decode, S0, S, vals, ha]
    · have hnot : ¬ center a ≠ f.1 a := by
        simpa [S0] using ha
      have heq : center a = f.1 a := by
        by_contra hne
        exact hnot hne
      simp [decode, S0, S, vals, ha, heq]
  have hball_card :
      (Finset.univ.filter (fun f : α → β =>
        (Finset.univ.filter (fun a : α => center a ≠ f a)).card ≤ e)).card =
        Fintype.card Ball := by
    dsimp [Ball]
    exact (Fintype.card_subtype
      (fun f : α → β =>
        (Finset.univ.filter (fun a : α => center a ≠ f a)).card ≤ e)).symm
  have hcard_le : Fintype.card Ball ≤ Fintype.card Enc :=
    Fintype.card_le_of_surjective decode hdecode_surj
  have hdomain :
      ∀ (t : Fin (e + 1)) (S : {S : Finset α // S.card = t.1}),
        Fintype.card {a : α // a ∈ S.1} = t.1 := by
    intro t S
    calc
      Fintype.card {a : α // a ∈ S.1} = S.1.card := by
        simpa using (Fintype.card_subtype (fun a : α => a ∈ S.1))
      _ = t.1 := S.2
  have hEnc_card :
      Fintype.card Enc =
        ∑ t : Fin (e + 1),
          Nat.choose (Fintype.card α) t.1 * Fintype.card β ^ t.1 := by
    dsimp [Enc]
    rw [Fintype.card_sigma]
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Fintype.card_sigma]
    calc
      (∑ S : {S : Finset α // S.card = t.1},
          Fintype.card ({a : α // a ∈ S.1} → β))
          = ∑ S : {S : Finset α // S.card = t.1},
              Fintype.card β ^ S.1.card := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hdom : Fintype.card {a : α // a ∈ S.1} = S.1.card := by
              simpa using (Fintype.card_subtype (fun a : α => a ∈ S.1))
            rw [Fintype.card_fun, hdom]
      _ = ∑ S : {S : Finset α // S.card = t.1},
              Fintype.card β ^ t.1 := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            simp [S.2]
      _ = Fintype.card {S : Finset α // S.card = t.1} * Fintype.card β ^ t.1 := by
            simp [Finset.sum_const]
      _ = Nat.choose (Fintype.card α) t.1 * Fintype.card β ^ t.1 := by
            have hlen :
                Fintype.card {S : Finset α // S.card = t.1} =
                  Nat.choose (Fintype.card α) t.1 := by
              simpa using (Fintype.card_finset_len (α := α) t.1)
            rw [hlen]
  have hFinRange :
      (∑ t : Fin (e + 1),
          Nat.choose (Fintype.card α) t.1 * Fintype.card β ^ t.1) =
        (Finset.range (e + 1)).sum
          (fun t : ℕ => Nat.choose (Fintype.card α) t * Fintype.card β ^ t) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun t : ℕ => Nat.choose (Fintype.card α) t * Fintype.card β ^ t)
        (e + 1))
  calc
    (Finset.univ.filter (fun f : α → β =>
      (Finset.univ.filter (fun a : α => center a ≠ f a)).card ≤ e)).card
        = Fintype.card Ball := hball_card
    _ ≤ Fintype.card Enc := hcard_le
    _ = ∑ t : Fin (e + 1),
          Nat.choose (Fintype.card α) t.1 * Fintype.card β ^ t.1 := hEnc_card
    _ = (Finset.range (e + 1)).sum
          (fun t : ℕ => Nat.choose (Fintype.card α) t * Fintype.card β ^ t) := hFinRange

/-- A Hamming ball of radius `e` around a function on the root cube has the
standard binomial upper bound.  We use the coarser factor `|K|^t`; this is still
sufficient for the asymptotic counting line. -/
theorem rootCubeBall_card_le_binomial
    {n e : ℕ} (center : rootCube ω n → K) :
    (rootCubeBall (ω := ω) center e).card ≤
      (Finset.range (e + 1)).sum
        (fun t : ℕ =>
          Nat.choose (Nat.card (rootCube ω n)) t * (Nat.card K) ^ t) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (rootCube ω n) := rootCubeFintypeOfFintype (K := K) ω n
  letI : Fintype (rootCube ω n → K) := Pi.instFintype
  have h :=
    function_hammingBall_card_le_binomial
      (α := rootCube ω n) (β := K) (center := center) (e := e)
  simpa [rootCubeBall, rootCubeFunctionBadCount, Nat.card_eq_fintype_card] using h

/-- The concrete finite counting obstruction for degree-`≤ D` polynomial
functions on the root cube, using low-degree squarefree coefficients as the
candidate family. -/
theorem rootCube_counting_obstruction_lowDegreeSquarefree
    {n D e B : ℕ} [Fintype K]
    (hω : ω ≠ 1)
    (hballB :
      (Finset.range (e + 1)).sum
        (fun t : ℕ => Nat.choose (2 ^ n) t * Fintype.card K ^ t) ≤ B)
    (hstrict :
      Fintype.card K ^ (2 ^ n) >
        Fintype.card (LowDegreeSupport n D → K) * B) :
    ¬ ∀ f : rootCube ω n → K,
        ∃ Q : MvPolynomial (Fin n) K,
          Q.totalDegree ≤ D ∧ rootCubeBadCount (ω := ω) f Q ≤ e := by
  classical
  letI : Fintype (rootCube ω n) := rootCubeFintypeOfFintype (K := K) ω n
  letI : Fintype (rootCube ω n → K) := Pi.instFintype
  have hcomplete : ∀ Q : MvPolynomial (Fin n) K,
      Q.totalDegree ≤ D →
        ∃ c : LowDegreeSupport n D → K,
          ∀ x : rootCube ω n,
            (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1 =
              Q.eval x.1 := by
    intro Q hQdeg
    exact lowDegree_squarefree_complete_on_rootCube (K := K) (ω := ω) hω Q hQdeg
  have hball : ∀ c : LowDegreeSupport n D → K,
      (rootCubeBall (ω := ω)
        (fun x : rootCube ω n =>
          (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1) e).card ≤ B := by
    intro c
    have h₁ := rootCubeBall_card_le_binomial (K := K) (ω := ω)
      (center := fun x : rootCube ω n =>
        (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1)
      (e := e)
    have hcubeF : Fintype.card (rootCube ω n) = 2 ^ n :=
      rootCube_card_of_ne_one (K := K) (ω := ω) hω
    have h₂ :
        (rootCubeBall (ω := ω)
          (fun x : rootCube ω n =>
            (lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c).eval x.1) e).card ≤
          (Finset.range (e + 1)).sum
            (fun t : ℕ => Nat.choose (2 ^ n) t * Fintype.card K ^ t) := by
      have hRhs :
          (Finset.range (e + 1)).sum
              (fun t : ℕ => Nat.choose (Nat.card (rootCube ω n)) t * (Nat.card K) ^ t) =
            (Finset.range (e + 1)).sum
              (fun t : ℕ => Nat.choose (2 ^ n) t * Fintype.card K ^ t) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [Nat.card_eq_fintype_card, hcubeF]
      rw [hRhs] at h₁
      exact h₁
    exact le_trans h₂ hballB
  have hstrict' :
      Nat.card (rootCube ω n → K) >
        Fintype.card (LowDegreeSupport n D → K) * B := by
    have hfun : Nat.card (rootCube ω n → K) = Fintype.card K ^ (2 ^ n) := by
      simpa [Nat.card_eq_fintype_card] using
        rootCube_function_card_of_ne_one (K := K) (ω := ω) hω
    rw [hfun]
    exact hstrict
  exact
    rootCube_counting_obstruction (K := K) (ω := ω)
      (n := n) (D := D) (e := e) (B := B)
      (Cand := LowDegreeSupport n D → K)
      (poly := fun c => lowDegreeSquarefreePolynomial (K := K) (n := n) (D := D) c)
      hcomplete hball hstrict'

/-- Concrete root-product lower bound obtained by combining the algebraic
reduction with the finite counting obstruction. -/
theorem no_low_degree_rootProd_approx_concrete
    {n d e B : ℕ} [Fintype K]
    (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (hballB :
      (Finset.range (e + 1)).sum
        (fun t : ℕ => Nat.choose (2 ^ n) t * Fintype.card K ^ t) ≤ B)
    (hstrict :
      Fintype.card K ^ (2 ^ n) >
        Fintype.card (LowDegreeSupport n (n / 2 + d) → K) * B) :
    ¬ ∃ P : MvPolynomial (Fin n) K,
        P.totalDegree ≤ d ∧
        rootCubeBadCount (ω := ω)
          (fun x : rootCube ω n => ∏ i, x.1 i) P ≤ e := by
  classical
  have hrepr : ∀ f : rootCube ω n → K,
      ∃ c : Finset (Fin n) → K,
        ∀ x : rootCube ω n,
          (squarefreePolynomial (K := K) c).eval x.1 = f x := by
    intro f
    exact exists_squarefree_representative_on_rootCube (K := K) (ω := ω) f
  have hcounting :
      ¬ ∀ f : rootCube ω n → K,
          ∃ Q : MvPolynomial (Fin n) K,
            Q.totalDegree ≤ n / 2 + d ∧ rootCubeBadCount (ω := ω) f Q ≤ e :=
    rootCube_counting_obstruction_lowDegreeSquarefree (K := K) (ω := ω)
      (n := n) (D := n / 2 + d) (e := e) (B := B)
      hω1 hballB hstrict
  exact
    no_low_degree_rootProd_approx (K := K) (ω := ω)
      (n := n) (d := d) (e := e) hω0 hrepr hcounting

end FiniteFieldCounting

end RemainingRootCubeRoadmap

end ACP
