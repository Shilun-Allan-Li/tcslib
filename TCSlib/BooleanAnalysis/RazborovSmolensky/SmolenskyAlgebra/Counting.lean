/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra.MultilinearSplit

/-!
# The counting obstruction on the root cube

Over a finite field, Hamming balls around low-degree polynomials cannot cover
all functions on `{1, ω}^n`; so the top monomial `∏ i, x i` has no low-degree
approximant.

## Main definitions

* `RazborovSmolensky.rootCubeBadCount`, `RazborovSmolensky.rootCubeFunctionBadCount`
  — error counts on the root cube.
* `RazborovSmolensky.rootCubeBall` — the Hamming ball around a function.

## Main results

* `RazborovSmolensky.rootCube_counting_obstruction` — the abstract counting
  obstruction.
* `RazborovSmolensky.rootProd_approx_implies_all_functions_approx` — a good
  approximant of the top monomial would approximate every function.
* `RazborovSmolensky.no_low_degree_rootProd_approx`,
  `RazborovSmolensky.no_low_degree_rootProd_approx_of_finite_counting`.
-/

open Finset
open scoped BigOperators

namespace RazborovSmolensky

open BoolCircuit

variable (p : ℕ) [Fact (Nat.Prime p)]

section ModqRoadmap

variable {K : Type*} [Field K]
variable (ω : K)

section CountingAndApproximation

variable [Finite K]

noncomputable instance rootCubeFintype (n : ℕ) : Fintype (rootCube ω n) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  unfold rootCube
  infer_instance

/-- Error count of a polynomial on the root-of-unity cube. -/
noncomputable def rootCubeBadCount {n : ℕ}
    (f : rootCube ω n → K)
    (P : MvPolynomial (Fin n) K) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : rootCube ω n => P.eval x.1 ≠ f x)).card

/-- Hamming error count between two functions on the root-of-unity cube.  The
second argument is written as the “center” function, matching
`rootCubeBadCount`, where a polynomial is compared against a target function. -/
noncomputable def rootCubeFunctionBadCount {n : ℕ}
    (f g : rootCube ω n → K) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : rootCube ω n => g x ≠ f x)).card

/-- The Hamming ball of radius `e` around a function on the root-of-unity cube. -/
noncomputable def rootCubeBall {n : ℕ}
    (center : rootCube ω n → K) (e : ℕ) : Finset (rootCube ω n → K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  exact Finset.univ.filter
    (fun f : rootCube ω n → K => rootCubeFunctionBadCount (ω := ω) f center ≤ e)

/-- A general finite covering/counting lemma for Hamming balls.  If every
function `α → β` lies in one of the balls centered at `center c`, and every such
ball has size at most `B`, then the total number of functions is at most the
number of centers times `B`.

This is the abstract pigeonhole step behind the final counting line of
Smolensky's argument. -/
theorem finite_cover_by_hamming_balls_card_bound
    {α β Cand : Type*} [Fintype α] [Fintype (α → β)] [Fintype Cand]
    [DecidableEq β]
    (center : Cand → α → β) (e B : ℕ)
    (hball : ∀ c : Cand,
      (Finset.univ.filter (fun f : α → β =>
        (Finset.univ.filter (fun a : α => center c a ≠ f a)).card ≤ e)).card ≤ B)
    (hcover : ∀ f : α → β,
      ∃ c : Cand,
        (Finset.univ.filter (fun a : α => center c a ≠ f a)).card ≤ e) :
    Fintype.card (α → β) ≤ Fintype.card Cand * B := by
  classical
  let chooseC : (α → β) → Cand := fun f => Classical.choose (hcover f)
  have hchoose : ∀ f : α → β,
      (Finset.univ.filter (fun a : α => center (chooseC f) a ≠ f a)).card ≤ e := by
    intro f
    exact Classical.choose_spec (hcover f)
  let Enc : Type _ :=
    Sigma (fun c : Cand =>
      {f : α → β //
        (Finset.univ.filter (fun a : α => center c a ≠ f a)).card ≤ e})
  let enc : (α → β) → Enc := fun f =>
    ⟨chooseC f, ⟨f, hchoose f⟩⟩
  have henc_inj : Function.Injective enc := by
    intro f g hfg
    exact congrArg (fun z : Enc => z.2.1) hfg
  have hcard_enc : Fintype.card (α → β) ≤ Fintype.card Enc :=
    Fintype.card_le_of_injective enc henc_inj
  have hcard_Enc : Fintype.card Enc ≤ Fintype.card Cand * B := by
    calc
      Fintype.card Enc
          = ∑ c : Cand,
              Fintype.card
                {f : α → β //
                  (Finset.univ.filter (fun a : α => center c a ≠ f a)).card ≤ e} := by
                simp [Enc]
      _ = ∑ c : Cand,
              (Finset.univ.filter (fun f : α → β =>
                (Finset.univ.filter (fun a : α => center c a ≠ f a)).card ≤ e)).card := by
                refine Finset.sum_congr rfl ?_
                intro c hc
                simpa using
                  (Fintype.card_subtype
                    (fun f : α → β =>
                      (Finset.univ.filter (fun a : α => center c a ≠ f a)).card ≤ e))
      _ ≤ ∑ _c : Cand, B := by
                refine Finset.sum_le_sum ?_
                intro c hc
                exact hball c
      _ = Fintype.card Cand * B := by
                simp
  exact le_trans hcard_enc hcard_Enc

/-- Convert an explicit finite counting bound for a chosen finite family of
candidate polynomial functions into the abstract `hcounting` hypothesis used by
`no_low_degree_rootProd_approx`.

`hcomplete` says that every degree-`≤ D` polynomial function on the cube is
represented, on the cube, by one of the finite candidates `poly c`.  `hball`
bounds the number of functions within Hamming distance `e` of each candidate.
If the resulting union bound is still smaller than the number of all functions
on the cube, not every function can have a degree-`≤ D` approximant. -/
theorem rootCube_counting_obstruction
    {n D e B : ℕ} {Cand : Type*} [Fintype Cand]
    (poly : Cand → MvPolynomial (Fin n) K)
    (hcomplete : ∀ Q : MvPolynomial (Fin n) K,
      Q.totalDegree ≤ D →
        ∃ c : Cand,
          ∀ x : rootCube ω n, (poly c).eval x.1 = Q.eval x.1)
    (hball : ∀ c : Cand,
      (rootCubeBall (ω := ω)
        (fun x : rootCube ω n => (poly c).eval x.1) e).card ≤ B)
    (hstrict : Nat.card (rootCube ω n → K) > Fintype.card Cand * B) :
    ¬ ∀ f : rootCube ω n → K,
        ∃ Q : MvPolynomial (Fin n) K,
          Q.totalDegree ≤ D ∧ rootCubeBadCount (ω := ω) f Q ≤ e := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : DecidableEq (rootCube ω n) := Classical.decEq _
  letI : Fintype (rootCube ω n → K) := inferInstance
  intro hcover
  have hball' : ∀ c : Cand,
      (Finset.univ.filter (fun f : rootCube ω n → K =>
        (Finset.univ.filter (fun x : rootCube ω n =>
          (poly c).eval x.1 ≠ f x)).card ≤ e)).card ≤ B := by
    intro c
    simpa [rootCubeBall, rootCubeFunctionBadCount] using hball c
  have hcover' : ∀ f : rootCube ω n → K,
      ∃ c : Cand,
        (Finset.univ.filter (fun x : rootCube ω n =>
          (poly c).eval x.1 ≠ f x)).card ≤ e := by
    intro f
    rcases hcover f with ⟨Q, hQdeg, hQbad⟩
    rcases hcomplete Q hQdeg with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hbad_eq :
        (Finset.univ.filter (fun x : rootCube ω n =>
          (poly c).eval x.1 ≠ f x)).card =
            rootCubeBadCount (ω := ω) f Q := by
      unfold rootCubeBadCount
      apply congrArg Finset.card
      ext x
      simp [hc x]
    exact hbad_eq.trans_le hQbad
  have hcard_le_ft :
      Fintype.card (rootCube ω n → K) ≤ Fintype.card Cand * B :=
    finite_cover_by_hamming_balls_card_bound
      (α := rootCube ω n) (β := K) (Cand := Cand)
      (center := fun c x => (poly c).eval x.1)
      (e := e) (B := B) hball' hcover'
  have hcard_le_nat :
      Nat.card (rootCube ω n → K) ≤ Fintype.card Cand * B := by
    simpa [Nat.card_eq_fintype_card] using hcard_le_ft
  exact (not_lt_of_ge hcard_le_nat) hstrict

/-- If the top monomial on `{1, ω}^n` had a good low-degree approximant, then
_every_ function on `{1, ω}^n` would have a degree `≤ n / 2 + d` approximant
with the same error. -/
theorem rootProd_approx_implies_all_functions_approx
    {n d e : ℕ}
    (hω0 : ω ≠ 0)
    (hrepr : ∀ f : rootCube ω n → K,
      ∃ c : Finset (Fin n) → K,
        ∀ x : rootCube ω n,
          (squarefreePolynomial (K := K) c).eval x.1 = f x)
    (P : MvPolynomial (Fin n) K)
    (hdeg : P.totalDegree ≤ d)
    (happrox :
      rootCubeBadCount (ω := ω)
        (fun x : rootCube ω n => ∏ i, x.1 i) P ≤ e) :
    ∀ f : rootCube ω n → K,
      ∃ Q : MvPolynomial (Fin n) K,
        Q.totalDegree ≤ n / 2 + d ∧
        rootCubeBadCount (ω := ω) f Q ≤ e := by
  classical
  intro f
  rcases hrepr f with ⟨c, hc⟩
  rcases split_multilinear_at_half_degree_direct (K := K) (ω := ω) hω0 c with
    ⟨P₁, R, hP₁deg, hRdeg, hsplit⟩
  let Q : MvPolynomial (Fin n) K := P₁ + P * R
  refine ⟨Q, ?_, ?_⟩
  · have hmuldeg : (P * R).totalDegree ≤ d + n / 2 := by
      calc
        (P * R).totalDegree ≤ P.totalDegree + R.totalDegree := by
          exact MvPolynomial.totalDegree_mul P R
        _ ≤ d + n / 2 := by
          exact Nat.add_le_add hdeg hRdeg
    calc
      Q.totalDegree ≤ max P₁.totalDegree (P * R).totalDegree := by
        simpa [Q] using MvPolynomial.totalDegree_add P₁ (P * R)
      _ ≤ n / 2 + d := by
        refine max_le ?_ ?_
        · exact le_trans hP₁deg (Nat.le_add_right _ _)
        · omega
  · have hbad_subset :
        rootCubeBadCount (ω := ω) f Q ≤
          rootCubeBadCount (ω := ω)
            (fun x : rootCube ω n => ∏ i, x.1 i) P := by
      unfold rootCubeBadCount
      refine Finset.card_le_card ?_
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      intro htop_eq
      apply hx
      calc
        Q.eval x.1
            = P₁.eval x.1 + P.eval x.1 * R.eval x.1 := by
              simp [Q]
        _ = P₁.eval x.1 + (∏ i : Fin n, x.1 i) * R.eval x.1 := by
              rw [htop_eq]
        _ = (squarefreePolynomial (K := K) c).eval x.1 := by
              rw [hsplit x]
        _ = f x := hc x
    exact le_trans hbad_subset happrox

/-- The final counting contradiction on `{1, ω}^n`, stated with the
counting estimate as an explicit hypothesis.

The hypothesis `hcounting` is the formal place where the entropy/binomial
estimate from the slide belongs: it says that it is impossible for every
function on the root cube to have a degree `≤ n / 2 + d` approximant with at
most `e` bad points.  The previous lemma turns any good approximant to the top
monomial into exactly such approximants for every function, so the contradiction
is immediate. -/
theorem no_low_degree_rootProd_approx
    {n d e : ℕ}
    (hω0 : ω ≠ 0)
    (hrepr : ∀ f : rootCube ω n → K,
      ∃ c : Finset (Fin n) → K,
        ∀ x : rootCube ω n,
          (squarefreePolynomial (K := K) c).eval x.1 = f x)
    (hcounting :
      ¬ ∀ f : rootCube ω n → K,
          ∃ Q : MvPolynomial (Fin n) K,
            Q.totalDegree ≤ n / 2 + d ∧
            rootCubeBadCount (ω := ω) f Q ≤ e) :
    ¬ ∃ P : MvPolynomial (Fin n) K,
        P.totalDegree ≤ d ∧
        rootCubeBadCount (ω := ω)
          (fun x : rootCube ω n => ∏ i, x.1 i) P ≤ e := by
  intro htop
  rcases htop with ⟨P, hdeg, happrox⟩
  apply hcounting
  intro f
  exact
    rootProd_approx_implies_all_functions_approx
      (K := K) (ω := ω) hω0 hrepr P hdeg happrox f

/-- The previous finite counting obstruction plugged into the top-monomial
reduction theorem.  This is the version to use once the candidate type is chosen
—for example, coefficients of multilinear polynomials of degree `≤ n / 2 + d`—
and the numerical entropy/binomial estimate has been proved. -/
theorem no_low_degree_rootProd_approx_of_finite_counting
    {n d e B : ℕ} {Cand : Type*} [Fintype Cand]
    (hω0 : ω ≠ 0)
    (hrepr : ∀ f : rootCube ω n → K,
      ∃ c : Finset (Fin n) → K,
        ∀ x : rootCube ω n,
          (squarefreePolynomial (K := K) c).eval x.1 = f x)
    (poly : Cand → MvPolynomial (Fin n) K)
    (hcomplete : ∀ Q : MvPolynomial (Fin n) K,
      Q.totalDegree ≤ n / 2 + d →
        ∃ c : Cand,
          ∀ x : rootCube ω n, (poly c).eval x.1 = Q.eval x.1)
    (hball : ∀ c : Cand,
      (rootCubeBall (ω := ω)
        (fun x : rootCube ω n => (poly c).eval x.1) e).card ≤ B)
    (hstrict : Nat.card (rootCube ω n → K) > Fintype.card Cand * B) :
    ¬ ∃ P : MvPolynomial (Fin n) K,
        P.totalDegree ≤ d ∧
        rootCubeBadCount (ω := ω)
          (fun x : rootCube ω n => ∏ i, x.1 i) P ≤ e := by
  exact
    no_low_degree_rootProd_approx (K := K) (ω := ω)
      (n := n) (d := d) (e := e) hω0 hrepr
      (rootCube_counting_obstruction (K := K) (ω := ω)
        (n := n) (D := n / 2 + d) (e := e) (B := B)
        (poly := poly) hcomplete hball hstrict)

end CountingAndApproximation

end ModqRoadmap

end RazborovSmolensky
