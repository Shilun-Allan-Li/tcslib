/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.LowDegreeObstruction.Completeness

/-!
# The concrete counting obstruction for low-degree polynomials

Counts low-degree squarefree polynomials, points of the root cube and Hamming
balls, and concludes that the top monomial has no low-degree approximant.

## Main results

* `RazborovSmolensky.lowDegreeSupport_card_le_binomial_sum`,
  `RazborovSmolensky.lowDegreeCoeff_card` — counting coefficient families.
* `RazborovSmolensky.rootCube_card_of_ne_one`,
  `RazborovSmolensky.rootCube_function_card_of_ne_one` — counting points and functions.
* `RazborovSmolensky.rootCubeBall_card_le_binomial` — the Hamming-ball bound.
* `RazborovSmolensky.rootCube_counting_obstruction_lowDegreeSquarefree`,
  `RazborovSmolensky.no_low_degree_rootProd_approx_concrete`.
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

end RazborovSmolensky
