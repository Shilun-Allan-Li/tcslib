/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra.BadCount

/-!
# The root-of-unity field and the cube `{1, ω}^n`

The field `𝔽_(p^(q-1))` and its nontrivial `q`-th root of unity `ω`, the cube
`{1, ω}^n`, multilinear representatives of functions on it, and squarefree
polynomials.

## Main definitions

* `RazborovSmolensky.ModqField` — the field `GaloisField p (q - 1)`.
* `RazborovSmolensky.rootCube` — the cube `{1, ω}^n`.
* `RazborovSmolensky.squarefreeMonomial`, `RazborovSmolensky.squarefreePolynomial`.

## Main results

* `RazborovSmolensky.exists_nontrivial_qth_root_modqField` — for `p ≠ q`, `ModqField`
  contains a nontrivial `q`-th root of unity.
* `RazborovSmolensky.exists_multilinear_representative_on_rootCube` — every function
  on `{1, ω}^n` is represented by a polynomial.
* `RazborovSmolensky.rootCube_top_mul_compl_inverse` — the top monomial times an
  inverse complement monomial is the monomial on the support.
-/

open Finset
open scoped BigOperators

namespace RazborovSmolensky

open BoolCircuit

variable (p : ℕ) [Fact (Nat.Prime p)]

section RootOfUnitySetup

/-- Standard field choice for the `MOD q` lower bound: the finite field
`𝔽_(p^(q-1))`. -/
abbrev ModqField (q : ℕ) := GaloisField p (q - 1)


/-- For prime `q`, the exponent `q - 1` used in `ModqField` is nonzero. This is
exactly the side condition required by `GaloisField.card`. -/
lemma q_sub_one_ne_zero
    {q : ℕ} [Fact (Nat.Prime q)] : q - 1 ≠ 0 := by
  have hq : Nat.Prime q := ‹Fact (Nat.Prime q)›.out
  exact Nat.sub_ne_zero_of_lt hq.one_lt

/-- Cardinality of the standard field used in the `MOD q` lower bound. -/
lemma natCard_modqField
    {q : ℕ} [Fact (Nat.Prime q)] :
    Nat.card (ModqField (p := p) q) = p ^ (q - 1) := by
  simpa [ModqField] using GaloisField.card p (q - 1) (q_sub_one_ne_zero (q := q))

/-- Multiplicative-group form of the root-of-unity setup: when `p ≠ q`, the
unit group of `𝔽_(p^(q-1))` contains an element of order exactly `q`.  This is
probably the cleanest first lemma to prove, using the cardinality and cyclicity
of the finite-field unit group. -/
theorem exists_unit_of_order_q_modqField
    {q : ℕ} [Fact (Nat.Prime q)] (hpq : p ≠ q) :
    ∃ u : (ModqField (p := p) q)ˣ, orderOf u = q := by
  classical
  let K := ModqField (p := p) q
  letI : Fintype K := Fintype.ofFinite K
  have hp : Nat.Prime p := ‹Fact (Nat.Prime p)›.out
  have hq : Nat.Prime q := ‹Fact (Nat.Prime q)›.out
  have hcardK : Fintype.card K = p ^ (q - 1) := by
    simpa [Nat.card_eq_fintype_card] using natCard_modqField (p := p) (q := q)
  have hcardUnits : Fintype.card Kˣ = p ^ (q - 1) - 1 := by
    simpa [hcardK] using (Fintype.card_units (α := K))
  have hcop : p.Coprime q := by
    exact (Nat.coprime_primes hp hq).2 hpq
  have hmod : p ^ (q - 1) ≡ 1 [MOD q] :=
    Nat.ModEq.pow_card_sub_one_eq_one hq hcop
  have hpowPos : 0 < p ^ (q - 1) := by
    exact Nat.pow_pos (n := q - 1) hp.pos
  have hdvdUnits : q ∣ Fintype.card Kˣ := by
    have hdiv : q ∣ p ^ (q - 1) - 1 := by
      exact (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt hpowPos)).1 hmod.symm
    simpa [hcardUnits] using hdiv
  have hcountOrderQ : #{u : Kˣ | orderOf u = q} = q.totient := by
    simpa using (IsCyclic.card_orderOf_eq_totient (α := Kˣ) (d := q) hdvdUnits)
  have hnonemptyOrderQ : Finset.Nonempty {u : Kˣ | orderOf u = q} := by
    exact Finset.card_pos.1 <| by
      rw [hcountOrderQ, Nat.totient_prime hq]
      exact Nat.sub_pos_of_lt hq.one_lt
  rcases hnonemptyOrderQ with ⟨u, hu_mem⟩
  exact ⟨u, (Finset.mem_filter.1 hu_mem).2⟩

/-- Field-element form of the previous setup lemma: when `p ≠ q`, the standard
field `𝔽_(p^(q-1))` contains a nontrivial `q`-th root of unity. Since `q` is
prime, this is equivalent to having a primitive `q`-th root of unity. -/
theorem exists_nontrivial_qth_root_modqField
    {q : ℕ} [Fact (Nat.Prime q)] (hpq : p ≠ q) :
    ∃ ω : ModqField (p := p) q, ω ^ q = 1 ∧ ω ≠ 1 := by
  rcases exists_unit_of_order_q_modqField (p := p) (q := q) hpq with ⟨u, hu⟩
  refine ⟨(u : ModqField (p := p) q), ?_, ?_⟩
  · simpa [hu] using
      congrArg (fun x : (ModqField (p := p) q)ˣ => (x : ModqField (p := p) q))
        (pow_orderOf_eq_one u)
  · intro hω
    have hq : Nat.Prime q := ‹Fact (Nat.Prime q)›.out
    have hu1 : u = 1 := Units.ext hω
    have hq1 : q = 1 := by
      calc
        q = orderOf u := hu.symm
        _ = 1 := by simp [hu1]
    exact hq.ne_one hq1

end RootOfUnitySetup

/-!
# Roadmap for the Smolensky side

The remaining work is the actual low-degree inapproximability theorem for
`MOD q` when `q ≠ p`.  The slide in `overview.pdf` suggests the following
formalization path.

1. Move from the Boolean cube to the root-of-unity cube `{1, ω}^n` inside a
   field `K` of characteristic `p` containing a primitive `q`-th root `ω`.
2. Prove that every function on `{1, ω}^n` has a multilinear representative.
   A useful local fact for this step is that on the two-point set `{1, ω}` every
   power `x^k` agrees with an affine-linear expression `a_k + b_k * x`; this is
   the one-variable reduction behind later multilinearization arguments.
3. Split a multilinear polynomial into the low-degree part plus the top
   monomial times a transformed low-degree part:

   `F(x) = F₁(x) + (∏ i, x i) * F₂(1 + ω⁻¹ - ω⁻¹ x₁, ..., 1 + ω⁻¹ - ω⁻¹ xₙ)`.

4. Show that if `∏ i, x i` had a degree-`d` approximant with error `e`, then
   every function on `{1, ω}^n` would have a degree-`n/2 + d` approximant with
   the same error `e`.
5. Count degree-`≤ n/2 + d` multilinear polynomials, count the number of
   functions within distance `e` of one such polynomial, and derive a
   contradiction once the counting inequality is strict.
6. Transfer the resulting lower bound back to Boolean `MOD q`, then feed it
   into `size_lower_bound_from_relative_badCountLB`.

The next section only sets up the main objects and theorem statements; these are
exactly the lemmas that still need to be filled in.
-/

section ModqRoadmap

variable {K : Type*} [Field K]
variable (ω : K)

/-- The `n`-dimensional cube `{1, ω}^n`. -/
def rootCube (n : ℕ) :=
  {x : Fin n → K // ∀ i, x i = 1 ∨ x i = ω}

/-- Every function on `{1, ω}^n` can be represented by a polynomial.  When
`ω ≠ 1` this is the usual two-point Lagrange interpolation on each coordinate;
when `ω = 1` the cube is a singleton and a constant polynomial suffices. -/
theorem exists_multilinear_representative_on_rootCube
    {n : ℕ} (f : rootCube ω n → K) :
    ∃ P : MvPolynomial (Fin n) K,
      ∀ x : rootCube ω n, P.eval x.1 = f x := by
  classical
  by_cases hω1 : ω = 1
  · let x0 : rootCube ω n := ⟨fun _ => 1, by
      intro i
      left
      rfl⟩
    refine ⟨MvPolynomial.C (f x0), ?_⟩
    intro x
    have hx : x = x0 := by
      apply Subtype.ext
      funext i
      rcases x.2 i with hx1 | hxω
      · exact hx1
      · simpa [hω1] using hxω
    simp [x0, hx]
  · have hωm1 : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
    have hone_ne_ω : (1 : K) ≠ ω := by
      intro h1ω
      exact hω1 h1ω.symm
    let point : Finset (Fin n) → rootCube ω n := fun s =>
      ⟨fun i => if i ∈ s then ω else 1, by
        intro i
        by_cases hi : i ∈ s <;> simp [hi]⟩
    let code : rootCube ω n → Finset (Fin n) := fun x =>
      Finset.univ.filter (fun i : Fin n => x.1 i = ω)
    let χω : Fin n → MvPolynomial (Fin n) K := fun i =>
      MvPolynomial.C ((ω - 1)⁻¹) * (MvPolynomial.X i - MvPolynomial.C (1 : K))
    let χ1 : Fin n → MvPolynomial (Fin n) K := fun i =>
      MvPolynomial.C ((ω - 1)⁻¹) * (MvPolynomial.C ω - MvPolynomial.X i)
    let P : MvPolynomial (Fin n) K :=
      ∑ s : Finset (Fin n),
        MvPolynomial.C (f (point s)) *
          ∏ i : Fin n, (if i ∈ s then χω i else χ1 i)
    refine ⟨P, ?_⟩
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
    have hfactor :
        ∀ (s : Finset (Fin n)) (i : Fin n),
          ((if i ∈ s then χω i else χ1 i).eval x.1) =
            (if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) := by
      intro s i
      have hωm1_inv : (ω - 1)⁻¹ * (ω - 1) = 1 := by
        rw [mul_comm]
        exact mul_inv_cancel₀ hωm1
      by_cases his : i ∈ s
      · by_cases hxi : x.1 i = ω
        · simpa [his, hxi, χω, χ1] using hωm1_inv
        · have hx1 : x.1 i = 1 := hx1_of_ne_ω i hxi
          simp [his, hx1, hone_ne_ω, χω, χ1]
      · by_cases hxi : x.1 i = ω
        · simp [his, hxi, χω, χ1]
        · have hx1 : x.1 i = 1 := hx1_of_ne_ω i hxi
          simpa [his, hx1, hone_ne_ω, χω, χ1] using hωm1_inv
    have hindicator :
        ∀ s : Finset (Fin n),
          (∏ i : Fin n, (if i ∈ s then χω i else χ1 i)).eval x.1 =
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
        (∏ i : Fin n, (if i ∈ s then χω i else χ1 i)).eval x.1
            = ∏ i : Fin n,
                (if (i ∈ s ↔ x.1 i = ω) then (1 : K) else 0) := by
                  simp [hfactor]
        _ = if (∀ i : Fin n, i ∈ s ↔ x.1 i = ω) then (1 : K) else 0 := hprod_bool
        _ = if s = code x then (1 : K) else 0 := by
              by_cases hs : s = code x
              · have hall : ∀ i : Fin n, i ∈ s ↔ x.1 i = ω := hEq.mpr hs
                rw [if_pos hall, if_pos hs]
              · have hnotall : ¬ ∀ i : Fin n, i ∈ s ↔ x.1 i = ω := by
                  intro hall
                  exact hs (hEq.mp hall)
                rw [if_neg hnotall, if_neg hs]
    have hterm_eval :
        ∀ s : Finset (Fin n),
          (MvPolynomial.C (f (point s)) *
            ∏ i : Fin n, (if i ∈ s then χω i else χ1 i)).eval x.1 =
              if s = code x then f x else 0 := by
      intro s
      calc
        (MvPolynomial.C (f (point s)) *
          ∏ i : Fin n, (if i ∈ s then χω i else χ1 i)).eval x.1
            = f (point s) * (if s = code x then (1 : K) else 0) := by
                simp [hindicator]
        _ = if s = code x then f x else 0 := by
            by_cases hs : s = code x
            · simp [hs, hpoint_code]
            · simp [hs]
    have hsum_final :
        ((Finset.univ : Finset (Finset (Fin n))).sum
          (fun s : Finset (Fin n) => if s = code x then f x else 0)) = f x := by
      simp
    calc
      P.eval x.1
          = (Finset.univ : Finset (Finset (Fin n))).sum
              (fun s : Finset (Fin n) => if s = code x then f x else 0) := by
              simp [P, hterm_eval]
      _ = f x := hsum_final

/-- The squarefree monomial `∏ i ∈ s, X_i`.  This is the concrete
multilinear basis used in the split step of the Smolensky counting proof. -/
noncomputable def squarefreeMonomial {n : ℕ} (s : Finset (Fin n)) :
    MvPolynomial (Fin n) K :=
  s.prod (fun i : Fin n => MvPolynomial.X i)

/-- A squarefree/multilinear polynomial written by its coefficients on subsets
of variables. -/
noncomputable def squarefreePolynomial {n : ℕ}
    (c : Finset (Fin n) → K) : MvPolynomial (Fin n) K :=
  (Finset.univ : Finset (Finset (Fin n))).sum
    (fun s : Finset (Fin n) =>
      MvPolynomial.C (c s) * squarefreeMonomial (K := K) s)

@[simp] theorem squarefreeMonomial_eval {n : ℕ}
    (s : Finset (Fin n)) (x : Fin n → K) :
    (squarefreeMonomial (K := K) s).eval x = s.prod (fun i : Fin n => x i) := by
  simp [squarefreeMonomial]

/-- On the cube `{1, ω}^n`, the affine expression from the slide is exactly
coordinatewise inversion. -/
theorem rootCube_affine_inverse
    {n : ℕ} (hω0 : ω ≠ 0) (x : rootCube ω n) (i : Fin n) :
    1 + ω⁻¹ - ω⁻¹ * x.1 i = (x.1 i)⁻¹ := by
  rcases x.2 i with hx | hx
  · simp [hx]
  · simp [hx, hω0]

/-- The squarefree monomial indexed by `s` has total degree at most `s.card`. -/
theorem squarefreeMonomial_totalDegree_le_card
    {n : ℕ} (s : Finset (Fin n)) :
    (squarefreeMonomial (K := K) s).totalDegree ≤ s.card := by
  classical
  calc
    (squarefreeMonomial (K := K) s).totalDegree
        ≤ s.sum (fun i : Fin n =>
            (MvPolynomial.X i : MvPolynomial (Fin n) K).totalDegree) := by
          simpa [squarefreeMonomial] using
            (MvPolynomial.totalDegree_finset_prod
              (R := K) (σ := Fin n) s
              (fun i : Fin n => MvPolynomial.X i))
    _ = s.card := by
          simp

/-- Nonzero coordinates on `{1, ω}^n` when `ω ≠ 0`. -/
theorem rootCube_coord_ne_zero
    {n : ℕ} (hω0 : ω ≠ 0) (x : rootCube ω n) (i : Fin n) :
    x.1 i ≠ 0 := by
  rcases x.2 i with hx | hx
  · simp [hx]
  · simpa [hx] using hω0

/-- Multiplying by the top monomial turns a complement monomial in the inverse
coordinates into the original monomial. -/
theorem rootCube_top_mul_compl_inverse
    {n : ℕ} (hω0 : ω ≠ 0) (x : rootCube ω n) (s : Finset (Fin n)) :
    (∏ i : Fin n, x.1 i) * ((sᶜ).prod fun i : Fin n => (x.1 i)⁻¹) =
      s.prod (fun i : Fin n => x.1 i) := by
  classical
  have hsplit :
      ((sᶜ).prod fun i : Fin n => x.1 i) * s.prod (fun i : Fin n => x.1 i) =
        ∏ i : Fin n, x.1 i := by
    simpa using
      (Finset.prod_compl_mul_prod (s := s) (f := fun i : Fin n => x.1 i))
  have hcancel :
      ((sᶜ).prod fun i : Fin n => x.1 i) *
          ((sᶜ).prod fun i : Fin n => (x.1 i)⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one ?_
    intro i hi
    exact mul_inv_cancel₀ (rootCube_coord_ne_zero (ω := ω) hω0 x i)
  calc
    (∏ i : Fin n, x.1 i) * ((sᶜ).prod fun i : Fin n => (x.1 i)⁻¹)
        = (((sᶜ).prod fun i : Fin n => x.1 i) * s.prod (fun i : Fin n => x.1 i)) *
            ((sᶜ).prod fun i : Fin n => (x.1 i)⁻¹) := by
              rw [hsplit]
    _ = s.prod (fun i : Fin n => x.1 i) *
          (((sᶜ).prod fun i : Fin n => x.1 i) *
            ((sᶜ).prod fun i : Fin n => (x.1 i)⁻¹)) := by
              ring
    _ = s.prod (fun i : Fin n => x.1 i) * 1 := by
              exact congrArg
                (fun z : K => s.prod (fun i : Fin n => x.1 i) * z)
                hcancel
    _ = s.prod (fun i : Fin n => x.1 i) := by
              simp

end ModqRoadmap

end RazborovSmolensky
