/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.CircuitSize
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain

open Finset
open scoped BigOperators

namespace ACP

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The Boolean `MOD q` function, viewed inside `ZMod p`. -/
noncomputable def modQTarget {q n : ℕ} [Fact (Nat.Prime q)]
    (x : Fin n → Fin 2) : ZMod p :=
  (((modGateOp q n).func x : Fin 2) : Nat)

/-- Number of Boolean inputs on which a polynomial disagrees with a target
function. -/
noncomputable def badInputCount {n : ℕ}
    (f : (Fin n → Fin 2) → ZMod p)
    (P : MvPolynomial (Fin n) (ZMod p)) : ℕ := by
  classical
  exact
    (Finset.univ.filter (fun x : Fin n → Fin 2 =>
      P.eval (boolInput (p := p) x) ≠ f x)).card

/-- A packaged lower bound statement for low-degree polynomial approximation on
`{0,1}^n`.  This is the exact interface needed to combine the Smolensky side of
Razborov-Smolensky with the circuit-approximation theorem already formalized. -/
noncomputable def LowDegreeBadCountLB {n : ℕ}
    (f : (Fin n → Fin 2) → ZMod p) (d E : ℕ) : Prop :=
  ∀ P : MvPolynomial (Fin n) (ZMod p),
    P.totalDegree ≤ d →
    E ≤ badInputCount (p := p) f P

/-- Averaging lemma: if every point is bad for at most a `B / C` fraction of the
parameters, then one parameter is bad on at most a `B / C` fraction of all
points.  This is the list/distribution-to-single-polynomial step needed to pass
from the existing pointwise circuit approximation theorem to one concrete low-
degree polynomial. -/
lemma exists_good_parameter_of_pointwise_bound
    {α β : Type*} [Fintype α]
    [Fintype β] [Nonempty β]
    (Fail : α → β → Prop) [∀ a b, Decidable (Fail a b)]
    (C B : ℕ)
    (hpoint : ∀ a,
      (Finset.univ.filter (fun b : β => Fail a b)).card * C ≤
        B * Fintype.card β) :
    ∃ b,
      (Finset.univ.filter (fun a : α => Fail a b)).card * C ≤
        B * Fintype.card α := by
  classical
  by_contra! h
  have hsum :
      ∑ b : β, (Finset.univ.filter (fun a : α => Fail a b)).card =
        ∑ a : α, (Finset.univ.filter (fun b : β => Fail a b)).card := by
    simp only [card_filter]
    rw [Finset.sum_comm]
  have hsumC :
      ∑ b : β, (Finset.univ.filter (fun a : α => Fail a b)).card * C =
        ∑ a : α, (Finset.univ.filter (fun b : β => Fail a b)).card * C := by
    rw [← Finset.sum_mul, hsum, Finset.sum_mul]
  have hlt :
      Fintype.card β * (B * Fintype.card α) <
        ∑ b : β, (Finset.univ.filter (fun a : α => Fail a b)).card * C := by
    calc
      Fintype.card β * (B * Fintype.card α)
          = ∑ b : β, B * Fintype.card α := by
              simp
      _ < ∑ b : β, (Finset.univ.filter (fun a : α => Fail a b)).card * C := by
            rcases ‹Nonempty β› with ⟨b₀⟩
            refine Finset.sum_lt_sum ?_ ?_
            · intro b hb
              exact le_of_lt (h b)
            · exact ⟨b₀, by simp, h b₀⟩
  have hle :
      ∑ b : β, (Finset.univ.filter (fun a : α => Fail a b)).card * C ≤
        Fintype.card α * (B * Fintype.card β) := by
    calc
      ∑ b : β, (Finset.univ.filter (fun a : α => Fail a b)).card * C
          = ∑ a : α, (Finset.univ.filter (fun b : β => Fail a b)).card * C := hsumC
      _ ≤ ∑ a : α, B * Fintype.card β := by
            refine Finset.sum_le_sum ?_
            intro a ha
            exact hpoint a
      _ = Fintype.card α * (B * Fintype.card β) := by
            simp
  have hcontra :
      Fintype.card β * (B * Fintype.card α) <
        Fintype.card β * (B * Fintype.card α) := by
    calc
      Fintype.card β * (B * Fintype.card α)
          < ∑ b : β, (Finset.univ.filter (fun a : α => Fail a b)).card * C := hlt
      _ ≤ Fintype.card α * (B * Fintype.card β) := hle
      _ = Fintype.card β * (B * Fintype.card α) := by
            ring
  exact (Nat.lt_irrefl _ hcontra)

/-- Specialization of the previous averaging lemma to a finite family of
polynomials over the Boolean cube. -/
theorem exists_single_polynomial_from_pointwise_distribution
    {n : ℕ} {Seed : Type*}
    [Fintype Seed] [Nonempty Seed]
    (P : Seed → MvPolynomial (Fin n) (ZMod p))
    (f : (Fin n → Fin 2) → ZMod p)
    (ℓ B : ℕ)
    (hpoint : ∀ x : Fin n → Fin 2,
      (Finset.univ.filter (fun s : Seed =>
        (P s).eval (boolInput (p := p) x) ≠ f x)).card * 2 ^ ℓ ≤
          B * Fintype.card Seed) :
    ∃ s : Seed,
      badInputCount (p := p) f (P s) * 2 ^ ℓ ≤ B * 2 ^ n := by
  classical
  let Fail : (Fin n → Fin 2) → Seed → Prop := fun x s =>
    (P s).eval (boolInput (p := p) x) ≠ f x
  rcases (exists_good_parameter_of_pointwise_bound
      (α := Fin n → Fin 2) (β := Seed)
      (Fail := Fail) (C := 2 ^ ℓ) (B := B)
      (hpoint := hpoint)) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  simpa [Fail, badInputCount, Fintype.card_fun] using hs

/-- From the already-formalized pointwise approximation theorem for
`AC⁰[p]`-circuits, extract one concrete low-degree polynomial with global error
bounded by `F.size / 2^ℓ`. -/
theorem exists_single_poly_for_circuit_one_size
    {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p)) (ℓ : ℕ) :
    ∃ P : MvPolynomial (Fin n) (ZMod p),
      P.totalDegree ≤ circuitDegreeBound p ℓ F.depth ∧
      badInputCount (p := p)
        (fun x : Fin n → Fin 2 => (((F.eval₁ x : Fin 2) : Nat) : ZMod p)) P * 2 ^ ℓ ≤
          F.size * 2 ^ n := by
  classical
  rcases exists_poly_distribution_for_circuit_one_size (p := p) F hUses ℓ with
    ⟨Seed, instF, _, P, hpos, hdeg, hbad⟩
  letI : Fintype Seed := instF
  letI : Nonempty Seed := Fintype.card_pos_iff.mp hpos
  rcases exists_single_polynomial_from_pointwise_distribution (p := p)
      (P := P)
      (f := fun x : Fin n → Fin 2 => (((F.eval₁ x : Fin 2) : Nat) : ZMod p))
      (ℓ := ℓ) (B := F.size) hbad with ⟨s, hs⟩
  exact ⟨P s, hdeg s, hs⟩

/-- The clean combination theorem: any lower bound against low-degree
polynomials immediately yields a size lower bound for `AC⁰[p]` circuits
computing the same function. -/
theorem size_lower_bound_from_badCountLB
    {q n : ℕ} [Fact (Nat.Prime q)]
    {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p))
    (hCompute : ∀ x : Fin n → Fin 2, F.eval₁ x = (modGateOp q n).func x)
    (ℓ E : ℕ)
    (hLB : LowDegreeBadCountLB (p := p)
      (modQTarget (p := p) (q := q) (n := n))
      (circuitDegreeBound p ℓ F.depth) E) :
    E * 2 ^ ℓ ≤ F.size * 2 ^ n := by
  classical
  rcases exists_single_poly_for_circuit_one_size (p := p) F hUses ℓ with
    ⟨P, hdeg, hbad⟩
  have hbad' :
      badInputCount (p := p)
        (modQTarget (p := p) (q := q) (n := n)) P * 2 ^ ℓ ≤ F.size * 2 ^ n := by
    simpa [badInputCount, modQTarget, hCompute] using hbad
  exact le_trans (Nat.mul_le_mul_right (2 ^ ℓ) (hLB P hdeg)) hbad'

/-- Relative-error version of the previous theorem.  This is usually the form
one wants after proving that every degree-`d` polynomial must disagree with
`MOD q` on at least a fixed fraction `δ` of the Boolean cube. -/
theorem size_lower_bound_from_relative_badCountLB
    {q n δ : ℕ} [Fact (Nat.Prime q)]
    {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p))
    (hCompute : ∀ x : Fin n → Fin 2, F.eval₁ x = (modGateOp q n).func x)
    (ℓ : ℕ)
    (hLB : LowDegreeBadCountLB (p := p)
      (modQTarget (p := p) (q := q) (n := n))
      (circuitDegreeBound p ℓ F.depth) (δ * 2 ^ n)) :
    δ * 2 ^ ℓ ≤ F.size := by
  have hmain :
      (δ * 2 ^ n) * 2 ^ ℓ ≤ F.size * 2 ^ n :=
    size_lower_bound_from_badCountLB (p := p) F hUses hCompute ℓ (δ * 2 ^ n) hLB
  have hmain' :
      (δ * 2 ^ ℓ) * 2 ^ n ≤ F.size * 2 ^ n := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  have hpowpos : 0 < 2 ^ n := by
    positivity
  exact Nat.le_of_mul_le_mul_right hmain' hpowpos

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

end ACP
