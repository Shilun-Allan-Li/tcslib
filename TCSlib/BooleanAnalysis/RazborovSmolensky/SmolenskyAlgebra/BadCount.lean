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

/-!
# Bad-input counts and the circuit-size reduction

The interface between low-degree inapproximability and the circuit lower bound:
the number of Boolean inputs on which a polynomial misses a target, an averaging
step from a pointwise distribution of approximating polynomials to a single one,
and the combination with the circuit approximation theorem.

## Main definitions

* `RazborovSmolensky.modQTarget` — Boolean `MOD q`, viewed in `ZMod p`.
* `RazborovSmolensky.badInputCount` — the number of inputs a polynomial gets wrong.
* `RazborovSmolensky.LowDegreeBadCountLB` — a lower bound on that count for every
  polynomial of bounded total degree.

## Main results

* `RazborovSmolensky.exists_good_parameter_of_pointwise_bound` — the averaging lemma.
* `RazborovSmolensky.size_lower_bound_from_badCountLB`,
  `RazborovSmolensky.size_lower_bound_from_relative_badCountLB` — a bad-count lower
  bound against low-degree polynomials gives a circuit-size lower bound.
-/

open Finset
open scoped BigOperators

namespace RazborovSmolensky

open BoolCircuit

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
    (F : LayeredCircuit (Fin 2) (Fin n) out)
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
    (F : LayeredCircuit (Fin 2) (Fin n) out)
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
    (F : LayeredCircuit (Fin 2) (Fin n) out)
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

end RazborovSmolensky
