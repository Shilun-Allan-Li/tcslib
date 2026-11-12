/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.ClassNP.EXP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exponential-polynomial time bounds

A bound `T` is *exponential-polynomial* if `T n ≤ 2^{K(n+1)^k}` for some constants. Such
bounds are closed under sums, products, domination and polynomial reparametrization, and a
language decided within one is in `EXP = ⋃_c DTIME(2^{n^c})` [AB09, §2.6.2]. This toolkit
bounds brute-force enumerations, e.g. in `Σ₂ᵖ ⊆ EXP` (`CircuitComplexity/MeyerSigmaEXP.lean`).
It is close to, but distinct from, the numerical helper `Complexity.ExpBound`
(`C · 2^{(n+1)^c}`) of `ClassNP/EXP.lean`.

## Main definitions

* `Complexity.ExpPoly` — "bounded by `2^{K (n+1)^k}`".

## Main results

* `Complexity.ExpPoly.of_le`, `ExpPoly.add`, `ExpPoly.mul`, `ExpPoly.comp_poly`,
  `Complexity.expPoly_exp`, `Complexity.expPoly_poly` — closure properties.
* `Complexity.ExpPoly.mem_EXP` — exponential-polynomial time is `EXP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2.)
-/

namespace Complexity

/-- **An exponential-polynomial bound**: `T n ≤ 2^{K (n+1)^k}` for some constants. -/
def ExpPoly (T : ℕ → ℕ) : Prop := ∃ K k : ℕ, ∀ n, T n ≤ 2 ^ (K * (n + 1) ^ k)

/-- Raising the degree of a positive base. -/
private theorem pow_mono_deg (n k k' : ℕ) (h : k ≤ k') : (n + 1) ^ k ≤ (n + 1) ^ k' :=
  Nat.pow_le_pow_right (by omega) h

/-- Exponential-polynomial bounds are closed under domination. -/
theorem ExpPoly.of_le {T T' : ℕ → ℕ} (h : ExpPoly T') (hle : ∀ n, T n ≤ T' n) : ExpPoly T := by
  obtain ⟨K, k, hK⟩ := h
  exact ⟨K, k, fun n => (hle n).trans (hK n)⟩

/-- The exponential `c · 2^{n^e}` is exponential-polynomial. -/
theorem expPoly_exp (c e : ℕ) : ExpPoly (fun n => c * 2 ^ n ^ e) := by
  refine ⟨c + 1, e, fun n => ?_⟩
  have h1 : c < 2 ^ c := Nat.lt_two_pow_self
  have h2 : n ^ e ≤ (n + 1) ^ e := Nat.pow_le_pow_left (by omega) e
  have h3 : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  calc c * 2 ^ n ^ e ≤ 2 ^ c * 2 ^ (n + 1) ^ e :=
        Nat.mul_le_mul h1.le (Nat.pow_le_pow_right (by omega) h2)
    _ = 2 ^ (c + (n + 1) ^ e) := by rw [pow_add]
    _ ≤ 2 ^ ((c + 1) * (n + 1) ^ e) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- A polynomial `a (n+1)^d` is exponential-polynomial. -/
theorem expPoly_poly (a d : ℕ) : ExpPoly (fun n => a * (n + 1) ^ d) := by
  refine ⟨a + d, 1, fun n => ?_⟩
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have h2 : (n + 1) ^ d ≤ (2 ^ (n + 1)) ^ d := Nat.pow_le_pow_left Nat.lt_two_pow_self.le d
  calc a * (n + 1) ^ d ≤ 2 ^ a * 2 ^ (d * (n + 1)) := by
        rw [pow_mul'] at *; exact Nat.mul_le_mul h1.le h2
    _ = 2 ^ (a + d * (n + 1)) := by rw [pow_add]
    _ ≤ 2 ^ ((a + d) * (n + 1) ^ 1) := Nat.pow_le_pow_right (by omega) (by rw [pow_one]; nlinarith)

/-- Exponential-polynomial bounds are closed under sums. -/
theorem ExpPoly.add {T₁ T₂ : ℕ → ℕ} (h₁ : ExpPoly T₁) (h₂ : ExpPoly T₂) :
    ExpPoly (fun n => T₁ n + T₂ n) := by
  obtain ⟨K₁, k₁, hK₁⟩ := h₁
  obtain ⟨K₂, k₂, hK₂⟩ := h₂
  refine ⟨K₁ + K₂ + 1, max k₁ k₂, fun n => ?_⟩
  set P := (n + 1) ^ max k₁ k₂
  have hp1 : (n + 1) ^ k₁ ≤ P := pow_mono_deg n _ _ (le_max_left _ _)
  have hp2 : (n + 1) ^ k₂ ≤ P := pow_mono_deg n _ _ (le_max_right _ _)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have e1 : T₁ n ≤ 2 ^ (K₁ * P) :=
    (hK₁ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp1))
  have e2 : T₂ n ≤ 2 ^ (K₂ * P) :=
    (hK₂ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp2))
  have e3 : 2 ^ (K₁ * P) ≤ 2 ^ (K₁ * P + K₂ * P) := Nat.pow_le_pow_right (by omega) (by omega)
  have e4 : 2 ^ (K₂ * P) ≤ 2 ^ (K₁ * P + K₂ * P) := Nat.pow_le_pow_right (by omega) (by omega)
  calc T₁ n + T₂ n ≤ 2 * 2 ^ (K₁ * P + K₂ * P) := by omega
    _ = 2 ^ (K₁ * P + K₂ * P + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ ((K₁ + K₂ + 1) * P) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- Exponential-polynomial bounds are closed under products. -/
theorem ExpPoly.mul {T₁ T₂ : ℕ → ℕ} (h₁ : ExpPoly T₁) (h₂ : ExpPoly T₂) :
    ExpPoly (fun n => T₁ n * T₂ n) := by
  obtain ⟨K₁, k₁, hK₁⟩ := h₁
  obtain ⟨K₂, k₂, hK₂⟩ := h₂
  refine ⟨K₁ + K₂, max k₁ k₂, fun n => ?_⟩
  set P := (n + 1) ^ max k₁ k₂
  have hp1 : (n + 1) ^ k₁ ≤ P := pow_mono_deg n _ _ (le_max_left _ _)
  have hp2 : (n + 1) ^ k₂ ≤ P := pow_mono_deg n _ _ (le_max_right _ _)
  calc T₁ n * T₂ n ≤ 2 ^ (K₁ * P) * 2 ^ (K₂ * P) :=
        Nat.mul_le_mul ((hK₁ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp1)))
          ((hK₂ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp2)))
    _ = 2 ^ ((K₁ + K₂) * P) := by rw [← pow_add]; ring_nf

/-- **Exponential-polynomial bounds compose with polynomial arguments**: if `T` is
exponential-polynomial, so is `n ↦ T (a (n+1)^d)`. -/
theorem ExpPoly.comp_poly {T : ℕ → ℕ} (h : ExpPoly T) (a d : ℕ) :
    ExpPoly (fun n => T (a * (n + 1) ^ d)) := by
  obtain ⟨K, k, hK⟩ := h
  refine ⟨K * (a + 1) ^ k, d * k, fun n => ?_⟩
  have h1 : a * (n + 1) ^ d + 1 ≤ (a + 1) * (n + 1) ^ d := by
    have : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc T (a * (n + 1) ^ d) ≤ 2 ^ (K * (a * (n + 1) ^ d + 1) ^ k) := hK _
    _ ≤ 2 ^ (K * ((a + 1) * (n + 1) ^ d) ^ k) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 k))
    _ = 2 ^ (K * (a + 1) ^ k * (n + 1) ^ (d * k)) := by rw [mul_pow, ← pow_mul]; ring_nf

/-- **Exponential-polynomial time is `EXP`** [AB09, Claim 2.4's budget normalization]:
a language decided within an exponential-polynomial bound is in `EXP`.

**Proof sketch.** For `n ≥ 2`, `K (n+1)^k ≤ n^K · n^{2k}`; small lengths are absorbed into
the constant (the argument of the private `enumExponent_bound` of `ClassNP/EXP.lean`). -/
theorem ExpPoly.mem_EXP {T : ℕ → ℕ} (h : ExpPoly T) {L : Language Bool} (hL : L ∈ DTIME T) :
    L ∈ EXP := by
  obtain ⟨K, k, hK⟩ := h
  obtain ⟨c₀, M, hM⟩ := hL
  have hexp : ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) := by
    intro n
    by_cases hn : 2 ≤ n
    · have hK' : K ≤ n ^ K :=
        (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
      have hn' : n + 1 ≤ n ^ 2 := by nlinarith
      have he : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
        calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
               Nat.mul_le_mul hK' (Nat.pow_le_pow_left hn' k)
             _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
      exact (Nat.pow_le_pow_right (by omega) he).trans
        (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
    · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
      calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
             Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
           _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
             Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  refine Set.mem_iUnion.mpr ⟨K + 2 * k, c₀ * 2 ^ (K * 2 ^ k), M, fun x => (hM x).mono ?_⟩
  calc c₀ * T x.length ≤ c₀ * 2 ^ (K * (x.length + 1) ^ k) := Nat.mul_le_mul_left _ (hK _)
    _ ≤ c₀ * (2 ^ (K * 2 ^ k) * 2 ^ x.length ^ (K + 2 * k)) := Nat.mul_le_mul_left _ (hexp _)
    _ = _ := by ring

end Complexity
