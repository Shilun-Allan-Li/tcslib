/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Build.WordTiming
import TCSlib.Complexity.Randomized.PolyExpr
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary polynomial evaluation with an output-length time bound

For each fixed syntactic polynomial, a multitape machine emits its value at one plus the input length. Its time is proportional to the input and output lengths. Expanding into nonzero monomials allows the sharp monomial machines to be combined without an extra power of the input length.

## Main definitions

The private polynomial translation connects syntactic expressions to polynomials over the natural numbers.

## Main results

* `Complexity.exists_unaryPoly_succ_computesFunInTime` computes the unary value within the combined input and output length.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Turing
open scoped BigOperators

attribute [local irreducible] FinTM.ComputesFunInTime FinTM.ComputesInTime

namespace Complexity

open Turing.FinTM

/-- The ordinary polynomial denoted by the syntactic arithmetic expression. -/
private noncomputable def toNatPolynomial : PolyExpr → Polynomial ℕ
  | .const a => Polynomial.C a
  | .var => Polynomial.X
  | .add p q => toNatPolynomial p + toNatPolynomial q
  | .mul p q => toNatPolynomial p * toNatPolynomial q
  | .pow p e => toNatPolynomial p ^ e

/-- The polynomial agrees with the syntactic evaluator.

**Proof sketch.** Induct over the expression using the polynomial evaluation laws. -/
private theorem toNatPolynomial_eval (p : PolyExpr) (n : ℕ) :
    (toNatPolynomial p).eval n = p.eval n := by
  induction p <;> simp_all only [toNatPolynomial, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, PolyExpr.eval_const,
    PolyExpr.eval_var, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_pow]

/-- Nonzero monomials can be evaluated and concatenated at a cost proportional
to their total output length plus the input length.

**Proof sketch.** Induct over the finite set of exponents. The sharp monomial
emitter charges a constant multiple of the monomial, since its coefficient is
positive. Use the bounded concatenation theorem for that emitter and the tail. -/
private theorem exists_unaryMonomialSum (coeff : ℕ → ℕ) (s : Finset ℕ)
    (hs : ∀ e ∈ s, 0 < coeff e) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun x => List.replicate (∑ e ∈ s, coeff e * (x.length + 1) ^ e) true)
      (fun n => c * ((∑ e ∈ s, coeff e * (n + 1) ^ e) + n + 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨constTM [], 1, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
    simp only [Finset.sum_empty, List.replicate_zero, Nat.zero_add, Nat.one_mul]
    exact (constTM_computes [] x).mono (by simp)
  | @insert e s he ih =>
    have hpos := hs e (Finset.mem_insert_self _ _)
    obtain ⟨G, b, hG⟩ := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    let a := coeff e + 5 * e + 4
    obtain ⟨M, c, hM⟩ := exists_append_computesFunInTime (polyUnaryTM_computes (coeff e) e) hG
    refine ⟨M, c * (a + b + 1), (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
    rw [Finset.sum_insert he, List.replicate_add]
    let n := x.length
    let term := coeff e * (n + 1) ^ e
    let rest := ∑ i ∈ s, coeff i * (n + 1) ^ i
    let total := term + rest + n + 1
    have hpow : (n + 1) ^ e ≤ term := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right ((n + 1) ^ e) hpos
    have hterm : (n + 1) ^ e ≤ total := hpow.trans (by dsimp only [total]; omega)
    have hrest : rest + n + 1 ≤ total := by dsimp only [total]; omega
    have hn : n + 1 ≤ total := by dsimp only [total]; omega
    refine ((computesFunInTime_iff _ _ _).1 hM x).mono ?_
    change c * (a * (n + 1) ^ e + b * (rest + n + 1) + n + 1) ≤
      c * (a + b + 1) * total
    calc
      _ ≤ c * (a * total + b * total + total) := by
        apply Nat.mul_le_mul_left
        simpa only [Nat.add_assoc] using
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hterm)
            (Nat.mul_le_mul_left _ hrest)) hn
      _ = _ := by ring

/-- The unary value of a syntactic polynomial at one plus the input length is
computable in time proportional to the sum of the input and output lengths.

**Proof sketch.** Expand the polynomial into its nonzero monomials. For each
degree use the sharp monomial emitter, and concatenate their unary outputs. -/
theorem exists_unaryPoly_succ_computesFunInTime (p : PolyExpr) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun x => List.replicate (p.eval (x.length + 1)) true)
      (fun n => c * (p.eval (n + 1) + n + 1)) := by
  let P := toNatPolynomial p
  have heval (n : ℕ) : p.eval n = ∑ e ∈ P.support, P.coeff e * n ^ e := by
    rw [← toNatPolynomial_eval, ← show P = toNatPolynomial p from rfl,
      Polynomial.eval_eq_sum, Polynomial.sum_def]
  obtain ⟨M, c, hM⟩ := exists_unaryMonomialSum P.coeff P.support fun e he =>
    Nat.pos_of_ne_zero (Polynomial.mem_support_iff.1 he)
  refine ⟨M, c, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  rw [heval]
  exact (computesFunInTime_iff _ _ _).1 hM x

end Complexity
