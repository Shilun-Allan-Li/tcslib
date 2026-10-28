/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimePairing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Syntactic polynomials for lengths and budgets

Every length or budget of the Pass–shelat campaign that depends on the security parameter
`n` — the number of coins and of advice bits of a machine, the input and output lengths of
function families and ensembles, the stretch of a generator, query and round budgets,
auxiliary-input bounds — is a *syntactic* polynomial expression `Complexity.PolyExpr`
(constants, the variable, sums, products, powers), never an abstract function `ℕ → ℕ`
with a bound. This is foundation decision D9 of `PassShelatChapter2-4Plan.md`: an abstract
length function can smuggle undecidable information through length arithmetic (the audit
lesson recorded in `TCSlib.Complexity.ClassNP.NP`), while a syntactic expression is
evaluated, substituted, bounded and computed in unary by structural recursion.

Time bounds of machines stay in the normal form `C * (n + 1) ^ c` of
`Complexity.PolyTimeComputable`; `PolyExpr.normal C c` is that normal form as an
expression, and `PolyExpr.eval_le` shows that every expression is majorised by one.

The unary evaluator `x ↦ 1^{p(|x|)}` (`Complexity.polyTimeComputable_unaryPoly`) lives in
`TCSlib.Complexity.Randomized.Primitives`, next to the unary-multiplication machine its
`mul` case needs; the normal-form instance `Complexity.polyTimeComputable_unaryNormal` is
proved here from the library's `Complexity.polyTimeComputable_polyUnary`.

## Main definitions

* `Complexity.PolyExpr` — syntactic polynomial expressions in the parameter `n`.
* `Complexity.PolyExpr.eval` — evaluation at a parameter.
* `Complexity.PolyExpr.subst` — substitution `p[q/n]` (parameter changes `n ↦ q(n)`).
* `Complexity.PolyExpr.normal` — the normal form `C * (n + 1) ^ c` as an expression.

## Main results

* `Complexity.PolyExpr.eval_subst` — evaluation commutes with substitution.
* `Complexity.PolyExpr.eval_mono` — evaluation is monotone in the parameter.
* `Complexity.PolyExpr.eval_le`, `Complexity.PolyExpr.polyBound_eval` — every expression is
  bounded by a normal form `C * (n + 1) ^ c` (the bridge to `Complexity.PolyBound`).
* `Complexity.polyTimeComputable_unaryNormal` — `x ↦ 1^{C(|x|+1)^c}` is polynomial-time
  computable (the normal-form case of the unary evaluator).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1: polynomials `p(n)` as running-time, coin and advice bounds.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, the function class FP.)
-/

namespace Complexity

open Turing

/-- Syntactic polynomial expressions in the security parameter `n`: every length of the
campaign (coins, advice, input/output lengths, query and round budgets) is one of these,
never an abstract `ℕ → ℕ`. `normal C c` is the campaign normal form `C * (n + 1) ^ c`.
[PS10, §2.1] writes such bounds as "a polynomial `p(n)`"; foundation decision D9 of
`PassShelatChapter2-4Plan.md` fixes the syntactic representation. -/
inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr

/-- Evaluation of a syntactic polynomial at the parameter `n`, by structural recursion. -/
def eval : PolyExpr → ℕ → ℕ
  | const c, _ => c
  | var, n => n
  | add p q, n => p.eval n + q.eval n
  | mul p q, n => p.eval n * q.eval n
  | pow p c, n => (p.eval n) ^ c

/-- Substitution `p[q/n]`: the expression `p` with every occurrence of the variable
replaced by `q` (parameter changes `n ↦ q(n)`, e.g. the coin polynomial of a machine run
at parameter `p(n)` is `coins.subst p`). -/
def subst : PolyExpr → PolyExpr → PolyExpr
  | const c, _ => const c
  | var, q => q
  | add p p', q => add (p.subst q) (p'.subst q)
  | mul p p', q => mul (p.subst q) (p'.subst q)
  | pow p c, q => pow (p.subst q) c

/-- The campaign normal form `C * (n + 1) ^ c` as a syntactic polynomial: the shape of the
time bounds of `Complexity.PolyTimeComputable`. -/
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)

/-- Evaluating a constant. -/
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl

/-- Evaluating the variable. -/
@[simp] theorem eval_var (n : ℕ) : var.eval n = n := rfl

/-- Evaluating a sum. -/
@[simp] theorem eval_add (p q : PolyExpr) (n : ℕ) : (add p q).eval n = p.eval n + q.eval n := rfl

/-- Evaluating a product. -/
@[simp] theorem eval_mul (p q : PolyExpr) (n : ℕ) : (mul p q).eval n = p.eval n * q.eval n := rfl

/-- Evaluating a power. -/
@[simp] theorem eval_pow (p : PolyExpr) (c n : ℕ) : (pow p c).eval n = (p.eval n) ^ c := rfl

/-- The normal form evaluates to `C * (n + 1) ^ c`. -/
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl

/-- Evaluation commutes with substitution: `(p[q/n])(n) = p(q(n))`. -/
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n) := by
  induction p <;> simp_all [subst, eval]

/-- Substituting the variable itself is the identity. -/
theorem subst_var (p : PolyExpr) : p.subst var = p := by
  induction p <;> simp_all [subst]

/-- Evaluation is monotone in the parameter (every coefficient is a natural number). -/
theorem eval_mono (p : PolyExpr) : Monotone p.eval := by
  induction p with
  | const k => intro a b _; exact le_rfl
  | var => intro a b h; exact h
  | add p q hp hq => intro a b h; exact Nat.add_le_add (hp h) (hq h)
  | mul p q hp hq => intro a b h; exact Nat.mul_le_mul (hp h) (hq h)
  | pow p k hp => intro a b h; exact Nat.pow_le_pow_left (hp h) k

/-- Every expression is bounded by a normal form `C * (n + 1) ^ c`: the bridge from syntactic
polynomials to the time bounds of `Complexity.PolyTimeComputable` and to
`Complexity.PolyBound`.

**Proof sketch.** Induction on `p`. Constants and the variable are their own majorants
(`k * (n+1)^0`, `1 * (n+1)^1`). For a sum, raise both degrees to their maximum
(`Nat.pow_le_pow_right`) and add the coefficients; for a product, multiply the coefficients
and add the degrees; for a power, raise the coefficient and multiply the degree
(`Nat.pow_le_pow_left`, `mul_pow`, `pow_mul`). -/
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c := by
  induction p with
  | const k => exact ⟨k, 0, fun n => by simp⟩
  | var => exact ⟨1, 1, fun n => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, c₁, h₁⟩ := hp
    obtain ⟨C₂, c₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max c₁ c₂, fun n => ?_⟩
    have e1 : (n + 1) ^ c₁ ≤ (n + 1) ^ (max c₁ c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_left _ _)
    have e2 : (n + 1) ^ c₂ ≤ (n + 1) ^ (max c₁ c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right _ _)
    calc (add p q).eval n = p.eval n + q.eval n := rfl
      _ ≤ C₁ * (n + 1) ^ c₁ + C₂ * (n + 1) ^ c₂ := Nat.add_le_add (h₁ n) (h₂ n)
      _ ≤ C₁ * (n + 1) ^ (max c₁ c₂) + C₂ * (n + 1) ^ (max c₁ c₂) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
      _ = (C₁ + C₂) * (n + 1) ^ (max c₁ c₂) := by ring
  | mul p q hp hq =>
    obtain ⟨C₁, c₁, h₁⟩ := hp
    obtain ⟨C₂, c₂, h₂⟩ := hq
    refine ⟨C₁ * C₂, c₁ + c₂, fun n => ?_⟩
    calc (mul p q).eval n = p.eval n * q.eval n := rfl
      _ ≤ (C₁ * (n + 1) ^ c₁) * (C₂ * (n + 1) ^ c₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
      _ = (C₁ * C₂) * (n + 1) ^ (c₁ + c₂) := by ring
  | pow p k hp =>
    obtain ⟨C, c, h⟩ := hp
    refine ⟨C ^ k, c * k, fun n => ?_⟩
    calc (pow p k).eval n = (p.eval n) ^ k := rfl
      _ ≤ (C * (n + 1) ^ c) ^ k := Nat.pow_le_pow_left (h n) k
      _ = C ^ k * (n + 1) ^ (c * k) := by rw [mul_pow, ← pow_mul]

/-- The evaluation of a syntactic polynomial is a `Complexity.PolyBound` (the library's
numerical majorant predicate), by `eval_le`. -/
theorem polyBound_eval (p : PolyExpr) : PolyBound p.eval := p.eval_le

/-- A syntactic polynomial is bounded by its own normal-form majorant *as an expression*:
there are `C, c` with `p.eval n ≤ (normal C c).eval n` for every `n`. -/
theorem exists_normal_ge (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ (normal C c).eval n := by
  obtain ⟨C, c, h⟩ := p.eval_le
  exact ⟨C, c, fun n => by rw [eval_normal]; exact h n⟩

end PolyExpr

/-- The unary evaluator of a normal form is polynomial-time: `x ↦ 1^{C(|x|+1)^c}`, i.e.
`x ↦ 1^{(normal C c)(|x|)}`, is polynomial-time computable (the library's
`Complexity.polyTimeComputable_polyUnary`, restated on `PolyExpr.normal`). This is the
case of `Complexity.polyTimeComputable_unaryPoly` that needs no unary multiplication. -/
theorem polyTimeComputable_unaryNormal (C c : ℕ) :
    PolyTimeComputable fun x => List.replicate ((PolyExpr.normal C c).eval x.length) true :=
  polyTimeComputable_polyUnary C c

end Complexity
