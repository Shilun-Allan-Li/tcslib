/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hardness amplification (Yao), concrete layer

From a weak one-way function `f`, which every adversary fails to invert with probability
at least `α`, [Gar26, Theorem 2.1] builds the strong one-way function
`g(x₁, …, x_q) = f(x₁)‖…‖f(x_q)`. The proof turns an inverter `B` of `g` with success `μ`
into the inverter `A` of `f` of [Gar26, Figure 2.2]: repeat `T` times — pick a uniform
position `i`, plant the challenge `y` at position `i` among `f(x_j)` for fresh uniform
`x_j`, call `B`, and keep its `i`-th answer if it is a preimage of `y`.

The analysis fixes a threshold `θ` and the set `S` of *bad* inputs `x`, those on which a
single iteration succeeds with probability at most `θ`. Then:

* (`invProb_prodFun_le`) `μ ≤ (1 - Pr[S])^q + q · θ · Pr[S]`: if `B` succeeds, either no
  `xᵢ` is bad, or some bad `xᵢ` was inverted, and a uniform bad position looks exactly
  like a planted challenge;
* (`one_sub_invProb_yaoInverter_le`) `A` fails with probability at most
  `Pr[S] + (1 - θ)^T`: off `S` the `T` independent iterations all fail with probability
  at most `(1 - θ)^T`.

## The parameters `T` and `θ`

The source sets `θ = α μ / (4n)` and `T = 4n² / (α μ)`, depending on the success `μ` of
`B`, which the reduction does not know and which is only bounded below by an inverse
polynomial for infinitely many `n`. Here `T` and `θ` are explicit parameters, and the
theorems hold for all values satisfying explicit hypotheses, so the asymptotic layer can
instantiate them from one inverse-polynomial lower bound `μ₀ ≤ μ`
(`yao_amplification_exp`). Moreover the source's step `q · θ = μ / 2` needs
`q = 2n / α` exactly, while `q = ⌈2n / α⌉`; taking `θ = μ₀ / (2q)` instead repairs it.

## Main definitions

* `prodFun f q`: the direct product `(x₁, …, x_q) ↦ (f x₁, …, f x_q)`.
* `yaoTry f B y c`: one iteration of [Gar26, Figure 2.2] with coins `c = (i, xs, r)`.
* `yaoInverter f B T`: `T` independent iterations, returning the first success.
* `yaoTryProb f B x`, `yaoBad f B θ`: the per-input success of one iteration and the
  bad set `S`.

## Main results

* `invProb_prodFun_le`: the bound on `μ` through the bad set.
* `one_sub_invProb_yaoInverter_le`: the failure bound for `A`.
* `yao_amplification`: if `(1 - a)^q + q θ < μ` then `A` inverts `f` with probability at
  least `1 - a - (1 - θ)^T`.
* `yao_amplification_exp`: the source's parameters, with failure at most
  `α / 2 + e^{-n}`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Definition 2.2, Theorem 2.1, Figure 2.2).
-/

namespace TCSlib.Cryptography.OneWay

open Finset TCSlib.Cryptography

variable {α β ρ : Type*} [Fintype α] [DecidableEq β] [Fintype ρ] {q : ℕ}

/-- The direct product of `q` copies of `f`: `g(x₁, …, x_q) = f(x₁)‖…‖f(x_q)`.
[Gar26, Theorem 2.1, proof]. -/
def prodFun (f : α → β) (q : ℕ) (xs : Fin q → α) : Fin q → β :=
  fun i => f (xs i)

/-- One iteration of the inverter of [Gar26, Figure 2.2] on challenge `y`, with coins
`c = (i, xs, r)`: plant `y` at position `i` of `(f(x₁), …, f(x_q))`, call `B` with coins
`r`, and return the `i`-th component of its answer. (The test `f(xᵢ') = y` is made by
`yaoInverter`.)

Cost: one call to `B`, `q - 1` evaluations of `f` (the coordinate `xᵢ` is overwritten),
sampling `i ∈ [q]` and `q` inputs. -/
def yaoTry (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (y : β)
    (c : Fin q × (Fin q → α) × ρ) : α :=
  B (Function.update (prodFun f q c.2.1) c.1 y) c.2.2 c.1

/-- The inverter `A` of [Gar26, Figure 2.2], repeated `T` times with independent coins: run
`yaoTry` for `t = 0, …, T - 1` and return the first answer that is a preimage of `y`, or
the default input (the source's `⊥`) if none is.

Cost: `T` calls to `B`, `T` iterations of `yaoTry`, and `T` evaluations of `f` for the
tests. -/
def yaoInverter [Inhabited α] (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (T : ℕ) :
    β → (Fin T → Fin q × (Fin q → α) × ρ) → α :=
  fun y cs => (List.finRange T).foldr
    (fun t acc => if f (yaoTry f B y (cs t)) = y then yaoTry f B y (cs t) else acc) default

/-- The probability, over the coins of one iteration, that `yaoTry` inverts `f(x)`.
[Gar26, Theorem 2.1, proof], `Pr_B[A inverts f(x) in a single iteration]`. -/
noncomputable def yaoTryProb (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (x : α) : ℝ :=
  uprob fun c : Fin q × (Fin q → α) × ρ => f (yaoTry f B (f x) c) = f x

/-- The bad set `S` of inputs on which a single iteration succeeds with probability at most
`θ`. [Gar26, Theorem 2.1, proof], with the threshold `θ` (the source's
`α_f(n) μ_{B,g}(nq) / (4n)`) as a parameter. -/
def yaoBad (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (θ : ℝ) (x : α) : Prop :=
  yaoTryProb f B x ≤ θ

omit [Fintype α] [Fintype ρ] in
/-- If some iteration of `yaoInverter` succeeds then its output is a preimage of `y`. -/
theorem yaoInverter_spec [Inhabited α] (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α))
    {T : ℕ} (y : β) (cs : Fin T → Fin q × (Fin q → α) × ρ)
    (h : ∃ t, f (yaoTry f B y (cs t)) = y) : f (yaoInverter f B T y cs) = y := by
  obtain ⟨t, ht⟩ := h
  have key : ∀ l : List (Fin T), t ∈ l → f (l.foldr (fun t acc =>
      if f (yaoTry f B y (cs t)) = y then yaoTry f B y (cs t) else acc) default) = y := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
      intro hm
      simp only [List.foldr_cons]
      split_ifs with hs
      · exact hs
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd ht hs
        · exact ih hm
  exact key _ (List.mem_finRange t)

omit [Fintype α] [DecidableEq β] in
/-- Planting commutes with applying `f`: `f ∘ (xs with xᵢ := x)` is `f ∘ xs` with its
`i`-th entry replaced by `f x`. -/
theorem prodFun_update (f : α → β) (xs : Fin q → α) (i : Fin q) (x : α) :
    prodFun f q (Function.update xs i x) = Function.update (prodFun f q xs) i (f x) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [prodFun]
  · simp [prodFun, Function.update_of_ne hj]

omit [DecidableEq β] in
/-- The bound on the success `μ` of `B` through the bad set:
`μ ≤ (1 - Pr[S])^q + q · θ · Pr[S]`. [Gar26, Theorem 2.1, proof, the chain bounding
`μ_{B,g}(nq)` under the assumption `Pr[x ∈ S] > α_f(n) / 2`]; that assumption is used
only afterwards, in `yao_amplification`.

**Proof sketch.** If `B` inverts `g(x₁, …, x_q)`, then either every `xᵢ` is outside `S`,
which has probability `(1 - Pr[S])^q`, or for some `i` the input `xᵢ` is in `S` and the
`i`-th answer of `B` is a preimage of `f(xᵢ)`. For fixed `i`, replacing `xᵢ` by a fresh
uniform `x` (planting) does not change the distribution, so the probability of the
latter event is `Pr_x[x ∈ S ∧ one iteration with position i inverts f(x)]`. Summing over
`i` gives `q` times the same event with `i` uniform, which is at most
`q · Pr[S] · θ` by the definition of `S`. -/
theorem invProb_prodFun_le [Nonempty α] [Nonempty ρ] (f : α → β)
    (B : (Fin q → β) → ρ → (Fin q → α)) (θ : ℝ) :
    invProb (prodFun f q) B ≤
      (1 - uprob (yaoBad f B θ)) ^ q + q * θ * uprob (yaoBad f B θ) := by
  classical
  set S := yaoBad f B θ with hSdef
  unfold invProb
  calc uprob (fun z : (Fin q → α) × ρ =>
        prodFun f q (B (prodFun f q z.1) z.2) = prodFun f q z.1)
      ≤ uprob (fun z : (Fin q → α) × ρ => (∀ i, ¬ S (z.1 i)) ∨
          ∃ i ∈ (univ : Finset (Fin q)),
            S (z.1 i) ∧ f (B (prodFun f q z.1) z.2 i) = f (z.1 i)) := by
        -- Success of `B` means some bad input was inverted, unless no input is bad.
        apply uprob_mono
        rintro ⟨xs, r⟩ h
        by_cases hall : ∀ i, ¬ S (xs i)
        · exact Or.inl hall
        · push_neg at hall
          obtain ⟨i, hi⟩ := hall
          exact Or.inr ⟨i, mem_univ _, hi, congrFun h i⟩
    _ ≤ uprob (fun z : (Fin q → α) × ρ => ∀ i, ¬ S (z.1 i)) +
          ∑ i, uprob (fun z : (Fin q → α) × ρ =>
            S (z.1 i) ∧ f (B (prodFun f q z.1) z.2 i) = f (z.1 i)) :=
        (uprob_or_le _ _).trans (add_le_add_left (uprob_exists_le _ _) _)
    _ ≤ _ := by
        apply add_le_add
        · -- No bad input: independent coordinates.
          rw [uprob_fst (fun xs : Fin q → α => ∀ i, ¬ S (xs i)),
            uprob_pi_forall (ι := Fin q) (fun x => ¬ S x), uprob_not, Fintype.card_fin]
        · -- A bad input at position `i` is distributed as a planted challenge.
          have hplant : ∀ i, uprob (fun z : (Fin q → α) × ρ =>
              S (z.1 i) ∧ f (B (prodFun f q z.1) z.2 i) = f (z.1 i)) =
              uprob (fun z : α × ((Fin q → α) × ρ) =>
                S z.1 ∧ f (yaoTry f B (f z.1) (i, z.2)) = f z.1) := by
            intro i
            rw [← uprob_update i (fun xs r =>
              S (xs i) ∧ f (B (prodFun f q xs) r i) = f (xs i))]
            apply uprob_congr
            rintro ⟨x, xs, r⟩
            simp [yaoTry, prodFun_update]
          simp only [hplant]
          -- Make the position uniform, then condition on the bad set.
          rw [sum_uprob_eq_card_mul, Fintype.card_fin]
          let e : α × (Fin q × ((Fin q → α) × ρ)) ≃ Fin q × (α × ((Fin q → α) × ρ)) :=
            { toFun := fun z => (z.2.1, (z.1, z.2.2))
              invFun := fun z => (z.2.1, (z.1, z.2.2))
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          rw [← uprob_comp_equiv e, mul_assoc]
          have hbad := uprob_and_le_mul S
            (fun z : α × (Fin q × (Fin q → α) × ρ) => f (yaoTry f B (f z.1) z.2) = f z.1)
            (θ := θ) (fun a ha => ha)
          exact mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)

/-- The failure probability of the inverter of [Gar26, Figure 2.2] with `T` iterations is
at most `Pr[S] + (1 - θ)^T`. [Gar26, Theorem 2.1, proof, the final computation of
`Pr[A(1ⁿ, f(x)) = ⊥]`]; the source writes `μ_{A,g}` for `μ_{B,g}` there.

**Proof sketch.** `A` fails only if all `T` iterations fail. Given `x`, the iterations
use independent coins, so all fail with probability `(1 - p(x))^T`, where `p(x)` is the
single-iteration success. For `x ∈ S` bound this by `1`; for `x ∉ S`, `p(x) > θ` and it
is at most `(1 - θ)^T`. Average over `x`. -/
theorem one_sub_invProb_yaoInverter_le [Inhabited α] [NeZero q] [Nonempty ρ] (f : α → β)
    (B : (Fin q → β) → ρ → (Fin q → α)) {θ : ℝ} (hθ : θ ≤ 1) (T : ℕ) :
    1 - invProb f (yaoInverter f B T) ≤ uprob (yaoBad f B θ) + (1 - θ) ^ T := by
  classical
  set S := yaoBad f B θ with hSdef
  unfold invProb
  rw [← uprob_not]
  calc uprob (fun z : α × (Fin T → Fin q × (Fin q → α) × ρ) =>
        ¬ f (yaoInverter f B T (f z.1) z.2) = f z.1)
      ≤ uprob (fun z : α × (Fin T → Fin q × (Fin q → α) × ρ) =>
          ∀ t, ¬ f (yaoTry f B (f z.1) (z.2 t)) = f z.1) := by
        -- `A` fails only if every iteration fails.
        apply uprob_mono
        rintro ⟨x, cs⟩ h t ht
        exact h (yaoInverter_spec f B _ cs ⟨t, ht⟩)
    _ = uexp (fun x => (1 - yaoTryProb f B x) ^ T) := by
        -- Given `x`, the iterations are independent.
        rw [uprob_prod]
        congr 1
        funext x
        rw [uprob_pi_forall (fun c => ¬ f (yaoTry f B (f x) c) = f x), uprob_not,
          Fintype.card_fin]
        rfl
    _ ≤ uexp (fun x => (if S x then (1 : ℝ) else 0) + (1 - θ) ^ T) := by
        apply uexp_mono
        intro x
        have h0 := uprob_nonneg fun c : Fin q × (Fin q → α) × ρ =>
          f (yaoTry f B (f x) c) = f x
        have h1 := uprob_le_one fun c : Fin q × (Fin q → α) × ρ =>
          f (yaoTry f B (f x) c) = f x
        change 0 ≤ yaoTryProb f B x at h0
        change yaoTryProb f B x ≤ 1 at h1
        by_cases hx : S x
        · rw [if_pos hx]
          have : (1 - yaoTryProb f B x) ^ T ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
          have : 0 ≤ (1 - θ) ^ T := pow_nonneg (by linarith) _
          linarith
        · rw [if_neg hx, zero_add]
          have : θ < yaoTryProb f B x := lt_of_not_ge hx
          exact pow_le_pow_left₀ (by linarith) (by linarith) _
    _ = _ := by
        rw [uexp_add (fun x => if S x then (1 : ℝ) else 0) (fun _ => (1 - θ) ^ T),
          uexp_indicator, uexp_const, one_mul]

/-- Yao's hardness amplification, concrete form: for any `a` and any threshold
`0 ≤ θ ≤ 1` with `(1 - a)^q + q θ < μ`, where `μ` is the probability that `B` inverts
`g = prodFun f q`, the inverter `A = yaoInverter f B T` inverts `f` with probability at
least `1 - a - (1 - θ)^T`. [Gar26, Theorem 2.1]. Deviation: `T` and `θ` are explicit
parameters rather than functions of the unknown `μ` (see the module docstring); the
source's case `a = α/2`, `θ = αμ/(4n)`, `T = 4n²/(αμ)` is `yao_amplification_exp`.

**Proof sketch.** If `Pr[S] > a` then `(1 - Pr[S])^q ≤ (1 - a)^q` and `Pr[S] ≤ 1`, so
`invProb_prodFun_le` gives `μ ≤ (1 - a)^q + q θ`, a contradiction. Hence `Pr[S] ≤ a`,
and `one_sub_invProb_yaoInverter_le` bounds the failure of `A` by `a + (1 - θ)^T`. -/
theorem yao_amplification [Inhabited α] [NeZero q] [Nonempty ρ] (f : α → β)
    (B : (Fin q → β) → ρ → (Fin q → α)) {a θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (T : ℕ)
    (h : (1 - a) ^ q + q * θ < invProb (prodFun f q) B) :
    1 - a - (1 - θ) ^ T ≤ invProb f (yaoInverter f B T) := by
  have hS : uprob (yaoBad f B θ) ≤ a := by
    by_contra hlt
    push_neg at hlt
    have h1 := invProb_prodFun_le f B θ
    have hS1 := uprob_le_one (yaoBad f B θ)
    have hpow : (1 - uprob (yaoBad f B θ)) ^ q ≤ (1 - a) ^ q :=
      pow_le_pow_left₀ (by linarith) (by linarith) q
    have hmul : (q : ℝ) * θ * uprob (yaoBad f B θ) ≤ q * θ :=
      mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) hθ₀) hS1
    linarith
  have := one_sub_invProb_yaoInverter_le f B hθ₁ T
  linarith

/-- Yao's hardness amplification with the source's parameters: let `α ≤ 1`,
let `B` invert `g = prodFun f q` with probability at least `μ₀ > 2e^{-n}`, and let
`2n ≤ α q` (the source's `q = ⌈2n/α⌉`) and `2nq ≤ μ₀ T` (the source's
`T = 4n²/(αμ)` with `μ₀` for `μ`). Then `A = yaoInverter f B T` inverts `f` with
probability at least `1 - α/2 - e^{-n}`, which exceeds `1 - α` once `e^{-n} < α/2`,
contradicting weak one-wayness. [Gar26, Theorem 2.1]. Deviation: the threshold is
`θ = μ₀ / (2q)` instead of `αμ/(4n)`, which agree when `q = 2n/α`; with the ceiling
`q = ⌈2n/α⌉` the source's `q θ = μ/2` fails, while `q · μ₀/(2q) = μ₀/2` always holds.

**Proof sketch.** Apply `yao_amplification` with `a = α/2` and `θ = μ₀/(2q)`. By
`1 - t ≤ e^{-t}`, `(1 - α/2)^q ≤ e^{-αq/2} ≤ e^{-n}` and
`(1 - θ)^T ≤ e^{-θT} ≤ e^{-n}`; and `e^{-n} + μ₀/2 < μ₀ ≤ μ`. -/
theorem yao_amplification_exp [Inhabited α] [NeZero q] [Nonempty ρ] (f : α → β)
    (B : (Fin q → β) → ρ → (Fin q → α)) {n α' μ₀ : ℝ} (T : ℕ) (hα₁ : α' ≤ 1)
    (hq : 2 * n ≤ α' * q) (hT : 2 * n * q ≤ μ₀ * T) (hμ₀ : 2 * Real.exp (-n) < μ₀)
    (hμ : μ₀ ≤ invProb (prodFun f q) B) :
    1 - α' / 2 - Real.exp (-n) ≤ invProb f (yaoInverter f B T) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hμ1 : μ₀ ≤ 1 := hμ.trans (uprob_le_one _)
  have hexp : 0 < Real.exp (-n) := Real.exp_pos _
  have hμ0 : 0 < μ₀ := by linarith
  set θ := μ₀ / (2 * q) with hθ
  have hθ₀ : 0 ≤ θ := by positivity
  have hθ₁ : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    linarith
  have hqθ : (q : ℝ) * θ = μ₀ / 2 := by
    rw [hθ]
    field_simp
  -- `(1 - α/2)^q ≤ e^{-αq/2} ≤ e^{-n}`.
  have hpow1 : (1 - α' / 2) ^ q ≤ Real.exp (-n) := by
    calc (1 - α' / 2) ^ q ≤ Real.exp (-(α' / 2)) ^ q :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) q
      _ = Real.exp (q * -(α' / 2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-n) := Real.exp_le_exp.mpr (by linarith)
  -- `(1 - θ)^T ≤ e^{-θT} ≤ e^{-n}`.
  have hpow2 : (1 - θ) ^ T ≤ Real.exp (-n) := by
    calc (1 - θ) ^ T ≤ Real.exp (-θ) ^ T :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) T
      _ = Real.exp (T * -θ) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-n) := by
          apply Real.exp_le_exp.mpr
          have : n ≤ T * θ := by
            rw [hθ, mul_div_assoc', le_div_iff₀ (by positivity)]
            linarith
          linarith
  have hmain := yao_amplification f B (a := α' / 2) hθ₀ hθ₁ T (by linarith)
  linarith

end TCSlib.Cryptography.OneWay
