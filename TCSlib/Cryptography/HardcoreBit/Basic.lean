/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Probability
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expectations and uniform pushforwards

Toolkit for the Goldreich–Levin development: algebra of the uniform average `uexp`, and
maps that push the uniform distribution forward to the uniform distribution. Such maps
carry every probability and expectation unchanged, which is how all distributional
facts of the proof (a shifted query is uniform, two coordinates of a uniform tuple are
independent and uniform, a subset XOR of uniform strings is uniform) are expressed.

## Main definitions

* `PushesUniform π`: the pushforward of the uniform distribution along `π` is uniform.

## Main results

* `uexp_add`, `uexp_const_mul`, `uexp_sum`, `uexp_mono`, `uexp_prod`: linearity,
  monotonicity and Fubini for `uexp`.
* `uprob_prod_and`: independent events on a product multiply.
* `half_le_uprob_threshold`: if the average of a `[0, 1]`-valued function is at least
  `c + ε`, then the points where it is at least `c + ε / 2` have probability at least
  `ε / 2` (the "good set" argument of [Gar26, §2.5.1]).
* `pushesUniform_eval`, `pushesUniform_eval_pair`, `PushesUniform.prodMap`,
  `pushesUniform_of_surjective`: coordinates and pairs of coordinates of a uniform
  tuple, products, and surjective additive homomorphisms push uniform to uniform.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

variable {Ω Ω' α β γ δ : Type*} [Fintype Ω] [Fintype Ω'] [Fintype α] [Fintype β]
  [Fintype γ] [Fintype δ]

/-! ### Algebra of `uexp` -/

/-- The average of a sum is the sum of the averages. -/
theorem uexp_add (f g : Ω → ℝ) : uexp (fun ω => f ω + g ω) = uexp f + uexp g := by
  simp only [uexp, sum_add_distrib, add_div]

/-- The average of a difference is the difference of the averages. -/
theorem uexp_sub (f g : Ω → ℝ) : uexp (fun ω => f ω - g ω) = uexp f - uexp g := by
  simp only [uexp, sum_sub_distrib, sub_div]

/-- Constants factor out of an average. -/
theorem uexp_const_mul (c : ℝ) (f : Ω → ℝ) : uexp (fun ω => c * f ω) = c * uexp f := by
  simp only [uexp, ← mul_sum, mul_div_assoc]

/-- The average of a constant over a nonempty type is that constant. -/
theorem uexp_const [Nonempty Ω] (c : ℝ) : uexp (fun _ : Ω => c) = c := by
  have : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uexp, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- The average of a finite sum of functions is the sum of their averages. -/
theorem uexp_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    uexp (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, uexp (f i) := by
  simp only [uexp, ← sum_div]
  rw [sum_comm]

/-- Averages are monotone. -/
theorem uexp_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : uexp f ≤ uexp g :=
  div_le_div_of_nonneg_right (sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

/-- Relabelling by a bijection preserves averages. -/
theorem uexp_comp_equiv (e : Ω ≃ α) (F : α → ℝ) : uexp (fun ω => F (e ω)) = uexp F := by
  simp only [uexp, Fintype.card_congr e]
  rw [Fintype.sum_equiv e _ _ (fun _ => rfl)]

/-- Fubini for averages: the average over a product is the average over the first
coordinate of the averages of the sections. -/
theorem uexp_prod (F : α × β → ℝ) : uexp F = uexp (fun a => uexp (fun b => F (a, b))) := by
  simp only [uexp, Fintype.card_prod, Fintype.sum_prod_type, ← sum_div, Nat.cast_mul, div_div,
    mul_comm]

/-- A function of the first coordinate has the same average on the product. -/
theorem uexp_fst [Nonempty β] (F : α → ℝ) : uexp (fun z : α × β => F z.1) = uexp F := by
  rw [uexp_prod]
  simp only [uexp_const]

/-- The probability of an event is the average of its indicator (decidability supplied
classically). -/
theorem uprob_eq_uexp_ite (p : Ω → Prop) [DecidablePred p] :
    uprob p = uexp (fun ω => if p ω then (1 : ℝ) else 0) :=
  uprob_eq_uexp p

/-- An event of probability one holds everywhere. -/
theorem forall_of_uprob_eq_one {p : Ω → Prop} (h : uprob p = 1) (ω : Ω) : p ω := by
  classical
  rw [uprob_eq_card_filter] at h
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    intro h0; rw [h0, div_zero] at h; exact zero_ne_one h
  have hcard : (univ.filter p).card = Fintype.card Ω := by
    have := (div_eq_one_iff_eq hc).1 h
    exact_mod_cast this
  have := Finset.eq_univ_of_card _ hcard
  have hω : ω ∈ univ.filter p := by rw [this]; exact mem_univ ω
  exact (mem_filter.1 hω).2

/-- An event that holds everywhere on a nonempty type has probability one. -/
theorem uprob_eq_one_of_forall [Nonempty Ω] {p : Ω → Prop} (h : ∀ ω, p ω) : uprob p = 1 := by
  have : p = fun _ => True := funext fun ω => propext ⟨fun _ => trivial, fun _ => h ω⟩
  rw [this, uprob_true]

/-- Independent events on a product: the probability that the first coordinate satisfies
`p` and the second satisfies `q` is the product of the probabilities. -/
theorem uprob_prod_and (p : α → Prop) (q : β → Prop) :
    uprob (fun z : α × β => p z.1 ∧ q z.2) = uprob p * uprob q := by
  classical
  rw [uprob_prod, uprob_eq_uexp_ite p, mul_comm, ← uexp_const_mul]
  congr 1
  funext a
  by_cases ha : p a
  · simp only [ha, true_and, if_true, mul_one]
  · simp only [ha, false_and, if_false, mul_zero]
    exact uprob_false

/-- If a function is at least `b` on an event and nonnegative everywhere, its average is
at least `b` times the probability of the event. -/
theorem uprob_mul_le_uexp {G : Ω → Prop} {q : Ω → ℝ} {b : ℝ} (hq : ∀ ω, 0 ≤ q ω)
    (hG : ∀ ω, G ω → b ≤ q ω) : uprob G * b ≤ uexp q := by
  classical
  rw [uprob_eq_uexp_ite G, mul_comm, ← uexp_const_mul]
  refine uexp_mono fun ω => ?_
  by_cases h : G ω
  · simpa [h] using hG ω h
  · simpa [h] using hq ω

/-- The good-set argument: if a `[0, 1]`-valued function has average at least `c + ε`,
with `c, ε ≥ 0`, then the points where it is at least `c + ε / 2` have probability at
least `ε / 2`. [Gar26, §2.5.1], the claim `Pr[x ∈ G] ≥ ε(n) / 2` (stated there for
`c = 3/4` and, "with an identical argument", for `c = 1/2`).

**Proof sketch.** Bound the function by `1` on the good set and by `c + ε / 2` off it:
its average is at most `Pr[G] + c + ε / 2`, so `Pr[G] ≥ ε / 2`. -/
theorem half_le_uprob_threshold [Nonempty α] (q : α → ℝ) (hq : ∀ a, q a ≤ 1) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 ≤ ε) (h : c + ε ≤ uexp q) :
    ε / 2 ≤ uprob (fun a => c + ε / 2 ≤ q a) := by
  classical
  have hpt : ∀ a, q a ≤ (if c + ε / 2 ≤ q a then (1 : ℝ) else 0) + (c + ε / 2) := by
    intro a
    by_cases ha : c + ε / 2 ≤ q a
    · simp only [ha, if_true]; linarith [hq a]
    · simp only [ha, if_false, zero_add]; linarith
  have h1 := uexp_mono hpt
  rw [uexp_add, uexp_const, ← uprob_eq_uexp_ite] at h1
  linarith

/-! ### Maps pushing uniform to uniform -/

/-- The map `π` pushes the uniform distribution on `Ω` forward to the uniform distribution
on `γ`: every average over `γ` equals the average of its composite with `π`. -/
def PushesUniform (π : Ω → γ) : Prop :=
  ∀ F : γ → ℝ, uexp (fun ω => F (π ω)) = uexp F

/-- A map pushing uniform to uniform preserves the probability of every event. -/
theorem PushesUniform.uprob_eq {π : Ω → γ} (h : PushesUniform π) (p : γ → Prop) :
    uprob (fun ω => p (π ω)) = uprob p := by
  classical
  rw [uprob_eq_uexp_ite, uprob_eq_uexp_ite]
  exact h (fun c => if p c then 1 else 0)

/-- Maps pushing uniform to uniform compose. -/
theorem PushesUniform.comp {π : Ω → γ} {σ : γ → δ} (hπ : PushesUniform π)
    (hσ : PushesUniform σ) : PushesUniform (fun ω => σ (π ω)) := fun F => by
  rw [hπ (fun c => F (σ c)), hσ F]

/-- A bijection pushes uniform to uniform. -/
theorem pushesUniform_equiv (e : Ω ≃ γ) : PushesUniform e := uexp_comp_equiv e

/-- The identity pushes uniform to uniform. -/
theorem pushesUniform_id : PushesUniform (fun ω : Ω => ω) := fun _ => rfl

/-- Translation `a ↦ a + e` in a finite additive group pushes uniform to uniform. -/
theorem pushesUniform_add_right {G : Type*} [AddGroup G] [Fintype G] (e : G) :
    PushesUniform (fun a : G => a + e) :=
  pushesUniform_equiv (Equiv.addRight e)

/-- The first projection pushes uniform to uniform. -/
theorem pushesUniform_fst [Nonempty β] : PushesUniform (Prod.fst : α × β → α) := uexp_fst

/-- The second projection pushes uniform to uniform. -/
theorem pushesUniform_snd [Nonempty α] : PushesUniform (Prod.snd : α × β → β) :=
  (pushesUniform_equiv (Equiv.prodComm α β)).comp pushesUniform_fst

/-- A product of maps pushing uniform to uniform pushes uniform to uniform: the
coordinates of a uniform pair are independent.

**Proof sketch.** Fubini over `Ω × Ω'`, push the inner average along the second map,
then the outer one along the first, and Fubini back. -/
theorem PushesUniform.prodMap {π₁ : Ω → γ} {π₂ : Ω' → δ} (h₁ : PushesUniform π₁)
    (h₂ : PushesUniform π₂) : PushesUniform (fun z : Ω × Ω' => (π₁ z.1, π₂ z.2)) := fun F => by
  rw [uexp_prod, uexp_prod F]
  have h : ∀ a, uexp (fun b => F (π₁ a, π₂ b)) = uexp (fun d => F (π₁ a, d)) :=
    fun a => h₂ (fun d => F (π₁ a, d))
  exact (congrArg uexp (funext h)).trans (h₁ (fun c => uexp fun d => F (c, d)))

/-- Evaluating a uniform function `ι → γ` at a point gives a uniform value. -/
theorem pushesUniform_eval {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    PushesUniform (fun ω : ι → γ => ω i) := by
  rcases isEmpty_or_nonempty γ with hγ | hγ
  · intro F
    haveI : IsEmpty (ι → γ) := ⟨fun ω => hγ.false (ω i)⟩
    show uexp _ = uexp _
    simp only [uexp, univ_eq_empty, sum_empty, zero_div]
  · have h := (pushesUniform_equiv (Equiv.funSplitAt i γ)).comp
      (pushesUniform_fst (α := γ) (β := {j // j ≠ i} → γ))
    exact h

/-- Evaluating a uniform function `ι → γ` at two distinct points gives a uniform pair: the
coordinates of a uniform tuple are pairwise independent and uniform. -/
theorem pushesUniform_eval_pair {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) : PushesUniform (fun ω : ι → γ => (ω i, ω j)) := by
  have h₂ : PushesUniform (fun z : γ × ({k // k ≠ i} → γ) => (z.1, z.2 ⟨j, hij.symm⟩)) :=
    (pushesUniform_equiv (Equiv.refl γ)).prodMap (pushesUniform_eval _)
  exact (pushesUniform_equiv (Equiv.funSplitAt i γ)).comp h₂

/-- A surjective homomorphism of finite additive groups pushes uniform to uniform: all its
fibres have the same size.

**Proof sketch.** Group the sum over the domain by fibres; every fibre has the size of the
kernel, so both the sum and the cardinality of the domain pick up the same factor. -/
theorem pushesUniform_of_surjective {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G]
    [Fintype H] (φ : G →+ H) (hφ : Function.Surjective φ) : PushesUniform φ := by
  classical
  intro F
  have hfib : ∀ h : H, #{g | φ g = h} = #{g | φ g = 0} := fun h =>
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hφ h) ⟨0, map_zero φ⟩
  have hsum : ∑ g, F (φ g) = (#{g | φ g = 0} : ℝ) * ∑ h, F h := by
    rw [← Finset.sum_fiberwise' univ φ F, mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_const, nsmul_eq_mul, hfib]
  have hcard : Fintype.card G = #{g | φ g = 0} * Fintype.card H := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := φ) (t := univ) (fun _ _ => mem_univ _)]
    simp only [hfib, sum_const, card_univ, smul_eq_mul, mul_comm]
  have hpos : (#{g | φ g = 0} : ℝ) ≠ 0 := by
    have : (0 : G) ∈ ({g | φ g = 0} : Finset G) := by simp
    exact_mod_cast (Finset.card_pos.2 ⟨0, this⟩).ne'
  simp only [uexp, hsum, hcard, Nat.cast_mul]
  rw [mul_div_mul_left _ _ hpos]

end TCSlib.Cryptography.HardcoreBit
