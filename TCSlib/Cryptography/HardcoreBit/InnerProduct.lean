/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.HardcoreBit.Basic
import Mathlib.Algebra.Ring.BooleanRing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin setting and the perfect predictor

The setting of [Gar26, Theorem 2.3]: from `f` on `n`-bit strings build
`g(x, r) = f(x) ‖ r` with the candidate hard-concentrate bit `B(x, r) = ⟨x, r⟩ mod 2`.
Bit strings are `Fin n → Bool`, and `Bool` carries Mathlib's Boolean-ring structure, in
which addition is XOR and multiplication is AND; so `s + t` is the bitwise XOR `s ⊕ t`
and `⟨x, r⟩ = ∑ᵢ xᵢ rᵢ` is the inner product mod 2.

This file sets up what the three cases of the proof share: inverters for `g` that keep
`r` and recover `x` from `f(x)` (`glInverter`), the reduction of the inversion probability
to the recovery probability (`le_invProb_of_good`), and the good set of inputs `x`
(`half_le_uprob_good`). It then proves the "super simple case": a perfect predictor
gives a perfect inverter.

## Main definitions

* `ip x r`: the inner product `⟨x, r⟩ mod 2`.
* `glPad f`: the function `g(x, r) = f(x) ‖ r`; `glBit`: the bit `B(x, r) = ⟨x, r⟩`.
* `glInverter R`: the inverter of `g` that outputs `R(f(x)) ‖ r` on `f(x) ‖ r`.
* `secProb f A x`: the probability, for fixed `x`, that `A` predicts `⟨x, r⟩` from
  `f(x) ‖ r` over uniform `r` and coins.
* `perfectInverter A`: the inverter of [Gar26, Figure 2.3].

## Main results

* `ip_add`, `ip_single`, `ip_sum`: linearity of the inner product, and
  `⟨x, eᵢ⟩ = xᵢ`; `pushesUniform_xor`: `a ⊕ e` is uniform for uniform `a`.
* `predProb_glPad_eq`: the prediction probability is the average of `secProb` over `x`.
* `half_le_uprob_good`: the good set has probability at least `ε / 2`.
* `le_invProb_of_good`: recovery bounds on a good set give inversion bounds.
* `invProb_perfectInverter`: [Gar26, Theorem 2.3, super simple case].

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1, Theorem 2.3 and Figure 2.3.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

variable {n : ℕ} {β γ ρ : Type*} [Fintype γ] [Fintype ρ]

/-! ### The inner product -/

/-- The inner product `⟨x, r⟩ = ∑ᵢ xᵢ rᵢ mod 2` of two bit strings, computed in the
Boolean ring `Bool` (XOR of the ANDs). [Gar26, Theorem 2.3], the bit `B(x, r)`. -/
def ip (x r : Fin n → Bool) : Bool := ∑ i, x i * r i

/-- The inner product is additive in its second argument: `⟨x, s ⊕ t⟩ = ⟨x, s⟩ ⊕ ⟨x, t⟩`. -/
theorem ip_add (x s t : Fin n → Bool) : ip x (s + t) = ip x s + ip x t := by
  simp only [ip, Pi.add_apply, mul_add, sum_add_distrib]

/-- The inner product with the unit vector `eᵢ` extracts the `i`-th bit: `⟨x, eᵢ⟩ = xᵢ`.
[Gar26, §2.5.1, super simple case]. -/
theorem ip_single (x : Fin n → Bool) (i : Fin n) : ip x (Pi.single i true) = x i := by
  simp only [ip]
  rw [sum_eq_single i]
  · simp only [Pi.single_eq_same]; exact mul_one _
  · intro j _ hj; simp only [Pi.single_eq_of_ne hj]; exact mul_zero _
  · intro h; exact absurd (mem_univ i) h

/-- The inner product with a sum of strings is the sum of the inner products:
`⟨x, ⊕_{j ∈ L} s_j⟩ = ⊕_{j ∈ L} ⟨x, s_j⟩`. [Gar26, §2.5.1, real case], the computation
`B(x, S_L) = ∑_{j ∈ L} B(x, s_j)`. -/
theorem ip_sum {κ : Type*} (x : Fin n → Bool) (L : Finset κ) (s : κ → Fin n → Bool) :
    ip x (∑ j ∈ L, s j) = ∑ j ∈ L, ip x (s j) := by
  simp only [ip, Finset.sum_apply, mul_sum]
  exact sum_comm

/-- XOR with a fixed string, `a ↦ a ⊕ e`, is a bijection of bit strings, so it maps a
uniform string to a uniform string. -/
theorem pushesUniform_xor (e : Fin n → Bool) : PushesUniform (fun a : Fin n → Bool => a + e) :=
  pushesUniform_equiv
    { toFun := fun a => a + e
      invFun := fun a => a + e
      left_inv := fun a => funext fun j => by
        simp only [Pi.add_apply]; cases a j <;> cases e j <;> rfl
      right_inv := fun a => funext fun j => by
        simp only [Pi.add_apply]; cases a j <;> cases e j <;> rfl }

/-! ### The function `g`, its bit, and inverters keeping `r` -/

/-- The function `g(x, r) = f(x) ‖ r` of [Gar26, Theorem 2.3]. -/
def glPad (f : (Fin n → Bool) → β) (z : (Fin n → Bool) × (Fin n → Bool)) :
    β × (Fin n → Bool) :=
  (f z.1, z.2)

/-- The candidate hard-concentrate bit `B(x, r) = ⟨x, r⟩ mod 2` of [Gar26, Theorem 2.3]. -/
def glBit (z : (Fin n → Bool) × (Fin n → Bool)) : Bool := ip z.1 z.2

/-- The inverter of `g` built from a recovery procedure `R`: on `f(x) ‖ r` with coins `c`
it outputs `R(f(x), c) ‖ r`. All three inverters of [Gar26, §2.5.1] have this form. -/
def glInverter (R : β → γ → Fin n → Bool) (y : β × (Fin n → Bool)) (c : γ) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (R y.1 c, y.2)

/-- The probability, for a fixed `x`, that the predictor `A` outputs `⟨x, r⟩` on
`f(x) ‖ r`, over uniform `r` and coins: the quantity `Pr_r[E]` defining the good set `G`
in [Gar26, §2.5.1]. -/
noncomputable def secProb (f : (Fin n → Bool) → β) (A : β × (Fin n → Bool) → ρ → Bool)
    (x : Fin n → Bool) : ℝ :=
  uprob fun z : (Fin n → Bool) × ρ => A (f x, z.1) z.2 = ip x z.1

/-- The prediction probability of `A` for the bit `B` of `g` is the average over `x` of the
probabilities `secProb f A x`. -/
theorem predProb_glPad_eq (f : (Fin n → Bool) → β) (A : β × (Fin n → Bool) → ρ → Bool) :
    predProb (glPad f) glBit A = uexp (secProb f A) := by
  unfold predProb secProb
  have h := uprob_prod
    (fun z : (Fin n → Bool) × ((Fin n → Bool) × ρ) => A (f z.1, z.2.1) z.2.2 = ip z.1 z.2.1)
  simp only at h
  rw [← h]
  exact uprob_comp_equiv (Equiv.prodAssoc _ _ _)
    (fun z : (Fin n → Bool) × ((Fin n → Bool) × ρ) => A (f z.1, z.2.1) z.2.2 = ip z.1 z.2.1)

/-- The good set is large: if `A` predicts `B` with probability at least `c + ε`
(`c, ε ≥ 0`), then `secProb f A x ≥ c + ε / 2` for a set of `x` of probability at least
`ε / 2`. [Gar26, §2.5.1], the claim `Pr[x ∈ G] ≥ ε(n)/2`, for `c = 3/4` (simple case) and
`c = 1/2` (real case). -/
theorem half_le_uprob_good (f : (Fin n → Bool) → β) (A : β × (Fin n → Bool) → ρ → Bool)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (h : c + ε ≤ predProb (glPad f) glBit A) :
    ε / 2 ≤ uprob (fun x => c + ε / 2 ≤ secProb f A x) := by
  rw [predProb_glPad_eq] at h
  exact half_le_uprob_threshold _ (fun x => uprob_le_one _) hc hε h

/-- Recovering `x` exactly inverts `g`: the inversion probability of `glInverter R` is at
least the probability that `R(f(x), c) = x` over uniform `x` and coins `c`. -/
theorem uprob_recover_le_invProb (f : (Fin n → Bool) → β) (R : β → γ → Fin n → Bool) :
    uprob (fun z : (Fin n → Bool) × γ => R (f z.1) z.2 = z.1) ≤
      invProb (glPad f) (glInverter R) := by
  let e : ((Fin n → Bool) × (Fin n → Bool)) × γ ≃ ((Fin n → Bool) × γ) × (Fin n → Bool) :=
    { toFun := fun w => ((w.1.1, w.2), w.1.2)
      invFun := fun z => ((z.1.1, z.2), z.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := uprob_comp_equiv e
    (fun z : ((Fin n → Bool) × γ) × (Fin n → Bool) => R (f z.1.1) z.1.2 = z.1.1)
  rw [uprob_fst (fun z : (Fin n → Bool) × γ => R (f z.1) z.2 = z.1)] at h
  rw [← h]
  refine uprob_mono fun w hw => ?_
  simp only [glPad, glInverter]
  simp only [e, Equiv.coe_fn_mk] at hw
  rw [hw]

/-- Inversion from recovery on a good set: if the good set `G` has probability at least
`a`, and for every `x ∈ G` the procedure `R` recovers `x` from `f(x)` with probability at
least `b ≥ 0`, then `glInverter R` inverts `g` with probability at least `a · b`.
[Gar26, §2.5.1], the final step `Pr[B inverts] ≥ Pr[x ∈ G] · Pr[x' = x | x ∈ G]` of the
simple and real cases.

**Proof sketch.** Bound the inversion probability below by the recovery probability,
split it over `x` (Fubini), and keep only the contribution of `x ∈ G`. -/
theorem le_invProb_of_good (f : (Fin n → Bool) → β) (R : β → γ → Fin n → Bool)
    {G : (Fin n → Bool) → Prop} {a b : ℝ} (hG : a ≤ uprob G) (hb : 0 ≤ b)
    (hR : ∀ x, G x → b ≤ uprob (fun c => R (f x) c = x)) :
    a * b ≤ invProb (glPad f) (glInverter R) := by
  refine le_trans ?_ (uprob_recover_le_invProb f R)
  rw [uprob_prod]
  exact (mul_le_mul_of_nonneg_right hG hb).trans
    (uprob_mul_le_uexp (fun x => uprob_nonneg _) hR)

/-- Union bound over the bits: the probability of recovering all of `x` is at least one
minus the sum over `i` of the probabilities that bit `i` is wrong. -/
theorem one_sub_sum_le_uprob_eq [Nonempty γ] (R : γ → Fin n → Bool) (x : Fin n → Bool) :
    1 - ∑ i, uprob (fun c => R c i ≠ x i) ≤ uprob (fun c => R c = x) := by
  have h1 : uprob (fun c => ¬ R c = x) ≤ ∑ i, uprob (fun c => R c i ≠ x i) := by
    refine (uprob_mono fun c hc => ?_).trans (uprob_exists_le univ fun i c => R c i ≠ x i)
    by_contra h
    push_neg at h
    exact hc (funext fun i => h i (mem_univ i))
  rw [uprob_not] at h1
  linarith

/-! ### The super simple case -/

/-- The recovery procedure of [Gar26, Figure 2.3]: the `i`-th bit is `A(f(x) ‖ eᵢ)`, where
`eᵢ` is the `i`-th unit vector. It makes `n` calls to `A`, each with fresh coins `c i`,
and no other computation. -/
def perfectRecover (A : β × (Fin n → Bool) → ρ → Bool) (y : β) (c : Fin n → ρ) :
    Fin n → Bool :=
  fun i => A (y, Pi.single i true) (c i)

/-- The inverter of [Gar26, Figure 2.3]: on `f(x) ‖ r` it outputs
`A(f(x) ‖ e₁) ⋯ A(f(x) ‖ eₙ) ‖ r`, using `n` calls to `A` with fresh coins. -/
def perfectInverter (A : β × (Fin n → Bool) → ρ → Bool) :
    β × (Fin n → Bool) → (Fin n → ρ) → (Fin n → Bool) × (Fin n → Bool) :=
  glInverter (perfectRecover A)

/-- The super simple case of Goldreich–Levin: if `A` predicts `B(x, r) = ⟨x, r⟩` from
`g(x, r) = f(x) ‖ r` with probability `1`, then `perfectInverter A` inverts `g` with
probability `1`. [Gar26, Theorem 2.3, super simple case].

**Proof sketch.** Probability one on a finite space means `A` is right on every input and
every coin string, in particular on `f(x) ‖ eᵢ`, where the right answer is
`⟨x, eᵢ⟩ = xᵢ`. So the inverter recovers `x` exactly, always. -/
theorem invProb_perfectInverter (f : (Fin n → Bool) → β) (A : β × (Fin n → Bool) → ρ → Bool)
    (h : predProb (glPad f) glBit A = 1) : invProb (glPad f) (perfectInverter A) = 1 := by
  have hA := forall_of_uprob_eq_one h
  have hρ : Nonempty ρ := by
    by_contra hρ
    rw [not_nonempty_iff] at hρ
    have : uprob (fun z : ((Fin n → Bool) × (Fin n → Bool)) × ρ =>
        A (glPad f z.1) z.2 = glBit z.1) = 0 := by
      classical
      rw [uprob_eq_card_filter]; simp
    unfold predProb at h
    rw [this] at h
    exact zero_ne_one h
  refine le_antisymm (uprob_le_one _) ?_
  refine le_of_eq_of_le ?_ (uprob_recover_le_invProb f (perfectRecover A))
  refine (uprob_eq_one_of_forall fun z => funext fun i => ?_).symm
  have := hA ((z.1, Pi.single i true), z.2 i)
  simpa only [glPad, glBit, ip_single] using this

end TCSlib.Cryptography.HardcoreBit
