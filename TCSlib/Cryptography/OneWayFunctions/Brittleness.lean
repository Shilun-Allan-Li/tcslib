/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Robustness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Brittleness: composing and truncating one-way functions

[Gar26, §2.2.2] gives two operations that do not preserve one-wayness.

1. *Self-composition.* From `g` build `f(x₁, x₂) = 0ⁿ‖g(x₁)`. Then `f ∘ f` is the
   constant `0ⁿ‖g(0ⁿ)`, inverted with probability one by any adversary
   (`invProb_zeroPrefix_comp_self`), while an inverter of `f` gives an inverter of `g`
   with exactly the same success (`invProb_zeroPrefixInverter`).
2. *Dropping a bit (Claims 2.1 and 2.2).* From `h` build
   `g(x‖y) = 0ⁿ‖y` if `x = 0ⁿ` and `1‖0ⁿ⁻¹‖h(y)` otherwise. An inverter of `g` gives an
   inverter of `h` losing at most `2⁻ⁿ - 2⁻²ⁿ` (`invProb_flagged_le`), while `g` without
   its first output bit is inverted with probability one (`invProb_dropFirst_flagged`).

Bit strings of length `n` are `Fin n → Bool`; a string `x₁‖x₂` of two halves is a pair,
and the first `n` output bits of the dropped-bit example are split as the first bit and
the remaining `n - 1 = m` bits, so `n = m + 1`.

## Main definitions

* `zeroPrefix g`: the function `(x₁, x₂) ↦ 0ⁿ‖g(x₁)`.
* `zeroPrefixInverter A`: the inverter of `g` built from an inverter of `zeroPrefix g`.
* `flagged h`: the function `g` of Claim 2.1.
* `flaggedInverter A`: the inverter `B` of `h` from the proof of Claim 2.2.

## Main results

* `invProb_zeroPrefix_comp_self`, `invProb_zeroPrefixInverter`: the composition example.
* `zeroPatch_zeroPrefix`: `zeroPrefix g` also refutes the example of §2.2.1.
* `invProb_flagged_le`: [Gar26, Claim 2.2].
* `invProb_dropFirst_flagged`: [Gar26, Claim 2.1, Step 3].

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.2.2 (Claims 2.1 and 2.2).
-/

namespace TCSlib.Cryptography.OneWay

open Finset TCSlib.Cryptography

variable {ρ : Type*} [Fintype ρ] {n m : ℕ}

/-- The all-zero bit string `0ⁿ`. -/
def zeros (n : ℕ) : Fin n → Bool := fun _ => false

/-! ### Self-composition -/

/-- The function `f(x₁, x₂) = 0ⁿ‖g(x₁)` on pairs of `n`-bit strings. [Gar26, §2.2.2,
"OWFs do not always compose securely"]. -/
def zeroPrefix (g : (Fin n → Bool) → (Fin n → Bool)) (x : (Fin n → Bool) × (Fin n → Bool)) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (zeros n, g x.1)

/-- `f ∘ f` is the constant `0ⁿ‖g(0ⁿ)`. [Gar26, §2.2.2, observation 1]. Deviation: the
source says `f ∘ f` is the constant `0^{2n}`, which holds only when `g(0ⁿ) = 0ⁿ`. -/
theorem zeroPrefix_comp_self (g : (Fin n → Bool) → (Fin n → Bool))
    (x : (Fin n → Bool) × (Fin n → Bool)) :
    zeroPrefix g (zeroPrefix g x) = (zeros n, g (zeros n)) := rfl

/-- `f ∘ f` is not one-way: the adversary that ignores its input and outputs `(0ⁿ, 0ⁿ)`
(any fixed input would do) inverts it with probability one. [Gar26, §2.2.2,
observation 1]. -/
theorem invProb_zeroPrefix_comp_self [Nonempty ρ] (g : (Fin n → Bool) → (Fin n → Bool)) :
    invProb (zeroPrefix g ∘ zeroPrefix g) (fun _ (_ : ρ) => (zeros n, zeros n)) = 1 := by
  unfold invProb
  simp only [Function.comp, zeroPrefix_comp_self]
  exact uprob_true

/-- The inverter of `g` from an inverter `A` of `zeroPrefix g`: on input `y`, run `A` on
`0ⁿ‖y` and output the first half `x₁` of its answer. [Gar26, §2.2.2, "Description of
B"]. Deviation: the source says `B` outputs the "lower-order" `n` bits, but with
`f(x₁, x₂) = 0ⁿ‖g(x₁)` the relevant half is `x₁`, and its displayed computation writes
`g(x₂)` for `g(x₁)`; this is the consistent version.

Cost: one call to `A` with the same coins, prepending `n` zeros, and projecting. -/
def zeroPrefixInverter (A : (Fin n → Bool) × (Fin n → Bool) → ρ → (Fin n → Bool) × (Fin n → Bool)) :
    (Fin n → Bool) → ρ → (Fin n → Bool) :=
  fun y r => (A (zeros n, y) r).1

/-- An inverter of `g` built from an inverter `A` of `zeroPrefix g` succeeds with exactly the
probability of `A`: `μ_{B,g}(n) = μ_{A,f}(2n)`. Hence `zeroPrefix g` is one-way when `g`
is. [Gar26, §2.2.2, observation 2].

**Proof sketch.** `A` inverts `0ⁿ‖g(x₁)` exactly when the first half of its answer is a
`g`-preimage of `g(x₁)`; this event does not depend on `x₂`, so averaging out `x₂` gives
`B`'s success probability. -/
theorem invProb_zeroPrefixInverter [Nonempty ρ] (g : (Fin n → Bool) → (Fin n → Bool))
    (A : (Fin n → Bool) × (Fin n → Bool) → ρ → (Fin n → Bool) × (Fin n → Bool)) :
    invProb g (zeroPrefixInverter A) = invProb (zeroPrefix g) A := by
  let e : ((Fin n → Bool) × (Fin n → Bool)) × ρ ≃ ((Fin n → Bool) × ρ) × (Fin n → Bool) :=
    { toFun := fun z => ((z.1.1, z.2), z.1.2)
      invFun := fun w => ((w.1.1, w.2), w.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold invProb
  rw [← uprob_fst (β := Fin n → Bool), ← uprob_comp_equiv e]
  apply uprob_congr
  rintro ⟨⟨x₁, x₂⟩, r⟩
  simp [zeroPrefix, zeroPrefixInverter, e]

/-- The function `zeroPrefix g` also refutes the robustness example of [Gar26, §2.2.1]:
its outputs all have zero first half, so by `invProb_zeroPatch_eq_one` the identity
adversary inverts `zeroPatch (zeroPrefix g)` with probability one, although
`zeroPrefix g` is one-way whenever `g` is (`invProb_zeroPrefixInverter`). -/
theorem zeroPatch_zeroPrefix [Nonempty ρ] (g : (Fin n → Bool) → (Fin n → Bool)) :
    invProb (zeroPatch (zeroPrefix g)) (fun y (_ : ρ) => y) = 1 :=
  invProb_zeroPatch_eq_one _ fun _ => rfl

/-! ### Dropping the first output bit -/

/-- The function `g` of Claim 2.1 on `2n`-bit inputs `x‖y`, with `n = m + 1`: output
`0ⁿ‖y` if `x = 0ⁿ` and `1‖0ⁿ⁻¹‖h(y)` otherwise. The first `n` output bits are split as
one bit and `m` bits. [Gar26, Claim 2.1, Step 1]. Deviation: the source writes `g(y)`
in the second case, a typo for `h(y)` (`g` is the function being defined). -/
def flagged (h : (Fin (m + 1) → Bool) → (Fin (m + 1) → Bool))
    (z : (Fin (m + 1) → Bool) × (Fin (m + 1) → Bool)) :
    Bool × (Fin m → Bool) × (Fin (m + 1) → Bool) :=
  if z.1 = zeros (m + 1) then (false, zeros m, z.2) else (true, zeros m, h z.2)

/-- Dropping the first output bit: `(b, u, v) ↦ (u, v)`. [Gar26, Claim 2.1], the
passage from `g` to `g'`. -/
def dropFirst (w : Bool × (Fin m → Bool) × (Fin (m + 1) → Bool)) :
    (Fin m → Bool) × (Fin (m + 1) → Bool) :=
  w.2

/-- `g'`, the function `g` with its first output bit dropped, is not one-way: the
adversary `C` that parses its input as `0ⁿ⁻¹‖v` and outputs `0ⁿ‖v` inverts it with
probability one. [Gar26, Claim 2.1, Step 3]. Deviation: the source writes the goal as
"an element of `g⁻¹(g(x‖y))`" where it means `g'⁻¹(g'(x‖y))`.

**Proof sketch.** Every value of `g'` has the form `0ⁿ⁻¹‖v`, and `g'(0ⁿ‖v) = 0ⁿ⁻¹‖v`. -/
theorem invProb_dropFirst_flagged [Nonempty ρ]
    (h : (Fin (m + 1) → Bool) → (Fin (m + 1) → Bool)) :
    invProb (dropFirst ∘ flagged h) (fun w (_ : ρ) => (zeros (m + 1), w.2)) = 1 := by
  have key : ∀ z, dropFirst (flagged h (zeros (m + 1), (dropFirst (flagged h z)).2)) =
      dropFirst (flagged h z) := by
    intro z
    unfold flagged dropFirst
    split_ifs <;> simp_all
  unfold invProb
  simp only [Function.comp, key]
  exact uprob_true

/-- The inverter `B` of `h` from the proof of Claim 2.2, with coins `(x, y', r)`: if
`x = 0ⁿ` output the random guess `y'`; otherwise run `A` on `1‖0ⁿ⁻¹‖v` and output the
second half `y'` of its answer. [Gar26, Claim 2.2, steps 1–3].

Cost: one call to `A` with coins `r`, sampling `2n` extra bits, and one comparison with
`0ⁿ`. -/
def flaggedInverter
    (A : Bool × (Fin m → Bool) × (Fin (m + 1) → Bool) → ρ →
      (Fin (m + 1) → Bool) × (Fin (m + 1) → Bool)) :
    (Fin (m + 1) → Bool) → ((Fin (m + 1) → Bool) × (Fin (m + 1) → Bool) × ρ) →
      (Fin (m + 1) → Bool) :=
  fun v c => if c.1 = zeros (m + 1) then c.2.1 else (A (true, zeros m, v) c.2.2).2

/-- Claim 2.2, concretely: with `N = 2ⁿ`, the inverter `B = flaggedInverter A` inverts `h`
with probability at least `μ - (1/N)(1 - 1/N)`, where `μ` is the probability that `A`
inverts `g = flagged h`. [Gar26, Claim 2.2]. Deviation: the source's middle step bounds
`B`'s success on `x ≠ 0ⁿ` by `μ` itself, which is not justified (`A`'s success on the
instances with `x = 0ⁿ` is part of `μ`); the final bound `μ - (2⁻ⁿ - 2⁻²ⁿ)` is
nevertheless correct, and is what is proved here.

**Proof sketch.** Condition on the first half `x` of `g`'s input, which is also `B`'s
coin `x`. For `x ≠ 0ⁿ`, `g(x‖y) = 1‖0ⁿ⁻¹‖h(y)` and `B` runs `A` on exactly this string;
whenever `A` inverts it, its answer has second half a preimage of `h(y)`, so `B`'s
conditional success is at least `A`'s. For `x = 0ⁿ`, `A`'s conditional success is at
most `1` while `B`'s random guess succeeds with probability at least
`Pr[y' = y] = 1/N`. Averaging over `x`, the loss is at most `(1/N)(1 - 1/N)`. -/
theorem invProb_flagged_le [Nonempty ρ]
    (h : (Fin (m + 1) → Bool) → (Fin (m + 1) → Bool))
    (A : Bool × (Fin m → Bool) × (Fin (m + 1) → Bool) → ρ →
      (Fin (m + 1) → Bool) × (Fin (m + 1) → Bool)) :
    invProb (flagged h) A - 1 / 2 ^ (m + 1) * (1 - 1 / 2 ^ (m + 1)) ≤
      invProb h (flaggedInverter A) := by
  classical
  -- Conditioning on the first half `x` of `g`'s input, and on `B`'s coin `x`.
  let P : (Fin (m + 1) → Bool) → ℝ := fun x => uprob fun w : (Fin (m + 1) → Bool) × ρ =>
    flagged h (A (flagged h (x, w.1)) w.2) = flagged h (x, w.1)
  let Q : (Fin (m + 1) → Bool) → ℝ := fun x =>
    uprob fun w : (Fin (m + 1) → Bool) × ((Fin (m + 1) → Bool) × ρ) =>
      h (flaggedInverter A (h w.1) (x, w.2.1, w.2.2)) = h w.1
  have hP : invProb (flagged h) A = uexp P := by
    unfold invProb
    rw [← uprob_comp_equiv (Equiv.prodAssoc (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ρ).symm,
      uprob_prod]
    rfl
  have hQ : invProb h (flaggedInverter A) = uexp Q := by
    let e : (Fin (m + 1) → Bool) × ((Fin (m + 1) → Bool) × ((Fin (m + 1) → Bool) × ρ)) ≃
        (Fin (m + 1) → Bool) × ((Fin (m + 1) → Bool) × ((Fin (m + 1) → Bool) × ρ)) :=
      { toFun := fun z => (z.2.1, (z.1, z.2.2))
        invFun := fun z => (z.2.1, (z.1, z.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    unfold invProb
    rw [← uprob_comp_equiv e, uprob_prod]
    rfl
  set N : ℝ := 2 ^ (m + 1) with hN
  have hcard : (Fintype.card (Fin (m + 1) → Bool) : ℝ) = N := by simp [hN]
  -- Pointwise comparison of the conditional success probabilities.
  have hpt : ∀ x, P x + (-1) * (if x = zeros (m + 1) then 1 - 1 / N else 0) ≤ Q x := by
    intro x
    by_cases hx : x = zeros (m + 1)
    · -- `x = 0ⁿ`: `B`'s random guess succeeds with probability at least `1 / N`.
      subst hx
      have hguess : 1 / N ≤ Q (zeros (m + 1)) := by
        calc 1 / N = uprob fun w : (Fin (m + 1) → Bool) × ((Fin (m + 1) → Bool) × ρ) =>
              w.2.1 = w.1 := by
              rw [uprob_prod]
              simp only
              have : ∀ y : Fin (m + 1) → Bool,
                  uprob (fun b : (Fin (m + 1) → Bool) × ρ => b.1 = y) = 1 / N := by
                intro y
                rw [uprob_fst (fun y' : Fin (m + 1) → Bool => y' = y), uprob_eq_one_div_card,
                  hcard]
              simp only [this, uexp_const]
          _ ≤ Q (zeros (m + 1)) := by
              apply uprob_mono
              rintro ⟨y, y', r⟩ hy
              simp only [flaggedInverter, if_true] at hy ⊢
              rw [hy]
      have h1 : P (zeros (m + 1)) ≤ 1 := uprob_le_one _
      simp only [if_true]
      linarith
    · -- `x ≠ 0ⁿ`: `B` runs `A` on exactly `g(x‖y)` and keeps the second half.
      simp only [hx, if_false, mul_zero, add_zero]
      have hQx : Q x = uprob fun w : (Fin (m + 1) → Bool) × ρ =>
          h (A (true, zeros m, h w.1) w.2).2 = h w.1 := by
        let e : (Fin (m + 1) → Bool) × ((Fin (m + 1) → Bool) × ρ) ≃
            ((Fin (m + 1) → Bool) × ρ) × (Fin (m + 1) → Bool) :=
          { toFun := fun z => ((z.1, z.2.2), z.2.1)
            invFun := fun w => (w.1.1, (w.2, w.1.2))
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← uprob_fst (β := Fin (m + 1) → Bool), ← uprob_comp_equiv e]
        simp only [Q, flaggedInverter, hx, if_false]
        rfl
      rw [hQx]
      apply uprob_mono
      rintro ⟨y, r⟩ hy
      simp only [flagged, hx, if_false] at hy
      revert hy
      split_ifs with h0
      · simp
      · intro hy
        simp only [Prod.mk.injEq, true_and] at hy
        exact hy
  -- Average the pointwise bound over `x`.
  have hzero : uprob (fun x : Fin (m + 1) → Bool => x = zeros (m + 1)) = 1 / N := by
    rw [uprob_eq_one_div_card, hcard]
  have havg := uexp_mono hpt
  rw [uexp_add, uexp_const_mul, uexp_indicator, hzero] at havg
  rw [hP, hQ]
  linarith

end TCSlib.Cryptography.OneWay
