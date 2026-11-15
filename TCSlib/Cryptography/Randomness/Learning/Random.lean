/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.Learning.Law
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# With a random function, no learner predicts better than `½ ± m/2^n`

Step 2 of [PS10, Theorem 179.1, proof]: in the game with a uniform random function
`R : {0,1}^n → {0,1}^n` in place of the keyed family, every learner `ℓ` predicts the first bit of
`R x` with probability within `m/2^n` of `½`, for `n ≥ 1` (`abs_gameProb_random_sub_half_le`).

**Proof.** Fix the examples `s`, the coins `r` and the fresh point `x`. If `x` is none of the
examples, flipping the first bit of `R x` (`flipAt`, an involution of the random functions) keeps
the labelled examples and negates the label of `x`, so it exchanges the winning and the losing
functions: the probability over `R` is exactly `½` (`uprob_flip_half`). Otherwise the probability
is between `0` and `1`. So the game probability is within `Pr[x ∈ s]` of `½`, and
`Pr[x ∈ s] ≤ Σ_j Pr[x = s_j] = m · 2^{-n}` (`uprob_exists_le`, `uprob_eq_point`).

## Main definitions

* `LearnPRF.flip0`, `LearnPRF.flipAt`: flipping the first bit of a string, and of a function's
  value at a point.

## Main results

* `LearnPRF.firstBit_flip0`, `LearnPRF.flipAt_involutive`.
* `LearnPRF.uprob_flip_half`: at a fresh point, the prediction wins with probability `½`.
* `LearnPRF.uprob_eq_point`: a uniform point hits a given point with probability `2^{-n}`.
* `LearnPRF.abs_gameProb_random_sub_half_le`: the bound `|gameProb − ½| ≤ m/2^n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity TCSlib.Cryptography TCSlib.LearningTheory.PAC Finset

section Random

variable {n : ℕ} (hn : 0 < n)

/-- **Flipping the first bit** of an `n`-bit string (`n ≥ 1`):
`flip0 hn y = update y 0 (!y 0)`. -/
def flip0 (y : Fin n → Bool) : Fin n → Bool := Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)

/-- `flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)`. -/
theorem flip0_eq (y : Fin n → Bool) : flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩) := rfl

/-- Flipping twice is the identity: `flip0 hn (flip0 hn y) = y`. -/
theorem flip0_flip0 (y : Fin n → Bool) : flip0 hn (flip0 hn y) = y := by
  rw [flip0_eq, flip0_eq, Function.update_self, Function.update_idem, Bool.not_not,
    Function.update_eq_self]

/-- The first bit of an `n`-bit string with `n ≥ 1` is its bit `0`:
`firstBit y = y ⟨0, hn⟩`. -/
theorem firstBit_of_pos (y : Fin n → Bool) : firstBit y = y ⟨0, hn⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [firstBit_eq, List.ofFn_succ, List.headD_cons]
  rfl

/-- Flipping the first bit negates it: `firstBit (flip0 hn y) = !firstBit y`. -/
theorem firstBit_flip0 (y : Fin n → Bool) : firstBit (flip0 hn y) = !firstBit y := by
  rw [firstBit_of_pos hn, firstBit_of_pos hn, flip0_eq, Function.update_self]

/-- **Flipping the first bit of a function's value at `x`:**
`flipAt hn x R = update R x (flip0 hn (R x))`. -/
def flipAt (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    (Fin n → Bool) → (Fin n → Bool) :=
  Function.update R x (flip0 hn (R x))

/-- `flipAt hn x R = Function.update R x (flip0 hn (R x))`. -/
theorem flipAt_eq (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    flipAt hn x R = Function.update R x (flip0 hn (R x)) := rfl

/-- `flipAt hn x` is an involution: `flipAt hn x (flipAt hn x R) = R`. -/
theorem flipAt_involutive (x : Fin n → Bool) : Function.Involutive (flipAt hn x) := by
  intro R
  rw [flipAt_eq, flipAt_eq, Function.update_self, flip0_flip0, Function.update_idem,
    Function.update_eq_self]

include hn in
/-- **At a fresh point the prediction wins with probability `½`:** if `x` is none of the
examples `s`, then for every learner `ℓ` and coins `r`, the uniform probability over `R` that
`ℓ (label (firstBit ∘ R) s) r x == firstBit (R x)` is `½`.

**Proof sketch.** `flipAt hn x` is a bijection of the functions (`flipAt_involutive`), so it
preserves the probability (`uprob_comp_equiv`). It keeps the labels of the examples
(`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`), so it maps the event to
its complement; hence `p = 1 − p` (`uprob_not`). -/
theorem uprob_flip_half {m : ℕ} {ρ : Type*}
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) (s : Fin m → Fin n → Bool)
    (r : ρ) (x : Fin n → Bool) (hx : ∀ j, s j ≠ x) :
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true) = 1 / 2 := by
  set σ := Function.Involutive.toPerm (flipAt hn x) (flipAt_involutive hn x) with hσ
  have h1 := uprob_comp_equiv σ (fun R =>
    (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true)
  have h2 : (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (σ R z)) s) r x ==
        firstBit (σ R x)) = true) =
      fun R => ¬ (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true := by
    funext R
    have hl : label (fun z => firstBit (σ R z)) s =
        label (fun z => firstBit (R z)) s := by
      funext j
      rw [label_apply, label_apply, hσ, Function.Involutive.coe_toPerm, flipAt_eq,
        Function.update_of_ne (hx j)]
    rw [hl, hσ, Function.Involutive.coe_toPerm, flipAt_eq, Function.update_self, firstBit_flip0]
    cases ℓ (label (fun z => firstBit (R z)) s) r x <;> cases firstBit (R x) <;> decide
  rw [h2, uprob_not] at h1
  linarith

/-- **A uniform point hits a given point with probability `2^{-n}`:**
`uprob (fun x : {0,1}^n => y = x) = 1 / 2^n`.

**Proof sketch.** This is `OneWay.uprob_eq_one_div_card` with the equation reversed and
`|{0,1}^n| = 2^n`. -/
theorem uprob_eq_point (y : Fin n → Bool) :
    uprob (fun x : Fin n → Bool => y = x) = 1 / 2 ^ n := by
  rw [show (fun x : Fin n → Bool => y = x) = (fun x => x = y) from
      funext fun _ => propext eq_comm, OneWay.uprob_eq_one_div_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_two]

include hn in
/-- **With a random function the prediction is within `m/2^n` of `½`** [PS10, Theorem 179.1,
proof, step 2]: for `n ≥ 1`, every learner `ℓ` and `m` examples,
`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`.

**Proof sketch.** Put the function last (`uprob_comp_equiv`) and average over it first
(`uprob_prod`): for fixed `((s, r), x)` the probability `p` is `½` when `x` is fresh
(`uprob_flip_half`) and in `[0, 1]` otherwise, so `|p − ½| ≤ [x ∈ s]`. Averaging (the
coupling bound `MultiMsg.abs_uexp_sub_le_uprob` against the constant `½`),
`|gameProb − ½| ≤ Pr[∃ j, s_j = x]`, which the union bound (`uprob_exists_le`) bounds by
`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`, `OneWay.uexp_const`). -/
theorem abs_gameProb_random_sub_half_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m : ℕ)
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
    |gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ - 1 / 2| ≤ m / 2 ^ n := by
  classical
  -- the random function last
  let e : (((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) × ((Fin n → Bool) → (Fin n → Bool)) ≃
      (((Fin n → Bool) → (Fin n → Bool)) × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) :=
    { toFun := fun w => ((w.2, w.1.1), w.1.2)
      invFun := fun w => ((w.1.2, w.2), w.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  set p : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → ℝ := fun t =>
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) t.1.1) t.1.2 t.2 == firstBit (R t.2)) = true) with hp
  have hgame : gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ = uexp p := by
    rw [gameProb_eq, ← uprob_comp_equiv e, uprob_prod]
    rfl
  -- the bad event: the fresh point is an example
  set bad : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → Prop :=
    fun t => ∃ j ∈ (Finset.univ : Finset (Fin m)), t.1.1 j = t.2 with hbad
  -- the coupling bound against the constant `½`: off the bad event, `p = ½`
  have hdev : |uexp p - 1 / 2| ≤ uprob bad := by
    have h := MultiMsg.abs_uexp_sub_le_uprob p (fun _ => 1 / 2) bad
      (fun _ => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun _ => ⟨by norm_num, by norm_num⟩)
      (fun t hb => uprob_flip_half hn ℓ t.1.1 t.1.2 t.2 fun j hj => hb ⟨j, Finset.mem_univ j, hj⟩)
    rwa [OneWay.uexp_const] at h
  -- the union bound
  have hj : ∀ j : Fin m, uprob (fun t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) =>
      t.1.1 j = t.2) = 1 / 2 ^ n := by
    intro j
    rw [uprob_prod]
    simp only [uprob_eq_point, OneWay.uexp_const]
  have hunion := uprob_exists_le (Finset.univ : Finset (Fin m))
    (fun j (t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) => t.1.1 j = t.2)
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
  rw [hgame]
  refine hdev.trans (hunion.trans (le_of_eq ?_))
  ring

end Random

end TCSlib.Cryptography.Randomness.LearnPRF
