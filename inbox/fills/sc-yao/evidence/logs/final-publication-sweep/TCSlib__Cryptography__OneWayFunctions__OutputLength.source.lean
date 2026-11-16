/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding and short outputs

Two facts about the shape of a one-way function.

* *Padding preserves one-wayness* [Gar26, Lemma 2.3]: `g(x, y) = f(x)‖y` is as hard to
  invert as `f`. The lemma is used to make a one-way function cheap to compute relative
  to its input length (time `n^c` becomes linear by padding with `n^c` bits); the
  running-time part belongs to the asymptotic layer, the inversion bound is here.
* *Short outputs are never one-way* [Gar26, Exercise 2.4]: a function with outputs of
  `⌊log₂ n⌋` bits has at most `n` values, so a table with one preimage per value — at
  most `n` strings of `n` bits, polynomial advice — inverts it with probability one.

## Main definitions

* `pad f`: the function `(x, y) ↦ (f x, y)`.
* `padInverter A`: the inverter of `f` built from an inverter of `pad f`.
* `tableInverter f`: the advice-table inverter of any function on a finite type.

## Main results

* `invProb_pad_le`: [Gar26, Lemma 2.3], concrete form.
* `invProb_tableInverter`: the table inverter succeeds with probability one.
* `card_log_bits_le`: `{0,1}^{⌊log₂ n⌋}` has at most `n` elements.
* `exists_inverter_log_output`: [Gar26, Exercise 2.4], concrete form.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.4 (Lemma 2.3) and Exercise 2.4.
-/

namespace TCSlib.Cryptography.OneWay

open Finset TCSlib.Cryptography

variable {α β γ ρ : Type*} [Fintype α] [Fintype γ] [Fintype ρ]

/-! ### Padding -/

/-- The padded function `g(x, y) = f(x)‖y`, which copies the padding `y` to the output.
[Gar26, Lemma 2.3, proof]. -/
def pad (f : α → β) (z : α × γ) : β × γ :=
  (f z.1, z.2)

/-- The inverter of `f` from an inverter `A` of `pad f`, with coins `(y, r)`: on input `v`,
run `A` on `v‖y` for the uniform padding `y` and output the first component (the
higher-order bits) of its answer. [Gar26, Lemma 2.3, proof, "B on input z …"].

Cost: one call to `A` with coins `r`, sampling the padding `y`, and a projection. -/
def padInverter (A : β × γ → ρ → α × γ) : β → γ × ρ → α :=
  fun v c => (A (v, c.1) c.2).1

/-- Padding preserves one-wayness: the inverter `padInverter A` inverts `f` with at least
the probability with which `A` inverts `pad f`. [Gar26, Lemma 2.3]. Deviation: the
source's displayed computation names the left-hand side `μ_{B,g}(n)` where it means
`μ_{B,f}(n)`.

**Proof sketch.** In both experiments the inputs `x` and `y` and the coins `r` of `A`
are uniform and independent, and `A` receives `f(x)‖y`. A successful answer of `A`
is a pair whose first component is an `f`-preimage of `f(x)`, which is `B`'s answer. -/
theorem invProb_pad_le (f : α → β) (A : β × γ → ρ → α × γ) :
    invProb (pad f) A ≤ invProb f (padInverter A) := by
  unfold invProb
  rw [← uprob_comp_equiv (Equiv.prodAssoc α γ ρ)]
  apply uprob_mono
  rintro ⟨⟨x, y⟩, r⟩ h
  simp only [pad, Prod.mk.injEq] at h
  exact h.1

/-! ### Short outputs -/

open Classical in
/-- The table inverter of `f`: on input `y`, output a fixed `f`-preimage of `y` if one
exists (and the default input otherwise). As a non-uniform adversary it is the advice
string listing one preimage for each possible output. [Gar26, Exercise 2.4].

Cost: no computation beyond a table lookup; the advice has `|β|` entries, each an
element of `α`. -/
noncomputable def tableInverter [Inhabited α] (f : α → β) : β → ρ → α :=
  fun y _ => if h : ∃ x, f x = y then h.choose else default

/-- The table inverter inverts every function with probability one. [Gar26,
Exercise 2.4]. -/
theorem invProb_tableInverter [Inhabited α] [Nonempty ρ] (f : α → β) :
    invProb f (tableInverter (ρ := ρ) f) = 1 := by
  have key : ∀ z : α × ρ, f (tableInverter f (f z.1) z.2) = f z.1 := by
    intro z
    have h : ∃ x', f x' = f z.1 := ⟨z.1, rfl⟩
    rw [tableInverter, dif_pos h, h.choose_spec]
  unfold invProb
  simp only [key]
  exact uprob_true

/-- There are at most `n` bit strings of length `⌊log₂ n⌋` (for `n ≥ 1`), so the table
inverter of a function into them has at most `n` entries. [Gar26, Exercise 2.4]. -/
theorem card_log_bits_le {n : ℕ} (hn : n ≠ 0) :
    Fintype.card (Fin (Nat.log 2 n) → Bool) ≤ n := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_log_le_self 2 hn

/-- No function `{0,1}ⁿ → {0,1}^{⌊log₂ n⌋}` is one-way: some adversary whose advice is a
table of at most `n` strings of `n` bits inverts it with probability one. [Gar26,
Exercise 2.4], concrete form; the polynomial size of the advice is `card_log_bits_le`.

**Proof sketch.** Store one preimage for each of the at most `n` output values. -/
theorem exists_inverter_log_output [Nonempty ρ] {n : ℕ}
    (f : (Fin n → Bool) → (Fin (Nat.log 2 n) → Bool)) :
    ∃ table : (Fin (Nat.log 2 n) → Bool) → (Fin n → Bool),
      invProb f (fun y (_ : ρ) => table y) = 1 :=
  ⟨fun y => tableInverter (ρ := ρ) f y (Classical.arbitrary ρ), invProb_tableInverter f⟩

end TCSlib.Cryptography.OneWay
