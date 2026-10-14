/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Robustness: redefining a one-way function on a small set

[Gar26, §2.2.1] observes that redefining a one-way function `f` on a set `S` of inputs of
negligible density keeps it one-way: an adversary for the patched function `g` must, on
most inputs, invert `f`. This file makes the concrete statement precise, and shows that
the claim needs a hypothesis the source leaves implicit.

Write `g = patch f k S` for the function equal to `k` on `S` and to `f` elsewhere. An
inverter `A` of `g` given `f x` with `x ∉ S` may answer with some `x' ∈ S` with
`k x' = f x`; such an answer is useless for inverting `f`. Hence:

* `invProb_patch_le`: with `B = A` itself, the loss is `Pr[S] + Pr[f x ∈ k(S)]`;
* `invProb_patch_le_of_correction`: if `B` post-processes answers in `S` with a correction
  map `c` sending `x' ∈ S` to an `f`-preimage of `k x'` (when one exists), the loss is
  only `Pr[S]`. Such a `c` always exists, but it is hard-wired advice: for one point
  (`invProb_update_le`) it is a single preimage, for exponentially many points it may be
  neither short nor efficiently computable.

For Garg's example `g(x₁‖x₂) = x₁‖x₂` when `x₁ = 0^{n/2}` (`zeroPatch`), the term
`Pr[f x ∈ k(S)]` is the probability that `f x` starts with `n/2` zeros, which need not be
small: if every output of `f` starts with `n/2` zeros then the identity adversary inverts
`zeroPatch f` with probability one (`invProb_zeroPatch_eq_one`), and such `f` can be
one-way (see `Brittleness.lean`, `zeroPatch_zeroPrefix`). So the source's example is
not one-way for every one-way `f`.

## Main definitions

* `patch f k S`: the function equal to `k` on `S` and to `f` off `S`.
* `patchInverter A S c`: the inverter of `f` built from an inverter `A` of the patch.
* `zeroPatch f`: Garg's example, the identity on inputs whose first half is zero.

## Main results

* `invProb_patch_le`, `invProb_patch_le_of_correction`, `invProb_update_le`: the
  concrete robustness bounds.
* `invProb_zeroPatch_le`: the bound for Garg's example.
* `invProb_zeroPatch_eq_one`: Garg's example fails when every output of `f` starts with
  zeros.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.2.1.
-/

namespace TCSlib.Cryptography.OneWay

open Finset TCSlib.Cryptography

variable {α β ρ : Type*} [Fintype α] [Fintype ρ]

/-- The patch of `f` by `k` on `S`: the function that agrees with `k` on inputs in `S` and
with `f` on all other inputs. [Gar26, §2.2.1], the function `g` with `g(x₀) = y₀` and
`g(x) = f(x)` otherwise, generalized to a set `S` of patched inputs. -/
def patch (f k : α → β) (S : α → Prop) [DecidablePred S] (x : α) : β :=
  if S x then k x else f x

/-- The inverter of `f` obtained from an inverter `A` of a patch on `S`: run `A` on the
input; if its answer `x'` lies in `S`, output the correction `c x'`, else output `x'`.
[Gar26, §2.2.1], "handling the case `x = x₀` separately".

Cost: one call to `A` with the same coins, one membership test for `S`, and one
evaluation of `c` (non-uniform advice in general). -/
def patchInverter (A : β → ρ → α) (S : α → Prop) [DecidablePred S] (c : α → α) :
    β → ρ → α :=
  fun y r => if S (A y r) then c (A y r) else A y r

variable (f k : α → β) (S : α → Prop) [DecidablePred S]

/-- Robustness without correction: any adversary inverts the patch `patch f k S` with
probability at most its probability of inverting `f`, plus `Pr[x ∈ S]`, plus the
probability `Pr[f x ∈ k(S)]` that an output of `f` is also a patched value. [Gar26,
§2.2.1]. Deviation: the source omits the last term; it is necessary (see
`invProb_zeroPatch_eq_one`).

**Proof sketch.** If `A` inverts the patch on `x ∉ S`, it outputs `x'` with patched value
`f x`. Either `x' ∉ S`, and then `f x' = f x`, or `x' ∈ S`, and then `f x ∈ k(S)`.
Conclude by the union bound. -/
theorem invProb_patch_le [Nonempty ρ] (A : β → ρ → α) :
    invProb (patch f k S) A ≤
      invProb f A + uprob S + uprob (fun x => ∃ x', S x' ∧ k x' = f x) := by
  unfold invProb
  calc uprob (fun z : α × ρ => patch f k S (A (patch f k S z.1) z.2) = patch f k S z.1)
      ≤ uprob (fun z : α × ρ => (f (A (f z.1) z.2) = f z.1 ∨ S z.1) ∨
          ∃ x', S x' ∧ k x' = f z.1) := by
        apply uprob_mono
        rintro ⟨x, r⟩ h
        by_cases hx : S x
        · exact Or.inl (Or.inr hx)
        simp only [patch, hx, if_false] at h ⊢
        by_cases hx' : S (A (f x) r)
        · rw [if_pos hx'] at h
          exact Or.inr ⟨_, hx', h⟩
        · rw [if_neg hx'] at h
          exact Or.inl (Or.inl h)
    _ ≤ _ := by
        refine (uprob_or_le _ _).trans (add_le_add ((uprob_or_le _ _).trans ?_) ?_)
        · rw [uprob_fst S]
        · rw [uprob_fst (fun x => ∃ x', S x' ∧ k x' = f x)]

/-- Robustness with correction: if `c` maps every `x' ∈ S` to an `f`-preimage of `k x'`
whenever `k x'` has one, then the patched function is inverted with probability at most
`Pr[x ∈ S]` more than `f` is inverted by `patchInverter A S c`. [Gar26, §2.2.1], the
argument "use [the inverter of `g`] to break `f` by handling the case `x = x₀`
separately". Deviation: the source leaves the correction implicit; here it is an
explicit parameter of the reduction.

**Proof sketch.** On `x ∉ S` the patch agrees with `f`, so a successful answer `x'` of
`A` has patched value `f x`. If `x' ∉ S` it is an `f`-preimage; if `x' ∈ S` then
`k x' = f x` has a preimage, so `c x'` is one. The inputs in `S` cost `Pr[S]`. -/
theorem invProb_patch_le_of_correction [Nonempty ρ] (A : β → ρ → α) (c : α → α)
    (hc : ∀ x', S x' → ∀ x, k x' = f x → f (c x') = f x) :
    invProb (patch f k S) A ≤ invProb f (patchInverter A S c) + uprob S := by
  unfold invProb
  calc uprob (fun z : α × ρ => patch f k S (A (patch f k S z.1) z.2) = patch f k S z.1)
      ≤ uprob (fun z : α × ρ => f (patchInverter A S c (f z.1) z.2) = f z.1 ∨ S z.1) := by
        apply uprob_mono
        rintro ⟨x, r⟩ h
        by_cases hx : S x
        · exact Or.inr hx
        left
        simp only [patch, hx, if_false] at h
        simp only [patchInverter]
        by_cases hx' : S (A (f x) r)
        · rw [if_pos hx'] at h ⊢
          exact hc _ hx' x h
        · rw [if_neg hx'] at h ⊢
          exact h
    _ ≤ _ := (uprob_or_le _ _).trans (by rw [uprob_fst S])

omit [DecidablePred S] in
/-- A correction map as required by `invProb_patch_le_of_correction` always exists: send
`x'` to some `f`-preimage of `k x'` if there is one. Its complexity is what the
asymptotic layer must charge (advice of size `|S|` preimages in general). -/
theorem exists_correction :
    ∃ c : α → α, ∀ x', S x' → ∀ x, k x' = f x → f (c x') = f x := by
  classical
  refine ⟨fun x' => if h : ∃ x, f x = k x' then h.choose else x', ?_⟩
  intro x' _ x hx
  have h : ∃ x, f x = k x' := ⟨x, hx.symm⟩
  show f (dite _ _ _) = f x
  rw [dif_pos h, h.choose_spec, hx]

/-- Robustness for a single point, the source's first case: redefining `f` at one input
`x₀` to the value `y₀` costs at most `1 / |α|` in inversion probability, against the
inverter that replaces the answer `x₀` by a hard-wired `f`-preimage `z₀` of `y₀` (any
`z₀` if there is none). [Gar26, §2.2.1], `g(x₀) = y₀`, `g(x) = f(x)` otherwise.

Cost: one call to `A`, one comparison with `x₀`, and the advice `x₀, z₀`.

**Proof sketch.** The case `S = {x₀}`, `c = const z₀` of
`invProb_patch_le_of_correction`; `Pr[x = x₀] = 1 / |α|`. -/
theorem invProb_update_le [DecidableEq α] [Nonempty ρ] (A : β → ρ → α) (x₀ : α) (y₀ : β)
    (z₀ : α) (hz₀ : ∀ x, f x = y₀ → f z₀ = y₀) :
    invProb (Function.update f x₀ y₀) A ≤
      invProb f (patchInverter A (· = x₀) fun _ => z₀) + 1 / Fintype.card α := by
  have hg : Function.update f x₀ y₀ = patch f (fun _ => y₀) (· = x₀) := by
    funext x
    simp only [Function.update_apply, patch]
  rw [hg, ← uprob_eq_one_div_card x₀]
  refine invProb_patch_le_of_correction f _ _ A _ ?_
  rintro x' - x hx
  rw [hz₀ x hx.symm, hx]

/-! ### Garg's example: the identity on inputs with a zero first half -/

/-- Garg's example of a patched function: on an input `x₁‖x₂` of two `m`-bit halves,
output `x₁‖x₂` itself when `x₁ = 0^m` and `f(x₁‖x₂)` otherwise. [Gar26, §2.2.1], the
displayed function `g` with `n = 2m`. -/
def zeroPatch {m : ℕ} (f : (Fin m → Bool) × (Fin m → Bool) → (Fin m → Bool) × (Fin m → Bool))
    (x : (Fin m → Bool) × (Fin m → Bool)) : (Fin m → Bool) × (Fin m → Bool) :=
  patch f id (fun x => x.1 = fun _ => false) x

variable {m : ℕ}

/-- For Garg's example, any adversary inverts `zeroPatch f` with probability at most its
probability of inverting `f`, plus `2^{-m}`, plus the probability that `f x` starts with
`m` zeros. [Gar26, §2.2.1]. Deviation: the source claims one-wayness of `zeroPatch f`
for every one-way `f`, omitting the last term; see `invProb_zeroPatch_eq_one`.

**Proof sketch.** `invProb_patch_le` with `S = {x | x₁ = 0^m}`, `k = id`;
`Pr[S] = 2^{-m}` and `f x ∈ k(S)` says `f x` has zero first half. -/
theorem invProb_zeroPatch_le [Nonempty ρ]
    (f : (Fin m → Bool) × (Fin m → Bool) → (Fin m → Bool) × (Fin m → Bool))
    (A : (Fin m → Bool) × (Fin m → Bool) → ρ → (Fin m → Bool) × (Fin m → Bool)) :
    invProb (zeroPatch f) A ≤
      invProb f A + 1 / 2 ^ m + uprob (fun x => (f x).1 = fun _ => false) := by
  have h := invProb_patch_le f id (fun x : (Fin m → Bool) × (Fin m → Bool) =>
    x.1 = fun _ => false) A
  have hS : uprob (fun x : (Fin m → Bool) × (Fin m → Bool) => x.1 = fun _ => false) =
      1 / 2 ^ m := by
    rw [uprob_fst (fun x₁ : Fin m → Bool => x₁ = fun _ => false), uprob_eq_one_div_card]
    simp
  have hk : uprob (fun x : (Fin m → Bool) × (Fin m → Bool) =>
      ∃ x', x'.1 = (fun _ => false) ∧ id x' = f x) =
      uprob (fun x => (f x).1 = fun _ => false) :=
    uprob_congr fun x => ⟨fun ⟨x', h1, h2⟩ => by rw [← h2]; exact h1,
      fun h => ⟨f x, h, rfl⟩⟩
  rw [hS, hk] at h
  exact h

/-- Garg's example is not one-way for every one-way `f`: if every output of `f` has a zero
first half, then the adversary that returns its input inverts `zeroPatch f` with
probability one. [Gar26, §2.2.1] (a counterexample to the source's claim).

**Proof sketch.** Every value `y` of `zeroPatch f` has zero first half (it is either an
input with zero first half or an output of `f`), and `zeroPatch f` is the identity on
such strings, so `zeroPatch f y = y`. -/
theorem invProb_zeroPatch_eq_one [Nonempty ρ]
    (f : (Fin m → Bool) × (Fin m → Bool) → (Fin m → Bool) × (Fin m → Bool))
    (hf : ∀ x, (f x).1 = fun _ => false) :
    invProb (zeroPatch f) (fun y (_ : ρ) => y) = 1 := by
  have hfix : ∀ x, zeroPatch f (zeroPatch f x) = zeroPatch f x := by
    intro x
    have h0 : (zeroPatch f x).1 = fun _ => false := by
      unfold zeroPatch patch
      split_ifs with h
      · exact h
      · exact hf x
    have : zeroPatch f (zeroPatch f x) = id (zeroPatch f x) := if_pos h0
    exact this
  unfold invProb
  simp only [hfix]
  exact uprob_true

end TCSlib.Cryptography.OneWay
