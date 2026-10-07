/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A toolkit for abstract register machines

Conveniences for writing logspace algorithms as abstract register machines
(`Complexity.LogProg.ARM`) on inputs `⟨1ⁿ, w⟩`: the virtual inputs of calls in `unaryFst`
mode with one or two register arguments are `⟨1ⁿ, bits r⟩` and `⟨1ⁿ, ⟨bits r, bits s⟩⟩`,
and `Complexity.LogProg.arm_decides_poly` restates `Complexity.LogProg.arm_decides` with
register values bounded by a polynomial in the input length.

## Main results

* `Complexity.LogProg.vword_unary₁`, `Complexity.LogProg.vword_unary₂` — virtual inputs
  of `unaryFst` calls.
* `Complexity.LogProg.arm_decides_poly` — abstract register machines with polynomially
  bounded register values decide languages in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type}

/-- The leading run of `1`s of `⟨1ⁿ, w⟩` is `1²ⁿ`. -/
lemma takeWhile_pairEncode_replicate (n : ℕ) (w : List Bool) :
    (pairEncode (List.replicate n true) w).takeWhile (· = true) =
      List.replicate (2 * n) true := by
  simp only [pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
  rw [List.takeWhile_append_of_pos (by simp)]
  simp

/-- The virtual input of a `unaryFst` call with one argument on `⟨1ⁿ, w⟩` is `⟨1ⁿ, V r⟩`. -/
lemma vword_unary₁ (n : ℕ) (w : List Bool) (j : Fin d) (r : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .unaryFst, [r], l₁, l₀⟩ (pairEncode (List.replicate n true) w) V) =
      pairEncode (List.replicate n true) (V r) := by
  simp only [callSegs, Mode.seg0, takeWhile_pairEncode_replicate, List.map_cons,
    List.map_nil, argSegs, vword, render, Bool.false_eq_true, ↓reduceIte]
  simp [pairEncode_eq_dbl, dbl_replicate]

/-- The virtual input of a `unaryFst` call with two arguments on `⟨1ⁿ, w⟩` is
`⟨1ⁿ, ⟨V r, V s⟩⟩`. -/
lemma vword_unary₂ (n : ℕ) (w : List Bool) (j : Fin d) (r s : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .unaryFst, [r, s], l₁, l₀⟩ (pairEncode (List.replicate n true) w) V) =
      pairEncode (List.replicate n true) (pairEncode (V r) (V s)) := by
  simp only [callSegs, Mode.seg0, takeWhile_pairEncode_replicate, List.map_cons,
    List.map_nil, argSegs, vword, render, Bool.false_eq_true, ↓reduceIte]
  simp [pairEncode_eq_dbl, dbl_replicate]

/-- The indicator of a set at a point, as a decision. -/
lemma indicator_eq_decide {α : Type} (S : Set α) (a : α) :
    MultiTapeTM.indicator S a = @decide (a ∈ S) (Classical.dec _) := by
  unfold MultiTapeTM.indicator; split <;> simp_all

/-- **Abstract register machines with polynomially bounded registers decide languages in
`L`**: the form of `arm_decides` with register values at most `C₀ (|x| + 1)^{c₀}`.

**Proof sketch.** A value `v ≤ C₀ (|x|+1)^{c₀}` has `|bits (v + 1)| ≤ ⌊log₂ (v + 1)⌋ + 1`,
which `log_poly_bound` bounds by `K · logSpace |x|`. -/
theorem arm_decides_poly {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ LOGSPACE := by
  obtain ⟨K, hK⟩ := log_poly_bound C₀ c₀ 1
  refine arm_decides A l₀ As hAs K fun x => (hcorr x).mono fun a ⟨h1, h2⟩ => ⟨h1, fun r => ?_⟩
  have e1 := length_bits_le_log (a.2.1 r + 1)
  have e2 : Nat.log 2 (a.2.1 r + 1) ≤ Nat.log 2 (C₀ * (x.length + 1) ^ c₀ + 1) :=
    Nat.log_mono_right (by have := h2 r; omega)
  have e3 := hK x.length
  simp only [logSpace]
  omega

end Complexity.LogProg
