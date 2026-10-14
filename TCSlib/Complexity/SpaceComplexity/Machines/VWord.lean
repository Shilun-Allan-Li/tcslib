/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading inputs by index: small shared lemmas

Small facts used by several register machines that read their input by index:

* `Complexity.getD_drop` — the letters of a suffix `y.drop a` of the input are the letters
  of `y` shifted by `a` (with default `false`); used by the codec parsers
  (`TCSlib.Complexity.SpaceComplexity.Codec.Run`) and the `PATH` walk
  (`TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk`).
* `Complexity.getD_of_drop`, `Complexity.drop_succ_of_drop`, `Complexity.lt_of_drop`,
  `Complexity.drop_add_of_drop`, `Complexity.le_of_drop` — reading a word through a known
  suffix `x.drop p = b :: r` or `u ++ r`; used by the `TQBF` evaluator
  (`TCSlib.Complexity.ClassPSPACE.TQBFARM`).
* `Complexity.LogProg.vword_whole₂`, `Complexity.LogProg.vword_whole₃` — the virtual input
  of a `whole`-mode call with two or three arguments, extending `vword_whole₁` of
  `TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`; used by the Savitch machine
  (`TCSlib.Complexity.SpaceComplexity.SavitchARM`) and by the step lemmas of
  `TCSlib.Complexity.SpaceComplexity.Machines.NARMKit`.

Infrastructure for the register-machine description of logspace algorithms of
[AB09, §4.1]; not itself a result of the book.

## Main results

* `Complexity.getD_drop`.
* `Complexity.getD_of_drop`, `Complexity.drop_succ_of_drop`, `Complexity.lt_of_drop`,
  `Complexity.drop_add_of_drop`, `Complexity.le_of_drop`.
* `Complexity.LogProg.vword_whole₂`, `Complexity.LogProg.vword_whole₃`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity

/-- **Letters of a suffix**: position `i` of `y.drop a` is position `a + i` of `y` (reading
with default `false`). -/
lemma getD_drop (y : List Bool) (a i : ℕ) : (y.drop a).getD i false = y.getD (a + i) false := by
  simp [List.getD_eq_getElem?_getD]

/-- The head of a suffix is the letter at its offset. -/
lemma getD_of_drop {x r : List Bool} {p : ℕ} {b : Bool} (h : x.drop p = b :: r) :
    x.getD p false = b := by
  have := getD_drop x p 0; rw [h] at this; simpa using this.symm

/-- The tail of a suffix is the next suffix. -/
lemma drop_succ_of_drop {x r : List Bool} {p : ℕ} {b : Bool} (h : x.drop p = b :: r) :
    x.drop (p + 1) = r := by
  rw [← List.tail_drop, h]; rfl

/-- A nonempty suffix starts inside the word. -/
lemma lt_of_drop {x r : List Bool} {p : ℕ} {b : Bool} (h : x.drop p = b :: r) :
    p < x.length := by
  by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at h; cases h

/-- A suffix of a suffix. -/
lemma drop_add_of_drop {x u r : List Bool} {p : ℕ} (h : x.drop p = u ++ r) :
    x.drop (p + u.length) = r := by
  rw [← List.drop_drop, h, List.drop_left]

/-- A suffix is no longer than the word: `p + |u| ≤ |x|`. -/
lemma le_of_drop {x u r : List Bool} {p : ℕ} (h : x.drop p = u ++ r) (hu : u ≠ []) :
    p + u.length ≤ x.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  have : u.length ≠ 0 := by simpa using hu
  omega

namespace LogProg

open Turing

/-! ## Virtual inputs of `whole`-mode calls

`Complexity.LogProg.vword_whole₁` (in `TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`)
covers calls with one argument; these are its two- and three-argument forms. -/

/-- The virtual input of a `whole`-mode call with two arguments on input `u` is
`⟨u, ⟨V r, V s⟩⟩`. -/
theorem vword_whole₂ {m d : ℕ} {Λ : Type} (u : List Bool) (j : Fin d) (r s : Fin m)
    (l₁ l₀ : Λ) (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .whole, [r, s], l₁, l₀⟩ u V) =
      pairEncode u (pairEncode (V r) (V s)) := by
  simp [callSegs, Mode.seg0, argSegs, vword, render, pairEncode_eq_dbl]

/-- The virtual input of a `whole`-mode call with three arguments on input `u` is
`⟨u, ⟨V r, ⟨V s, V t⟩⟩⟩`. -/
theorem vword_whole₃ {m d : ℕ} {Λ : Type} (u : List Bool) (j : Fin d) (r s t : Fin m)
    (l₁ l₀ : Λ) (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .whole, [r, s, t], l₁, l₀⟩ u V) =
      pairEncode u (pairEncode (V r) (pairEncode (V s) (V t))) := by
  simp [callSegs, Mode.seg0, argSegs, vword, render, pairEncode_eq_dbl]

end LogProg

end Complexity
