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
* `Complexity.LogProg.vword_whole₂`, `Complexity.LogProg.vword_whole₃` — the virtual input
  of a `whole`-mode call with two or three arguments, extending `vword_whole₁` of
  `TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`; used by the Savitch machine
  (`TCSlib.Complexity.SpaceComplexity.SavitchARM`).

Infrastructure for the register-machine description of logspace algorithms of
[AB09, §4.1]; not itself a result of the book.

## Main results

* `Complexity.getD_drop`.
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
