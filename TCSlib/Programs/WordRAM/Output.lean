/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The output of a word-RAM program

`WordRAM.progOut P W x` is the bit string that the extended word-RAM program `P` emits on the
input `x`, with word size `W |x|` and coins reading `0`, if it halts, and `[]` if it does not. A
program's output is unique (`WordRAM.HaltsWithin.unique`), so this is well defined. It names the
function a program computes even where the program's correctness is only proved on some inputs:
a consumer proves halting within a bound on every input, and correctness only where it matters.

## Main definitions

* `WordRAM.progOut`: the output of a program on an input, `[]` if it does not halt.

## Main results

* `WordRAM.progOut_eq`: a halting run's output is `progOut`.
* `WordRAM.progOut_of_not_halts`: without a halting run, `progOut` is `[]`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM

/-- **The output of a program**: what `P` emits on `x`, with word size `W |x|` and the empty coin
stream, if some run halts; `[]` otherwise. -/
noncomputable def progOut (P : XProgram) (W : ℕ → ℕ) (x : List Bool) : List Bool :=
  haveI := Classical.propDecidable
    (∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ), HaltsWithin P x [] (W x.length) t v o f)
  if h : ∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ), HaltsWithin P x [] (W x.length) t v o f
    then Classical.choose h else []

/-- **A halting run's output is `progOut`.**

**Proof sketch.** A halting run exists, so `progOut` is the output of some chosen halting run;
`HaltsWithin.unique` makes the two outputs equal. -/
theorem progOut_eq {P : XProgram} {W : ℕ → ℕ} {x : List Bool} {t f : ℕ} {v : Bool}
    {o : List Bool} (h : HaltsWithin P x [] (W x.length) t v o f) : progOut P W x = o := by
  have hex : ∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ),
      HaltsWithin P x [] (W x.length) t v o f := ⟨o, t, v, f, h⟩
  unfold progOut
  rw [dif_pos hex]
  obtain ⟨t', v', f', h'⟩ := Classical.choose_spec hex
  exact (h'.unique h).2

/-- Without a halting run, `progOut` is `[]`. -/
theorem progOut_of_not_halts {P : XProgram} {W : ℕ → ℕ} {x : List Bool}
    (h : ¬ ∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ), HaltsWithin P x [] (W x.length) t v o f) :
    progOut P W x = [] := by
  unfold progOut
  rw [dif_neg h]

end WordRAM
