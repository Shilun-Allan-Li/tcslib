/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.TuringMachine.Encoding
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shared encoding for authentication games

## Main definitions

* `splitBits` splits a machine's output into two fixed-width values for the games.
* `atParam` encodes a verifier or hash evaluator's input with its unary security parameter.

## Main results

`splitBits_fst`, `splitBits_snd` and `atParam_eq` expose the encoded values.
`ofFn_splitBits_fst`, `ofFn_splitBits_snd` read the two halves as the prefix and suffix words.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  ch. 5.
-/

namespace TCSlib.Cryptography.Authentication

open Turing

/-- The first `a` and the last `b` bits of an `(a + b)`-bit string. -/
def splitBits {a b : ℕ} (w : Fin (a + b) → Bool) : (Fin a → Bool) × (Fin b → Bool) :=
  (fun i => w (Fin.castAdd b i), fun j => w (Fin.natAdd a j))

attribute [simps (config := { isSimp := false }) fst snd] splitBits

/-- The word of the first component of `splitBits w` is the first `a` bits of the word of `w`:
`List.ofFn (splitBits w).1 = (List.ofFn w).take a`. Framework glue, no textbook counterpart. -/
protected theorem ofFn_splitBits_fst {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).1 = (List.ofFn w).take a := by
  have hfst : (splitBits w).1 = fun i : Fin a => w (Fin.castAdd b i) :=
    funext fun i => splitBits_fst w i
  rw [hfst, List.ofFn_add (f := w), List.take_left' List.length_ofFn]
  rfl

/-- The word of the second component of `splitBits w` is the word of `w` after its first `a`
bits: `List.ofFn (splitBits w).2 = (List.ofFn w).drop a`. Framework glue, no textbook
counterpart. -/
protected theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).2 = (List.ofFn w).drop a := by
  have hsnd : (splitBits w).2 = fun j : Fin b => w (Fin.natAdd a j) :=
    funext fun j => splitBits_snd w j
  rw [hsnd, List.ofFn_add (f := w), List.drop_left' List.length_ofFn]

/-- The parameter-tagged input `⟨1^n, w⟩` of a deterministic polynomial-time algorithm. -/
def atParam (n : ℕ) (w : List Bool) : List Bool := pairEncode (List.replicate n true) w

/-- The parameter-tagged input is `pairEncode (List.replicate n true) w`. -/
theorem atParam_eq (n : ℕ) (w : List Bool) :
    atParam n w = pairEncode (List.replicate n true) w := rfl

end TCSlib.Cryptography.Authentication
