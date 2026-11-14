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

/-- The parameter-tagged input `⟨1^n, w⟩` of a deterministic polynomial-time algorithm. -/
def atParam (n : ℕ) (w : List Bool) : List Bool := pairEncode (List.replicate n true) w

/-- The parameter-tagged input is `pairEncode (List.replicate n true) w`. -/
theorem atParam_eq (n : ℕ) (w : List Bool) :
    atParam n w = pairEncode (List.replicate n true) w := rfl

end TCSlib.Cryptography.Authentication
