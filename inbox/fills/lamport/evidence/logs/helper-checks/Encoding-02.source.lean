/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Complexity.TuringMachine.Encoding
import Mathlib.Data.List.OfFn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Injectivity of the cryptographic tuple encoding

## Main definitions

None.

## Main results

* `encodeList_injective`: equality of encoded lists implies equality of their blocks.
* `encodeList_eq_iff`: list encodings agree exactly when the lists agree.
* `encodeList_ofFn_eq_iff`: encodings of finite tuples agree exactly when the tuples agree.

## References

Generic encoding lemmas; no textbook counterpart. These use the list encoding of
[PS10, Definition 93.1] through its published equations only.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open Turing
open TCSlib.Cryptography.PrivateKeyScheme (encodeList encodeList_nil encodeList_cons)

/-- The nested-pair list encoding is injective: `encodeList xs = encodeList ys` implies
`xs = ys`.

**Proof sketch.** Induct on the first list. An empty encoding cannot equal a cons encoding,
since a pair encoding is nonempty. For two cons encodings, injectivity of pairing identifies
the heads and the encoded tails, and induction identifies the tails. -/
theorem encodeList_injective : Function.Injective encodeList := by
  have haux : ∀ xs ys : List (List Bool), encodeList xs = encodeList ys → xs = ys := by
    intro xs
    induction xs with
    | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
        rw [encodeList_nil, encodeList_cons] at h
        exact False.elim (pairEncode_ne_nil y (encodeList ys) h.symm)
    | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
        rw [encodeList_cons, encodeList_nil] at h
        exact False.elim (pairEncode_ne_nil x (encodeList xs) h)
      | cons y ys =>
        rw [encodeList_cons, encodeList_cons] at h
        have hp : (x, encodeList xs) = (y, encodeList ys) := pairEncode_injective h
        have hx : x = y := congrArg Prod.fst hp
        have hxs : xs = ys := ih ys (congrArg Prod.snd hp)
        exact congrArg₂ List.cons hx hxs
  intro xs ys h
  exact haux xs ys h

/-- Two nested-pair list encodings agree exactly when their lists of blocks agree. -/
theorem encodeList_eq_iff (xs ys : List (List Bool)) :
    encodeList xs = encodeList ys ↔ xs = ys :=
  ⟨encodeList_injective, congrArg encodeList⟩

/-- Encodings of two tuples with the same finite index length agree exactly when the tuples
agree: `encodeList (List.ofFn g) = encodeList (List.ofFn h) ↔ g = h`. -/
theorem encodeList_ofFn_eq_iff {q : ℕ} (g h : Fin q → List Bool) :
    encodeList (List.ofFn g) = encodeList (List.ofFn h) ↔ g = h := by
  constructor
  · intro heq
    exact List.ofFn_injective (encodeList_injective heq)
  · intro heq
    exact congrArg (fun k : Fin q → List Bool => encodeList (List.ofFn k)) heq

end TCSlib.Cryptography.Authentication.LamportReduction
