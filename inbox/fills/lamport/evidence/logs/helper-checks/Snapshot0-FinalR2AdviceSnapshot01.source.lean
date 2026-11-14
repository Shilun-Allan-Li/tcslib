/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.OneWayLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary advice for a best Lamport position

## Main definitions

* `indexBits n i`: an index bounded by `n` encoded using exactly `Nat.size n` bits.
* `expandIndex U`: expand binary index advice to unary using a parameter-bounded decoder.

## Main results

* `indexBits_value`: the encoded index reads back as `i`.
* `exists_withIndexAdvice`: a machine expecting unary index data can receive that index
  through binary non-uniform advice of exactly `Nat.size n` bits.

`Nat.size n` is the binary digit count, hence the added advice has logarithmic length.
The polynomial bound supplied to the machine constructor is the weaker `Nat.size n ≤ n`.
The zero parameter uses an empty binary word encoding zero.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2, choosing the best position as non-uniform advice.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity Turing TCSlib.Cryptography

/-- An index `i ≤ n` is encoded as the inverse of the published binary-number equivalence
at width `Nat.size n`. Its width is logarithmic, including an empty encoding at `n=0`. -/
noncomputable def indexBits (n i : ℕ) (hi : i ≤ n) : List Bool :=
  List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)

/-- The index word is the serialized inverse image of `i` under `bitsEquiv`. -/
theorem indexBits_eq (n i : ℕ) (hi : i ≤ n) : indexBits n i hi =
    List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩) := rfl

/-- The binary index word has exactly `Nat.size n` bits. -/
theorem length_indexBits (n i : ℕ) (hi : i ≤ n) :
    (indexBits n i hi).length = Nat.size n := by
  rw [indexBits_eq, List.length_ofFn]

/-- Its logarithmic width is bounded by the polynomial width `n`. -/
theorem length_indexBits_le (n i : ℕ) (hi : i ≤ n) : (indexBits n i hi).length ≤ n := by
  rw [length_indexBits]
  exact Nat.size_le.2 n.lt_two_pow_self

/-- Reading the binary index word gives the original natural number `i`.

**Proof sketch.** Apply `bitsEquiv` to its inverse image, read the natural-number value
using `bitsEquiv_val`, then use the published equivalence between typed and list numerals. -/
theorem indexBits_value (n i : ℕ) (hi : i ≤ n) :
    OneWay.bitListToNat (indexBits n i hi) = i := by
  have h := congrArg Fin.val ((bitsEquiv (Nat.size n)).apply_symm_apply
    ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)
  rw [bitsEquiv_val, OneWay.bitsToNat_eq_bitListToNat] at h
  rw [indexBits_eq]
  exact h

/-- On a parameter-aware input `⟨1^n,⟨y,b⟩⟩`, decode the bounded binary index `b` to unary
and return `⟨y,U(⟨1^n,b⟩)⟩`. -/
def expandIndex (U : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD w))
    (U (pairEncode (pairFstD w) (pairSndD (pairSndD w))))

/-- The expansion pairs the challenge with `U` applied to the parameter and binary index. -/
theorem expandIndex_eq (U : List Bool → List Bool) (w : List Bool) : expandIndex U w =
    pairEncode (pairFstD (pairSndD w))
      (U (pairEncode (pairFstD w) (pairSndD (pairSndD w)))) := rfl

/-- Expanding binary index advice is polynomial-time whenever the bounded decoder is. -/
theorem expandIndex_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable (expandIndex U) :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
    (hU.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- On canonical parameter-aware input, the bounded decoder expands `b` to its unary
numeric value. This reads `advInput` and pairing only through their public equations. -/
theorem expandIndex_advInput (U : List Bool → List Bool)
    (hU : ∀ p b : List Bool, OneWay.bitListToNat b ≤ p.length →
      U (pairEncode p b) = List.replicate (OneWay.bitListToNat b) true)
    (n : ℕ) (y b : List Bool) (hb : OneWay.bitListToNat b ≤ n) :
    expandIndex U (NUPPT.advInput n (pairEncode y b)) =
      pairEncode y (List.replicate (OneWay.bitListToNat b) true) := by
  simp only [expandIndex_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [hU _ b (by simpa only [List.length_replicate] using hb)]

/-- A machine expecting `⟨y,1^(i n)⟩` can instead receive `i n ≤ n` as non-uniform binary
advice of exactly `Nat.size n` bits, keeping its coin polynomial. This is the best-position
advice step in [PS10, proof of Theorem 137.2].

**Proof sketch.** The public bounded binary-to-unary decoder expands an index using `1^n`
as its output cap. Parameter-aware preprocessing composes that decoder with the original
machine. Hard-wire the binary word using `exists_withAdvice`, bounded by `Nat.size n ≤ n`.
The preprocessor recovers the chosen unary index at every parameter, including zero. -/
theorem exists_withIndexAdvice (A : NUPPT) (i : ℕ → ℕ) (hi : ∀ n, i n ≤ n) :
    ∃ B : NUPPT, B.coins = A.coins ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r := by
  obtain ⟨U, hU, hUread⟩ := OneWay.exists_unaryOf
  obtain ⟨D, hDcoins, _, _, hD⟩ := NUPPT.exists_compParam A
    (expandIndex_poly hU) polyTimeComputable_pairSndD
  let β : ℕ → List Bool := fun n => indexBits n (i n) (hi n)
  have hβ : ∀ n, (β n).length ≤ PolyExpr.var.eval n := by
    intro n
    rw [PolyExpr.eval_var]
    exact length_indexBits_le n (i n) (hi n)
  obtain ⟨B, hBcoins, hB⟩ := NUPPT.exists_withAdvice D β .var hβ
  refine ⟨B, hBcoins.trans hDcoins, fun n y r => ?_⟩
  have hvalue : OneWay.bitListToNat (β n) = i n := indexBits_value n (i n) (hi n)
  have hcap : OneWay.bitListToNat (β n) ≤ n := by rw [hvalue]; exact hi n
  rw [hB, hD, pairSndD_pairEncode, expandIndex_advInput U hUread n y (β n) hcap, hvalue]

/-- A same-coins machine with the indexed untyped activation equation has the corresponding
typed activation equation through the published `coinsCongr` equivalence. -/
theorem runAt_indexAdvice {A B : NUPPT} (hcoins : B.coins = A.coins)
    (i : ℕ → ℕ)
    (hB : ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r)
    (n : ℕ) (y : List Bool) (r : A.Coins n) :
    B.runAt n y (NUPPT.coinsCongr hcoins.symm n r) =
      A.runAt n (pairEncode y (List.replicate (i n) true)) r := by
  rw [NUPPT.runAt_coinsCongr hcoins.symm, hB, ← NUPPT.runAt_eq]

end TCSlib.Cryptography.Authentication.LamportFill
