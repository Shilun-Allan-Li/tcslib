/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding and coin-splitting lemmas for the collection and universal constructions

Proof infrastructure shared by `TCSlib.Cryptography.Asymptotic.Collections`
([PS10, Theorem 42.2 ⇒]) and `TCSlib.Cryptography.Asymptotic.Universal`
([PS10, Theorem 63.1]): the polynomial-time *padding evaluator*
`padStr p u w = (w ++ 0^{p(|u|)}).take (p(|u|))`, which is the string form of the typed
output `padFin (p n) w` of a function family at parameter `n` read off `1^n`
(`ofFn_padFin_eq_padStr`).

Every FP fact here is an instance of the pairing calculus of
`TCSlib.Complexity.ClassNP.PolyTimePairing`, the unary evaluator
`Complexity.polyTimeComputable_unaryPoly`, the typed cut
`Complexity.polyTimeComputable_pairTakePoly` and the bitwise xor
`Complexity.polyTimeComputable_pairXor` (zeros are `1^m ⊕ 1^m`).

## Main definitions

* `TCSlib.Cryptography.padStr` — the string padded with `false` (or truncated) to
  `p(|u|)` bits.

## Main results

* `TCSlib.Cryptography.polyTimeComputable_padStr` — the padding evaluator is
  polynomial-time on `⟨u, w⟩`.
* `TCSlib.Cryptography.ofFn_padFin_eq_take`, `TCSlib.Cryptography.ofFn_padFin_eq_padStr`,
  `TCSlib.Cryptography.padStr_of_length_le` — the encoding of a padded typed string is the
  padded string.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5 Theorem 42.2; §2.13 Algorithm 64.2.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## Zeros and the padding evaluator -/

/-- The bitwise xor of `1^m` with itself is `0^m`. -/
theorem zipWith_xor_replicate_true (m : ℕ) :
    List.zipWith xor (List.replicate m true) (List.replicate m true) = List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m _ => simp [List.replicate_succ]

/-- `z ↦ 0^{p(|fst z|)}` is polynomial-time: the unary evaluator of `p` on the first
component, xored with itself (`Complexity.polyTimeComputable_pairXor`). -/
theorem polyTimeComputable_zerosPoly (p : PolyExpr) :
    PolyTimeComputable fun z => List.replicate (p.eval (pairFstD z).length) false := by
  have hu : PolyTimeComputable fun z => List.replicate (p.eval (pairFstD z).length) true :=
    (polyTimeComputable_unaryPoly p).comp polyTimeComputable_pairFstD
  have h := polyTimeComputable_pairXor.comp (hu.pairEncode hu)
  convert h using 1
  funext z
  simp

/-- The string `w` padded with `false` (or truncated) to `p(|u|)` bits: the string form of
the typed output `padFin (p n) w` at the parameter `n = |u|` read off `u = 1^n`
(`ofFn_padFin_eq_padStr`). -/
def padStr (p : PolyExpr) (u w : List Bool) : List Bool :=
  (w ++ List.replicate (p.eval u.length) false).take (p.eval u.length)

/-- **The padding evaluator is polynomial-time** on `⟨u, w⟩`: append the zeros
`polyTimeComputable_zerosPoly` and keep the first `p(|u|)` bits
(`Complexity.polyTimeComputable_pairTakePoly` on `⟨u, w ++ 0^{p(|u|)}⟩`). -/
theorem polyTimeComputable_padStr (p : PolyExpr) :
    PolyTimeComputable fun z => padStr p (pairFstD z) (pairSndD z) := by
  have hbody : PolyTimeComputable fun z =>
      pairSndD z ++ List.replicate (p.eval (pairFstD z).length) false :=
    polyTimeComputable_pairSndD.append (polyTimeComputable_zerosPoly p)
  have h := (polyTimeComputable_pairTakePoly p).comp (polyTimeComputable_pairFstD.pairEncode hbody)
  convert h using 1
  funext z
  simp [padStr]

/-- The padded reading of a string: `List.ofFn (padFin ℓ w)` is `(w ++ 0^ℓ).take ℓ`. -/
theorem ofFn_padFin_eq_take (ℓ : ℕ) (w : List Bool) :
    List.ofFn (padFin ℓ w) = (w ++ List.replicate ℓ false).take ℓ := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_append, List.length_replicate]
    omega
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_take,
      List.getElem_append]
    simp only [padFin, List.getD_eq_getElem?_getD]
    split_ifs with h₃
    · simp [List.getElem?_eq_getElem h₃]
    · simp [List.getElem?_eq_none_iff.mpr (not_lt.mp h₃)]

/-- The encoding of the typed padding at parameter `|u|` is the padding evaluator. -/
theorem ofFn_padFin_eq_padStr (p : PolyExpr) (u w : List Bool) :
    List.ofFn (padFin (p.eval u.length) w) = padStr p u w :=
  ofFn_padFin_eq_take _ _

/-- The padding of a string shorter than the target length appends zeros only. -/
theorem padStr_of_length_le (p : PolyExpr) (u w : List Bool) (hw : w.length ≤ p.eval u.length) :
    padStr p u w = w ++ List.replicate (p.eval u.length - w.length) false := by
  unfold padStr
  rw [List.take_append, List.take_of_length_le hw, List.take_replicate]
  congr 2
  omega

end TCSlib.Cryptography
