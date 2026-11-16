/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Candidates.Arithmetic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient group operations of a bilinear group generator

[BB04, §2.2]: "`G` is a bilinear group if the group action in `G` can be computed efficiently and
there exists a group `G_1` and an efficiently computable bilinear map `e`". A `BilinearGen` keeps
its groups abstract (`Pairing/Group.lean`); this file states the efficiency half of the
definition as a separate contract, `BilinearGen.Ops`: polynomial-time string functions that, on
every generated description `d`, compute on the encodings of the elements of the group `d`
describes.

The contract is a hypothesis only of the results whose reductions compute in the group (the
security of BB1, `AdvancedEncryption.IdentityBased.bb1_sidSecure`). It reads exponents and the
order as binary numerals with `NumberTheory.listToNat`, the convention of the arithmetic bundle
`Candidates.ArithmeticFP` (D11), so that a reduction can do its exponent arithmetic modulo `p`
with that bundle.

## Main definitions

* `TCSlib.Cryptography.Pairing.BilinearGen.Ops` — the order, multiplication and exponentiation in
  `G`, the pairing, multiplication in `G_T` and the membership test of `G_T`, as polynomial-time
  string functions with their specifications at generated descriptions.

## Main results

None: the contract is a hypothesis, read through its fields.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (p. 4).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 23.5, polynomial-time computation.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.NumberTheory

namespace BilinearGen

/-- **Efficient operations of a bilinear group generator** [BB04, §2.2, "the group action in `G`
can be computed efficiently … an efficiently computable bilinear map `e`"]: polynomial-time
string functions that, on every generated description `d = G.desc κ r` and the encodings of
elements `x, y ∈ G`, `u, v ∈ G_T`, compute
* the order `p`, as a binary numeral (`orderStr d`);
* `x · y` from `⟨d, ⟨x, y⟩⟩` (`mulG`) and `x^n` from `⟨d, ⟨x, n⟩⟩` for any numeral `n` (`powG`);
* `e(x, y)` from `⟨d, ⟨x, y⟩⟩` (`pairStr`);
* `u · v` from `⟨d, ⟨u, v⟩⟩` (`mulT`);
* whether a `wT(κ)`-bit string `w` encodes an element of `G_T`, from `⟨d, w⟩` (`memT`).

**Deviation:** the paper asks for efficient group operations and pairing; the order, the
membership test of `G_T` and numeral exponents are the minimal extras a machine needs to sample
exponents in `Z_p` and to read messages of `G_T` sent by an adversary. Inputs that are not of
these forms are unconstrained. Inversion is `x^{p−1}`. -/
structure Ops (G : BilinearGen) where
  /-- The order `p` of the described group, as a binary numeral. -/
  orderStr : List Bool → List Bool
  /-- Multiplication in `G` on `⟨d, ⟨x, y⟩⟩`. -/
  mulG : List Bool → List Bool
  /-- Exponentiation in `G` on `⟨d, ⟨x, n⟩⟩`, `n` a binary numeral. -/
  powG : List Bool → List Bool
  /-- The pairing on `⟨d, ⟨x, y⟩⟩`. -/
  pairStr : List Bool → List Bool
  /-- Multiplication in `G_T` on `⟨d, ⟨u, v⟩⟩`. -/
  mulT : List Bool → List Bool
  /-- The membership test of `G_T` on `⟨d, w⟩`. -/
  memT : List Bool → List Bool
  /-- `orderStr` is polynomial-time. -/
  orderStr_poly : PolyTimeComputable orderStr
  /-- `mulG` is polynomial-time. -/
  mulG_poly : PolyTimeComputable mulG
  /-- `powG` is polynomial-time. -/
  powG_poly : PolyTimeComputable powG
  /-- `pairStr` is polynomial-time. -/
  pairStr_poly : PolyTimeComputable pairStr
  /-- `mulT` is polynomial-time. -/
  mulT_poly : PolyTimeComputable mulT
  /-- `memT` is polynomial-time. -/
  memT_poly : PolyTimeComputable memT
  /-- `orderStr d` reads as the order of the described group. -/
  orderStr_spec : ∀ κ (r : G.gen.Coins κ), listToNat (orderStr (G.desc κ r)) = (G.inst κ r).order
  /-- `mulG ⟨d, ⟨x, y⟩⟩` is the encoding of `x · y`. -/
  mulG_spec : ∀ κ (r : G.gen.Coins κ) (x y : (G.inst κ r).G),
    mulG (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x))
      (List.ofFn ((G.inst κ r).encG y)))) = List.ofFn ((G.inst κ r).encG (x * y))
  /-- `powG ⟨d, ⟨x, n⟩⟩` is the encoding of `x^n`, `n` read as a binary numeral. -/
  powG_spec : ∀ κ (r : G.gen.Coins κ) (x : (G.inst κ r).G) (n : List Bool),
    powG (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x)) n)) =
      List.ofFn ((G.inst κ r).encG (x ^ listToNat n))
  /-- `pairStr ⟨d, ⟨x, y⟩⟩` is the encoding of `e(x, y)`. -/
  pairStr_spec : ∀ κ (r : G.gen.Coins κ) (x y : (G.inst κ r).G),
    pairStr (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x))
      (List.ofFn ((G.inst κ r).encG y)))) = List.ofFn ((G.inst κ r).encT ((G.inst κ r).pair x y))
  /-- `mulT ⟨d, ⟨u, v⟩⟩` is the encoding of `u · v`. -/
  mulT_spec : ∀ κ (r : G.gen.Coins κ) (u v : (G.inst κ r).GT),
    mulT (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encT u))
      (List.ofFn ((G.inst κ r).encT v)))) = List.ofFn ((G.inst κ r).encT (u * v))
  /-- `memT ⟨d, w⟩` is `[true]` iff `w` encodes an element of `G_T`, and `[false]` otherwise. -/
  memT_spec : ∀ κ (r : G.gen.Coins κ) (w : Fin (G.wT.eval κ) → Bool),
    memT (pairEncode (G.desc κ r) (List.ofFn w)) = [decide (∃ u, (G.inst κ r).encT u = w)]

end BilinearGen

end TCSlib.Cryptography.Pairing
