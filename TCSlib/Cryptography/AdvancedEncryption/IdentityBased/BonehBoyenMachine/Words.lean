/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Draws
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The string layer of the BB1 reduction handler

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): the string functions from which the handler of
`BonehBoyenMachine/Handler.lean` is assembled, each polynomial-time, with its value on the inputs
the handler sees.

**The round input.** One round of the handler (`Games.PolyHandler`) reads
`w = ⟨⟨1^κ, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (`PolyHandler.input`): the parameter, the reduction input
`z = ⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` (`Pairing.tupleStr`), the seed `ω`, the state
`s = ⟨1^j, ⟨o_1, o_2⟩⟩` (padded), the oracle index and the query. The readers are named after the
field they read: `rU`, `rZ`, `rW`, `rS`, `rI`, `rX` (the round input), `zD`, …, `zT` (the tuple),
`sJ`, `sO1`, `sR`, `sCom`, `sChal`, `sC`, `sO2`, `kT`, `kA` (the state).

**Arithmetic and groups.** Residues modulo the order `p = ⟦orderStr d⟧` are binary numerals:
`modS`, `negS`, `addS`, `mulS`, `invS` compute `a mod p`, `−a`, `a + c`, `a · c`, `a⁻¹` (`0⁻¹ = 0`)
with the functions of `Candidates.ArithmeticFP` (negation through truncated subtraction of the
reduced residue from `p`, then a reduction); `mulGS`, `powGS` are the operations of `G` of the
contract `Pairing.BilinearGen.Ops`. `uS` draws the exponent of the query from block `j` of the
seed by `Candidates.sampleBelowL` and writes it with `wG(κ) + 1` bits.

## Main definitions

* `BB1Machine.aWidth`, `BB1Machine.nn` — the widths `wG + 1` and `n · n`.
* `BB1Machine.rU`, …, `BB1Machine.kA` — the readers of the round input.
* `BB1Machine.pS`, `modS`, `negS`, `addS`, `mulS`, `invS`, `mulGS`, `powGS` — arithmetic.
* `BB1Machine.blkS`, `BB1Machine.uS` — the block of the query and its exponent.

## Main results

* `BB1Machine.poly_rU`, …, `BB1Machine.poly_uS` — polynomial time.
* `BB1Machine.rU_input`, …, `BB1Machine.zT_of` — the readers on a round input.
* `BB1Machine.listToNat_modS`, …, `BB1Machine.listToNat_invS` — the arithmetic in `Z_p`.
* `BB1Machine.listToNat_pS`, `mulGS_ofFn`, `powGS_ofFn`, `mulT_ofFn`, `memT_ofFn`,
  `memT_headD` — the group operations on encodings.
* `BB1Machine.uS_of_blkS` — the drawn exponent's numeral.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 43.2, the extended Euclidean algorithm. Context only: §2.8, Theorem 52.3, the
  discrete-log collection, whose proof remarks that its domain `Z_q` is easy to sample; it does
  not give the bounded sampler or its bound, which are the library's `Candidates.sampleBelowL`
  and `Candidates.statClose_sampleBelowL`, `Cryptography/Candidates/DiscreteLog.lean`.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability TCSlib.Cryptography.NumberTheory
  TCSlib.Cryptography.Candidates

namespace BB1Machine

noncomputable section

variable (G : BilinearGen) (ℓ : PolyExpr) (O : G.Ops)

/-! ### Lengths -/

/-- The width `aWidth G = wG + 1` of the numeral of `α_1` in the state. -/
def aWidth : PolyExpr := G.wG.add (.const 1)

/-- `(aWidth G).eval κ = wG(κ) + 1`. -/
theorem aWidth_eval (κ : ℕ) : (aWidth G).eval κ = G.wG.eval κ + 1 := by
  rw [aWidth, PolyExpr.eval_add, PolyExpr.eval_const]

/-- The block length `nn G = n · n` of one exponent's coins, `n = blockLen G`. -/
def nn : PolyExpr := (blockLen G).mul (blockLen G)

/-- `(nn G).eval κ = n · n`. -/
theorem nn_eval (κ : ℕ) : (nn G).eval κ = (blockLen G).eval κ * (blockLen G).eval κ := by
  rw [nn, PolyExpr.eval_mul]

/-! ### Reading the round input `⟨⟨1^κ, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` -/

/-- The parameter `1^κ` of the round input: `rU w = pairFstD (pairFstD w)`. -/
def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The reduction input `z`: `rZ w = pairFstD (pairSndD (pairFstD w))`. -/
def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
/-- The seed `ω`: `rW w = pairSndD (pairSndD (pairFstD w))`. -/
def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
/-- The state `s`: `rS w = pairFstD (pairSndD w)`. -/
def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i`: `rI w = pairFstD (pairSndD (pairSndD w))`. -/
def rI (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))
/-- The query `x`: `rX w = pairSndD (pairSndD (pairSndD w))`. -/
def rX (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- The description `d` of `z = ⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩`: `zD w = pairFstD (rZ w)`. -/
def zD (w : List Bool) : List Bool := pairFstD (rZ w)
/-- The word of `g`: `zG w = pairFstD (pairSndD (rZ w))`. -/
def zG (w : List Bool) : List Bool := pairFstD (pairSndD (rZ w))
/-- The word of `X`: `zX w = pairFstD (pairSndD² (rZ w))`. -/
def zX (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (rZ w)))
/-- The word of `Y`: `zY w = pairFstD (pairSndD³ (rZ w))`. -/
def zY (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD (rZ w))))
/-- The word of `Z`: `zZ w = pairFstD (pairSndD⁴ (rZ w))`. -/
def zZ (w : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))
/-- The word of `T`: `zT w = pairSndD⁵ (rZ w)`. -/
def zT (w : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))

/-- The counter `1^j` of the state `⟨1^j, ⟨o_1, o_2⟩⟩`: `sJ w = pairFstD (rS w)`. -/
def sJ (w : List Bool) : List Bool := pairFstD (rS w)
/-- The commitment `o_1`: `sO1 w = pairFstD (pairSndD (rS w))`. -/
def sO1 (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
/-- The challenge record `o_2` followed by the padding: `sR w = pairSndD (pairSndD (rS w))`. -/
def sR (w : List Bool) : List Bool := pairSndD (pairSndD (rS w))
/-- Whether an identity is committed: `sCom w = [o_1 ≠ []]`. -/
def sCom (w : List Bool) : Bool := !decide (sO1 w = [])
/-- Whether a challenge is recorded, the first bit of `o_2`: `sChal w = (sR w).headD false`. -/
def sChal (w : List Bool) : Bool := (sR w).headD false
/-- The recorded challenge `C` of `o_2 = 1 ‖ C`: the `ctLen(κ)` bits after the first. -/
def sC (w : List Bool) : List Bool :=
  ((sR w).drop 1).take ((bb1Scheme G ℓ).ctLen.eval (rU w).length)
/-- The challenge record without its padding: `1 :: sC w` if a challenge is recorded, else `[]`. -/
def sO2 (w : List Bool) : List Bool := if sChal w then true :: sC G ℓ w else []
/-- The committed identity: `kT w = pairFstD (sO1 w)`. -/
def kT (w : List Bool) : List Bool := pairFstD (sO1 w)
/-- The numeral of the committed `α_1`: `kA w = pairSndD (sO1 w)`. -/
def kA (w : List Bool) : List Bool := pairSndD (sO1 w)

/-! ### Arithmetic modulo `p` and in the groups -/

/-- The numeral of the order `p`: `pS w = orderStr (zD w)`. -/
def pS (w : List Bool) : List Bool := O.orderStr (zD w)
/-- `a mod p`: `modS w a = pairSndD (divModStr ⟨a, pS w⟩)`. -/
def modS (w a : List Bool) : List Bool := pairSndD (divModStr (pairEncode a (pS G O w)))
/-- The residue of `−a`: `negS w a = modS w (subStr ⟨pS w, modS w a⟩)`. -/
def negS (w a : List Bool) : List Bool :=
  modS G O w (subStr (pairEncode (pS G O w) (modS G O w a)))
/-- `(a + c) mod p`: `addS w a c = modS w (addStr ⟨a, c⟩)`. -/
def addS (w a c : List Bool) : List Bool := modS G O w (addStr (pairEncode a c))
/-- `(a · c) mod p`: `mulS w a c = modS w (mulStr ⟨a, c⟩)`. -/
def mulS (w a c : List Bool) : List Bool := modS G O w (mulStr (pairEncode a c))
/-- The inverse of `a` modulo `p` (`0` for `a ≡ 0`): `invS w a = pairSndD (xgcdStr ⟨a, pS w⟩)`. -/
def invS (w a : List Bool) : List Bool := pairSndD (xgcdStr (pairEncode a (pS G O w)))
/-- The product `x · y` in `G`: `mulGS w x y = mulG ⟨zD w, ⟨x, y⟩⟩`. -/
def mulGS (w x y : List Bool) : List Bool := O.mulG (pairEncode (zD w) (pairEncode x y))
/-- The power `x^e` in `G`: `powGS w x e = powG ⟨zD w, ⟨x, e⟩⟩`. -/
def powGS (w x e : List Bool) : List Bool := O.powG (pairEncode (zD w) (pairEncode x e))

/-! ### The exponent of the query -/

/-- The block of `n · n` seed bits of the `j`-th query:
`blkS w = ((rW w).drop (j · n²)).take n²` with `j = |sJ w|`. -/
def blkS (w : List Bool) : List Bool :=
  ((rW w).drop ((sJ w).length * (nn G).eval (rU w).length)).take ((nn G).eval (rU w).length)

/-- The exponent drawn from the block, as a `(wG(κ) + 1)`-bit numeral:
`uS w = ⟦(sampleBelowL p (Nat.size p) n n (blkS w)).getD 0⟧_{wG+1}`, `p = ⟦pS w⟧`. -/
def uS (w : List Bool) : List Bool :=
  natToList ((aWidth G).eval (rU w).length)
    ((sampleBelowL (listToNat (pS G O w)) (Nat.size (listToNat (pS G O w)))
      ((blockLen G).eval (rU w).length) ((blockLen G).eval (rU w).length) (blkS G w)).getD 0)

/-! ### The readers' equations -/

/-- `rU w = pairFstD (pairFstD w)`. -/
theorem rU_eq (w : List Bool) : rU w = pairFstD (pairFstD w) := rfl
/-- `rZ w = pairFstD (pairSndD (pairFstD w))`. -/
theorem rZ_eq (w : List Bool) : rZ w = pairFstD (pairSndD (pairFstD w)) := rfl
/-- `rW w = pairSndD (pairSndD (pairFstD w))`. -/
theorem rW_eq (w : List Bool) : rW w = pairSndD (pairSndD (pairFstD w)) := rfl
/-- `rS w = pairFstD (pairSndD w)`. -/
theorem rS_eq (w : List Bool) : rS w = pairFstD (pairSndD w) := rfl
/-- `rI w = pairFstD (pairSndD (pairSndD w))`. -/
theorem rI_eq (w : List Bool) : rI w = pairFstD (pairSndD (pairSndD w)) := rfl
/-- `rX w = pairSndD (pairSndD (pairSndD w))`. -/
theorem rX_eq (w : List Bool) : rX w = pairSndD (pairSndD (pairSndD w)) := rfl
/-- `zD w = pairFstD (rZ w)`. -/
theorem zD_eq (w : List Bool) : zD w = pairFstD (rZ w) := rfl
/-- `zG w = pairFstD (pairSndD (rZ w))`. -/
theorem zG_eq (w : List Bool) : zG w = pairFstD (pairSndD (rZ w)) := rfl
/-- `zX w = pairFstD (pairSndD (pairSndD (rZ w)))`. -/
theorem zX_eq (w : List Bool) : zX w = pairFstD (pairSndD (pairSndD (rZ w))) := rfl
/-- `zY w = pairFstD (pairSndD (pairSndD (pairSndD (rZ w))))`. -/
theorem zY_eq (w : List Bool) : zY w = pairFstD (pairSndD (pairSndD (pairSndD (rZ w)))) := rfl
/-- `zZ w = pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))`. -/
theorem zZ_eq (w : List Bool) :
    zZ w = pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w))))) := rfl
/-- `zT w = pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))`. -/
theorem zT_eq (w : List Bool) :
    zT w = pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w))))) := rfl
/-- `sJ w = pairFstD (rS w)`. -/
theorem sJ_eq (w : List Bool) : sJ w = pairFstD (rS w) := rfl
/-- `sO1 w = pairFstD (pairSndD (rS w))`. -/
theorem sO1_eq (w : List Bool) : sO1 w = pairFstD (pairSndD (rS w)) := rfl
/-- `sR w = pairSndD (pairSndD (rS w))`. -/
theorem sR_eq (w : List Bool) : sR w = pairSndD (pairSndD (rS w)) := rfl
/-- `sCom w = !decide (sO1 w = [])`. -/
theorem sCom_eq (w : List Bool) : sCom w = !decide (sO1 w = []) := rfl
/-- `sChal w = (sR w).headD false`. -/
theorem sChal_eq (w : List Bool) : sChal w = (sR w).headD false := rfl
/-- `sC G ℓ w = ((sR w).drop 1).take (ctLen.eval |rU w|)`. -/
theorem sC_eq (w : List Bool) :
    sC G ℓ w = ((sR w).drop 1).take ((bb1Scheme G ℓ).ctLen.eval (rU w).length) := rfl
/-- `sO2 G ℓ w = if sChal w then true :: sC G ℓ w else []`. -/
theorem sO2_eq (w : List Bool) : sO2 G ℓ w = if sChal w then true :: sC G ℓ w else [] := rfl
/-- `kT w = pairFstD (sO1 w)`. -/
theorem kT_eq (w : List Bool) : kT w = pairFstD (sO1 w) := rfl
/-- `kA w = pairSndD (sO1 w)`. -/
theorem kA_eq (w : List Bool) : kA w = pairSndD (sO1 w) := rfl
/-- `pS G O w = orderStr (zD w)`. -/
theorem pS_eq (w : List Bool) : pS G O w = O.orderStr (zD w) := rfl
/-- `modS G O w a = pairSndD (divModStr ⟨a, pS G O w⟩)`. -/
theorem modS_eq (w a : List Bool) :
    modS G O w a = pairSndD (divModStr (pairEncode a (pS G O w))) := rfl
/-- `negS G O w a = modS G O w (subStr ⟨pS G O w, modS G O w a⟩)`. -/
theorem negS_eq (w a : List Bool) :
    negS G O w a = modS G O w (subStr (pairEncode (pS G O w) (modS G O w a))) := rfl
/-- `addS G O w a c = modS G O w (addStr ⟨a, c⟩)`. -/
theorem addS_eq (w a c : List Bool) : addS G O w a c = modS G O w (addStr (pairEncode a c)) :=
  rfl
/-- `mulS G O w a c = modS G O w (mulStr ⟨a, c⟩)`. -/
theorem mulS_eq (w a c : List Bool) : mulS G O w a c = modS G O w (mulStr (pairEncode a c)) :=
  rfl
/-- `invS G O w a = pairSndD (xgcdStr ⟨a, pS G O w⟩)`. -/
theorem invS_eq (w a : List Bool) :
    invS G O w a = pairSndD (xgcdStr (pairEncode a (pS G O w))) := rfl
/-- `mulGS G O w x y = mulG ⟨zD w, ⟨x, y⟩⟩`. -/
theorem mulGS_eq (w x y : List Bool) :
    mulGS G O w x y = O.mulG (pairEncode (zD w) (pairEncode x y)) := rfl
/-- `powGS G O w x e = powG ⟨zD w, ⟨x, e⟩⟩`. -/
theorem powGS_eq (w x e : List Bool) :
    powGS G O w x e = O.powG (pairEncode (zD w) (pairEncode x e)) := rfl
/-- `blkS G w = ((rW w).drop (|sJ w| · n²)).take n²`. -/
theorem blkS_eq (w : List Bool) :
    blkS G w = ((rW w).drop ((sJ w).length * (nn G).eval (rU w).length)).take
      ((nn G).eval (rU w).length) := rfl
/-- `uS G O w = ⟦(sampleBelowL p (Nat.size p) n n (blkS G w)).getD 0⟧_{wG+1}`. -/
theorem uS_eq (w : List Bool) :
    uS G O w = natToList ((aWidth G).eval (rU w).length)
      ((sampleBelowL (listToNat (pS G O w)) (Nat.size (listToNat (pS G O w)))
        ((blockLen G).eval (rU w).length) ((blockLen G).eval (rU w).length) (blkS G w)).getD 0) :=
  rfl

/-! ### Polynomial time -/

section Poly

/-- `rU` is polynomial-time (two first projections). -/
theorem poly_rU : PolyTimeComputable rU :=
  polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
/-- `rZ` is polynomial-time. -/
theorem poly_rZ : PolyTimeComputable rZ :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
/-- `rW` is polynomial-time. -/
theorem poly_rW : PolyTimeComputable rW :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
/-- `rS` is polynomial-time. -/
theorem poly_rS : PolyTimeComputable rS :=
  polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
/-- `rI` is polynomial-time. -/
theorem poly_rI : PolyTimeComputable rI :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
/-- `rX` is polynomial-time. -/
theorem poly_rX : PolyTimeComputable rX :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
/-- `zD` is polynomial-time. -/
theorem poly_zD : PolyTimeComputable zD := polyTimeComputable_pairFstD.comp' poly_rZ
/-- `zG` is polynomial-time. -/
theorem poly_zG : PolyTimeComputable zG :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' poly_rZ)
/-- `zX` is polynomial-time. -/
theorem poly_zX : PolyTimeComputable zX :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' poly_rZ))
/-- `zY` is polynomial-time. -/
theorem poly_zY : PolyTimeComputable zY :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' poly_rZ)))
/-- `zZ` is polynomial-time. -/
theorem poly_zZ : PolyTimeComputable zZ :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' poly_rZ))))
/-- `zT` is polynomial-time. -/
theorem poly_zT : PolyTimeComputable zT :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' poly_rZ))))
/-- `sJ` is polynomial-time. -/
theorem poly_sJ : PolyTimeComputable sJ := polyTimeComputable_pairFstD.comp' poly_rS
/-- `sO1` is polynomial-time. -/
theorem poly_sO1 : PolyTimeComputable sO1 :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' poly_rS)
/-- `sR` is polynomial-time. -/
theorem poly_sR : PolyTimeComputable sR :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' poly_rS)
/-- `w ↦ [sCom w]` is polynomial-time (`isNil`, then `not`). -/
theorem poly_sCom : PolyTimeComputable fun w => [sCom w] :=
  polyTimeComputable_not (polyTimeComputable_isNil.comp' poly_sO1)
/-- `w ↦ [sChal w]` is polynomial-time (`headD`). -/
theorem poly_sChal : PolyTimeComputable fun w => [sChal w] :=
  polyTimeComputable_headD.comp' poly_sR
/-- `sC G ℓ` is polynomial-time (`pairTakePoly ctLen` of `⟨rU w, (sR w).tail⟩`). -/
theorem poly_sC : PolyTimeComputable (sC G ℓ) :=
  ((polyTimeComputable_pairTakePoly (bb1Scheme G ℓ).ctLen).comp'
    (poly_rU.pairEncode (polyTimeComputable_tail.comp' poly_sR))).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
/-- `sO2 G ℓ` is polynomial-time (a branch on `sChal`). -/
theorem poly_sO2 : PolyTimeComputable (sO2 G ℓ) :=
  (polyTimeComputable_ite poly_sChal ((polyTimeComputable_const [true]).append (poly_sC G ℓ))
    (polyTimeComputable_const [])).congr fun w => by
      simp only [sO2, List.singleton_append]
/-- `kT` is polynomial-time. -/
theorem poly_kT : PolyTimeComputable kT := polyTimeComputable_pairFstD.comp' poly_sO1
/-- `kA` is polynomial-time. -/
theorem poly_kA : PolyTimeComputable kA := polyTimeComputable_pairSndD.comp' poly_sO1

/-- `pS G O` is polynomial-time (`orderStr_poly`). -/
theorem poly_pS : PolyTimeComputable (pS G O) := O.orderStr_poly.comp' poly_zD

/-- `w ↦ modS G O w (a w)` is polynomial-time for polynomial-time `a` (`H.divMod`). -/
theorem poly_modS (H : ArithmeticFP) {a : List Bool → List Bool} (ha : PolyTimeComputable a) :
    PolyTimeComputable fun w => modS G O w (a w) :=
  polyTimeComputable_pairSndD.comp' (H.divMod.comp' (ha.pairEncode (poly_pS G O)))
/-- `w ↦ negS G O w (a w)` is polynomial-time for polynomial-time `a` (`H.sub`). -/
theorem poly_negS (H : ArithmeticFP) {a : List Bool → List Bool} (ha : PolyTimeComputable a) :
    PolyTimeComputable fun w => negS G O w (a w) :=
  poly_modS G O H (H.sub.comp' ((poly_pS G O).pairEncode (poly_modS G O H ha)))
/-- `w ↦ addS G O w (a w) (c w)` is polynomial-time for polynomial-time `a`, `c`. -/
theorem poly_addS (H : ArithmeticFP) {a c : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hc : PolyTimeComputable c) : PolyTimeComputable fun w => addS G O w (a w) (c w) :=
  poly_modS G O H (H.add.comp' (ha.pairEncode hc))
/-- `w ↦ mulS G O w (a w) (c w)` is polynomial-time for polynomial-time `a`, `c`. -/
theorem poly_mulS (H : ArithmeticFP) {a c : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hc : PolyTimeComputable c) : PolyTimeComputable fun w => mulS G O w (a w) (c w) :=
  poly_modS G O H (H.mul.comp' (ha.pairEncode hc))
/-- `w ↦ invS G O w (a w)` is polynomial-time for polynomial-time `a` (`H.xgcd`). -/
theorem poly_invS (H : ArithmeticFP) {a : List Bool → List Bool} (ha : PolyTimeComputable a) :
    PolyTimeComputable fun w => invS G O w (a w) :=
  polyTimeComputable_pairSndD.comp' (H.xgcd.comp' (ha.pairEncode (poly_pS G O)))
/-- `w ↦ mulGS G O w (x w) (y w)` is polynomial-time for polynomial-time `x`, `y`. -/
theorem poly_mulGS {x y : List Bool → List Bool} (hx : PolyTimeComputable x)
    (hy : PolyTimeComputable y) : PolyTimeComputable fun w => mulGS G O w (x w) (y w) :=
  O.mulG_poly.comp' (poly_zD.pairEncode (hx.pairEncode hy))
/-- `w ↦ powGS G O w (x w) (e w)` is polynomial-time for polynomial-time `x`, `e`. -/
theorem poly_powGS {x e : List Bool → List Bool} (hx : PolyTimeComputable x)
    (he : PolyTimeComputable e) : PolyTimeComputable fun w => powGS G O w (x w) (e w) :=
  O.powG_poly.comp' (poly_zD.pairEncode (hx.pairEncode he))

/-- `blkS G` is polynomial-time: the offset `1^{|sJ w| · n²}`
(`OneWay.polyTimeComputable_unaryMulPair`), a drop by its length and a take of `n²` bits. -/
theorem poly_blkS : PolyTimeComputable (blkS G) := by
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((sJ w).length * (nn G).eval (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp'
      (poly_sJ.pairEncode ((polyTimeComputable_unaryPoly (nn G)).comp' poly_rU))).congr fun w => by
        simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((sJ w).length * (nn G).eval (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp' (hOff.pairEncode poly_rW)).congr fun w => by
      simp only [PrefixByLength.drop_def, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate]
  exact ((polyTimeComputable_pairTakePoly (nn G)).comp' (poly_rU.pairEncode hDrop)).congr
    fun w => by simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl

/-- `uS G O` is polynomial-time.

**Proof sketch.** Apply the block-rejection host `Candidates.polyTimeComputable_rejectBlocksL`
with the test `v < p` (`H.le`), the width word `sizeStr p` (`H.size`) and `n` blocks of `n`
bits read from `blkS w`: its output `g w` is empty when the sampler fails, and otherwise its
tail, of at most `|sizeStr p|` bits, reads as the accepted value
(`sampleBelowL_eq_rejectBlocksL`). Take the tail, then normalize the width by
`(⟦0⟧_W ‖ v).drop |v| = ⟦⟦v⟧⟧_W` (`natToList_zero_append_drop`, with `⟦0⟧_W = subStr ⟨1^W, 1^W⟩`
and `W = wG + 1`), as in `Candidates.polyTimeComputable_expSampleRaw`; on a failure the tail is
empty and reads as `0`, the fallback value. -/
theorem poly_uS (H : ArithmeticFP) : PolyTimeComputable (uS G O) := by
  have hN : PolyTimeComputable fun w => List.replicate ((blockLen G).eval (rU w).length) true :=
    (polyTimeComputable_unaryPoly (blockLen G)).comp' poly_rU
  obtain ⟨g, hg, hs⟩ := polyTimeComputable_rejectBlocksL (fun a v => v < a)
    (acc := fun x => !decide (listToNat (pairFstD x) ≤ listToNat (pairSndD x)))
    (polyTimeComputable_not (H.le_poly polyTimeComputable_pairFstD polyTimeComputable_pairSndD))
    (fun w c => by
      dsimp only
      rw [pairFstD_pairEncode, pairSndD_pairEncode, ← decide_not, decide_eq_decide, Nat.not_le])
    (poly_pS G O) (H.size.comp' (poly_pS G O)) hN hN (poly_blkS G)
  have hb : PolyTimeComputable fun w => (g w).tail :=
    (PolyTimeComputable.comp' polyTimeComputable_tail hg).congr fun w => List.drop_one
  have hW : PolyTimeComputable fun w => List.replicate ((aWidth G).eval (rU w).length) true :=
    (polyTimeComputable_unaryPoly (aWidth G)).comp' poly_rU
  have hz := H.sub.comp' (hW.pairEncode hW)
  have hq := (polyTimeComputable_pairDropPoly .var).comp' (hb.pairEncode (hz.append hb))
  refine hq.congr fun w => ?_
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, subStr_self,
    List.length_replicate]
  rw [natToList_zero_append_drop, uS, sampleBelowL_eq_rejectBlocksL]
  have h2 := (hs w).2
  rw [length_sizeStr, List.length_replicate] at h2
  rw [h2]
  split_ifs with he
  · rw [he, List.tail_nil, listToNat_nil]
    rfl
  · rfl

end Poly

/-! ### Reading the round input -/

section Fields

variable {κ : ℕ} {z W S X : List Bool} {i : Fin 3}

/-- `rU (input κ z ω s i x) = 1^κ`. -/
theorem rU_input : rU (PolyHandler.input κ z W S i X) = List.replicate κ true := by
  rw [PolyHandler.input_eq, rU, pairFstD_pairEncode, pairFstD_pairEncode]
/-- `rZ (input κ z ω s i x) = z`. -/
theorem rZ_input : rZ (PolyHandler.input κ z W S i X) = z := by
  rw [PolyHandler.input_eq, rZ, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `rW (input κ z ω s i x) = ω`. -/
theorem rW_input : rW (PolyHandler.input κ z W S i X) = W := by
  rw [PolyHandler.input_eq, rW, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
/-- `rS (input κ z ω s i x) = s`. -/
theorem rS_input : rS (PolyHandler.input κ z W S i X) = S := by
  rw [PolyHandler.input_eq, rS, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `rI (input κ z ω s i x) = 1^i`. -/
theorem rI_input : rI (PolyHandler.input κ z W S i X) = List.replicate i true := by
  rw [PolyHandler.input_eq, rI, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `rX (input κ z ω s i x) = x`. -/
theorem rX_input : rX (PolyHandler.input κ z W S i X) = X := by
  rw [PolyHandler.input_eq, rX, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

end Fields

section Tuple

variable {w : List Bool} {wG wT : ℕ} {B : BilinearGroup wG wT} {d : List Bool}
  {g X Y Z : B.G} {T : B.GT}

/-- `zD w = d` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zD_of (h : rZ w = tupleStr B d g X Y Z T) : zD w = d := by
  rw [zD, h, tupleStr_eq, pairFstD_pairEncode]
/-- `zG w = ⟦g⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zG_of (h : rZ w = tupleStr B d g X Y Z T) : zG w = List.ofFn (B.encG g) := by
  rw [zG, h, tupleStr_eq, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `zX w = ⟦X⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zX_of (h : rZ w = tupleStr B d g X Y Z T) : zX w = List.ofFn (B.encG X) := by
  rw [zX, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `zY w = ⟦Y⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zY_of (h : rZ w = tupleStr B d g X Y Z T) : zY w = List.ofFn (B.encG Y) := by
  rw [zY, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
/-- `zZ w = ⟦Z⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zZ_of (h : rZ w = tupleStr B d g X Y Z T) : zZ w = List.ofFn (B.encG Z) := by
  rw [zZ, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode, pairFstD_pairEncode]
/-- `zT w = ⟦T⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zT_of (h : rZ w = tupleStr B d g X Y Z T) : zT w = List.ofFn (B.encT T) := by
  rw [zT, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode, pairSndD_pairEncode]

end Tuple

/-! ### Arithmetic modulo `p` on numerals -/

section Arith

variable {w : List Bool} {p : ℕ} [NeZero p]

omit [NeZero p] in
/-- The order read from `pS` fits its numeral: `p < 2^{|pS w|}`. -/
theorem pS_lt (hp : listToNat (pS G O w) = p) : p < 2 ^ (pS G O w).length :=
  hp ▸ listToNat_lt_two_pow _

/-- `⟦a mod p⟧ = (a : Z_p).val`. -/
theorem listToNat_modS (hp : listToNat (pS G O w) = p) (a : List Bool) :
    listToNat (modS G O w a) = ((listToNat a : ZMod p)).val := by
  rw [modS, divModStr_pairEncode, pairSndD_pairEncode, hp, ZMod.val_natCast]
  exact listToNat_natToList ((Nat.mod_lt _ (NeZero.pos p)).trans (pS_lt G O hp))

/-- `⟦−a mod p⟧ = (−(a : Z_p)).val`. -/
theorem listToNat_negS (hp : listToNat (pS G O w) = p) (a : List Bool) :
    listToNat (negS G O w a) = (-(listToNat a : ZMod p)).val := by
  rw [negS, listToNat_modS G O hp, listToNat_subStr, hp, listToNat_modS G O hp, ZMod.neg_val',
    ZMod.val_natCast]

/-- `⟦(a + c) mod p⟧ = ((a : Z_p) + c).val`. -/
theorem listToNat_addS (hp : listToNat (pS G O w) = p) (a c : List Bool) :
    listToNat (addS G O w a c) = ((listToNat a : ZMod p) + (listToNat c : ZMod p)).val := by
  rw [addS, listToNat_modS G O hp, listToNat_addStr, Nat.cast_add]

/-- `⟦(a · c) mod p⟧ = ((a : Z_p) · c).val`. -/
theorem listToNat_mulS (hp : listToNat (pS G O w) = p) (a c : List Bool) :
    listToNat (mulS G O w a c) = ((listToNat a : ZMod p) * (listToNat c : ZMod p)).val := by
  rw [mulS, listToNat_modS G O hp, listToNat_mulStr, Nat.cast_mul]

/-- `⟦a⁻¹ mod p⟧ = ((a : Z_p)⁻¹).val` (the extended Euclidean algorithm; `0⁻¹ = 0`). -/
theorem listToNat_invS (hp : listToNat (pS G O w) = p) (a : List Bool) :
    listToNat (invS G O w a) = ((listToNat a : ZMod p)⁻¹).val := by
  rw [invS, xgcdStr_pairEncode, pairSndD_pairEncode, hp]
  exact listToNat_natToList ((ZMod.val_lt _).trans (pS_lt G O hp))

end Arith

/-! ### Group operations on encodings -/

section Group

variable {w : List Bool} {κ : ℕ} {r : G.gen.Coins κ}

/-- `⟦pS⟧ = p` on the generated description. -/
theorem listToNat_pS (hD : zD w = G.desc κ r) :
    listToNat (pS G O w) = (G.group κ (G.desc κ r)).order := by
  have h := O.orderStr_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [pS, hD]
  exact h

/-- `mulG` on encodings: `⟦x⟧ · ⟦y⟧ = ⟦x · y⟧`. -/
theorem mulGS_ofFn (hD : zD w = G.desc κ r) (x y : (G.group κ (G.desc κ r)).G) :
    mulGS G O w (List.ofFn ((G.group κ (G.desc κ r)).encG x))
      (List.ofFn ((G.group κ (G.desc κ r)).encG y)) =
      List.ofFn ((G.group κ (G.desc κ r)).encG (x * y)) := by
  have h := O.mulG_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [mulGS, hD]
  exact h x y

/-- `powG` on encodings: `⟦x⟧^e = ⟦x^{⟦e⟧}⟧`. -/
theorem powGS_ofFn (hD : zD w = G.desc κ r) (x : (G.group κ (G.desc κ r)).G)
    (e : List Bool) :
    powGS G O w (List.ofFn ((G.group κ (G.desc κ r)).encG x)) e =
      List.ofFn ((G.group κ (G.desc κ r)).encG (x ^ listToNat e)) := by
  have h := O.powG_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [powGS, hD]
  exact h x e

/-- `mulT` on encodings: `⟦u⟧ · ⟦v⟧ = ⟦u · v⟧` in `G_T`. -/
theorem mulT_ofFn (hD : zD w = G.desc κ r) (u v : (G.group κ (G.desc κ r)).GT) :
    O.mulT (pairEncode (zD w) (pairEncode (List.ofFn ((G.group κ (G.desc κ r)).encT u))
      (List.ofFn ((G.group κ (G.desc κ r)).encT v)))) =
      List.ofFn ((G.group κ (G.desc κ r)).encT (u * v)) := by
  have h := O.mulT_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [hD]
  exact h u v

/-- `memT` on encodings: `[w encodes an element of G_T]`. -/
theorem memT_ofFn (hD : zD w = G.desc κ r) (m : Fin (G.wT.eval κ) → Bool) :
    O.memT (pairEncode (zD w) (List.ofFn m)) =
      [decide (∃ u, (G.group κ (G.desc κ r)).encT u = m)] := by
  have h := O.memT_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [hD]
  exact h m

/-- The membership test on a `wT`-bit word: `(memT ⟨d, l⟩).headD false = [l encodes some u]`. -/
theorem memT_headD (hD : zD w = G.desc κ r) (l : List Bool) (hl : l.length = G.wT.eval κ) :
    (O.memT (pairEncode (zD w) l)).headD false =
      decide (∃ u, List.ofFn ((G.group κ (G.desc κ r)).encT u) = l) := by
  have h := memT_ofFn G O hD (padFin _ l)
  rw [ofFn_padFin_of_length hl] at h
  rw [h, List.headD_cons, decide_eq_decide]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [hu, ofFn_padFin_of_length hl]⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [← hu, padFin_ofFn]⟩

end Group

/-! ### The order and the identities -/

section Order

variable {κ : ℕ}

/-- The width of `α_1`'s numeral is `wG + 1`, and the order is below `2^{wG + 1}`. -/
theorem order_lt_aWidth (κ : ℕ) (d : List Bool) :
    (G.group κ d).order < 2 ^ (aWidth G).eval κ := by
  rw [aWidth, PolyExpr.eval_add, PolyExpr.eval_const, pow_succ]
  have := order_le_two_pow G κ d
  have h2 : 0 < 2 ^ G.wG.eval κ := Nat.two_pow_pos _
  omega

/-- The numeral of a residue at width `wG + 1` reads back as its value. -/
theorem listToNat_natToList_val {d : List Bool} (v : ZMod (G.group κ d).order) :
    listToNat (natToList ((aWidth G).eval κ) v.val) = v.val :=
  listToNat_natToList ((ZMod.val_lt v).trans (order_lt_aWidth G κ d))

/-- An identity read in `Z_p` is its numeral's residue:
`idToZ (padFin _ ⟦x⟧) = (⟦x⟧ : Z_p)`. -/
theorem idToZ_padFin {d : List Bool} {e : ℕ} (x : Fin e → Bool)
    (h : e = (bb1Scheme G ℓ).idLen.eval κ) :
    BB1.idToZ (G.group κ d) (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) =
      ((listToNat (List.ofFn x) : ℕ) : ZMod (G.group κ d).order) := by
  rw [BB1.idToZ_eq, NumberTheory.bitsToNat_eq_listToNat,
    ofFn_padFin_of_length (by rw [List.length_ofFn, h])]

end Order

/-! ### The drawn exponent -/

/-- **The drawn exponent's numeral**: if the block of the query is `⟦v⟧`, then
`uS w = ⟦(draw G κ d v).val⟧_{wG+1}` (`draw_eq`; a drawn value is below `p`). -/
theorem uS_of_blkS {w : List Bool} {κ : ℕ} {r : G.gen.Coins κ} (hU : (rU w).length = κ)
    (hD : zD w = G.desc κ r) (v : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool)
    (hv : blkS G w = List.ofFn v) :
    uS G O w = natToList ((aWidth G).eval κ) (draw G κ (G.desc κ r) v).val := by
  have hp := listToNat_pS G O hD
  rw [uS, hU, hp, hv, draw_eq, ZMod.val_natCast, Nat.mod_eq_of_lt]
  generalize hs : sampleBelowL _ _ _ _ _ = o
  rcases o with _ | u
  · exact (G.group κ (G.desc κ r)).order_prime.pos
  · exact sampleBelowL_lt hs

end

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
