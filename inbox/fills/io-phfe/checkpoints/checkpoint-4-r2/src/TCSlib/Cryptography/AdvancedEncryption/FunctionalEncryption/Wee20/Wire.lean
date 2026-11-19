/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSimulator
import TCSlib.Cryptography.Encoding.Modular

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Wire representations of Wee's typed data

Source-group entries use the public group's injective encoding. Scalar entries use the
existing modular encoding at the source-group width. Explicit finite coordinates order
all partial-garbling entries; no enumeration of functions or group exponent extraction is
used. Nested pairs retain the boundaries of the finite blocks.

## Main definitions

* `Wee20.Wire.groupVector`, `groupMatrix`: source-group coordinate encodings.
* `Wee20.Wire.linearMPK`, `linearMSK`, `linearCT`, `linearKey`: the linear data words.
* `Wee20.Wire.quadraticMPK`, `quadraticMSK`, `quadraticCT`, `quadraticKey`: outer words.

## Main results

Equation readers expose every representation. Faithfulness and polynomial width bounds
are stated at the concrete outer wrapper, where all dimensions are fixed.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 3.1 and 4.2.

The wire representations are technical glue for these typed algorithms.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire

open Complexity Turing TCSlib.Cryptography.Pairing

variable {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ)

/-- Encode a source-group vector in increasing coordinate order. -/
def groupVector {n : ℕ} (v : Fin n → pp.group.G) : List Bool :=
  (List.ofFn fun i => List.ofFn (pp.group.encG (v i))).flatten

/-- The group-vector word concatenates its fixed-width element encodings. -/
theorem groupVector_eq {n : ℕ} (v : Fin n → pp.group.G) :
    groupVector pp v = (List.ofFn fun i => List.ofFn (pp.group.encG (v i))).flatten := rfl

/-- Encode a source-group matrix in increasing row and column order. -/
def groupMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) pp.group.G) : List Bool :=
  (List.ofFn fun i => groupVector pp (A i)).flatten

/-- The matrix word is the concatenation of its group-vector row words. -/
theorem groupMatrix_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) pp.group.G) :
    groupMatrix pp A = (List.ofFn fun i => groupVector pp (A i)).flatten := rfl

/-- Encode Π's public key in its four public matrix blocks. -/
def linearMPK {ℓ z : PolyExpr} (pk : Linear.MPK G ℓ z κ pp) : List Bool :=
  pairEncode (groupMatrix pp pk.A) (pairEncode (groupMatrix pp pk.AW)
    (pairEncode (groupMatrix pp (fun i j => pk.AU i (finProdFinEquiv.symm j)))
      (groupMatrix pp pk.AV)))

/-- The public-key word has exactly the four specified matrix blocks. -/
theorem linearMPK_eq {ℓ z : PolyExpr} (pk : Linear.MPK G ℓ z κ pp) :
    linearMPK pp pk = pairEncode (groupMatrix pp pk.A) (pairEncode (groupMatrix pp pk.AW)
      (pairEncode (groupMatrix pp (fun i j => pk.AU i (finProdFinEquiv.symm j)))
        (groupMatrix pp pk.AV))) := rfl

/-- Encode Π's scalar master secret at the public source-group width. -/
def linearMSK {ℓ z : PolyExpr} (sk : Linear.MSK G ℓ z κ pp) : List Bool :=
  pairEncode (Encoding.Modular.encodeMatrix (G.wG.eval κ) sk.W)
    (pairEncode (Encoding.Modular.encodeMatrix (G.wG.eval κ)
      (fun i j => sk.U i (finProdFinEquiv.symm j)))
      (Encoding.Modular.encodeMatrix (G.wG.eval κ) sk.V))

/-- The master-secret word is the displayed scalar matrix encoding. -/
theorem linearMSK_eq {ℓ z : PolyExpr} (sk : Linear.MSK G ℓ z κ pp) :
    linearMSK pp sk = pairEncode (Encoding.Modular.encodeMatrix (G.wG.eval κ) sk.W)
      (pairEncode (Encoding.Modular.encodeMatrix (G.wG.eval κ)
        (fun i j => sk.U i (finProdFinEquiv.symm j)))
        (Encoding.Modular.encodeMatrix (G.wG.eval κ) sk.V)) := rfl

/-- Encode Π's ciphertext by concatenating its three fixed-size group vectors. -/
def linearCT {z : PolyExpr} (ct : Linear.CT G z κ pp) : List Bool :=
  groupVector pp ct.c0 ++ groupVector pp ct.c1 ++ groupVector pp ct.c2

/-- The ciphertext word concatenates the three source-group blocks. -/
theorem linearCT_eq {z : PolyExpr} (ct : Linear.CT G z κ pp) :
    linearCT pp ct = groupVector pp ct.c0 ++ groupVector pp ct.c1 ++
      groupVector pp ct.c2 := rfl

variable {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
  (PG : PartialGarbling.Raw ℓ n' Fn)

/-- Encode a function key using the partial garbling's published node coordinates. -/
def linearKey {f : Fn κ pp.orderParam} (sk : Linear.Key G PG κ pp f) : List Bool :=
  pairEncode (groupMatrix pp sk.K1)
    (pairEncode (groupMatrix pp (fun i j =>
      let a := finProdFinEquiv.symm j
      sk.K2 i (a.1, (PG.mCoord κ pp.orderParam f).symm a.2)))
      (pairEncode (groupMatrix pp (fun i j => sk.K3 i ((PG.mCoord κ pp.orderParam f).symm j)))
        (groupMatrix pp (fun i j => sk.R i ((PG.mCoord κ pp.orderParam f).symm j)))))

/-- The function-key word uses `K1,K2,K3,R` in that order. -/
theorem linearKey_eq {f : Fn κ pp.orderParam} (sk : Linear.Key G PG κ pp f) :
    linearKey pp PG sk = pairEncode (groupMatrix pp sk.K1)
      (pairEncode (groupMatrix pp (fun i j =>
        let a := finProdFinEquiv.symm j
        sk.K2 i (a.1, (PG.mCoord κ pp.orderParam f).symm a.2)))
        (pairEncode (groupMatrix pp
          (fun i j => sk.K3 i ((PG.mCoord κ pp.orderParam f).symm j)))
          (groupMatrix pp (fun i j => sk.R i ((PG.mCoord κ pp.orderParam f).symm j))))) := rfl

/-- Encode an outer public key by its two masks and Π's public key. -/
def quadraticMPK {ℓ n1 n2 : PolyExpr} (pk : Quadratic.MPK G ℓ n1 n2 κ pp) : List Bool :=
  pairEncode (groupMatrix pp pk.A1)
    (pairEncode (groupMatrix pp pk.A2) (linearMPK pp pk.linear))

/-- The outer public-key word is the displayed three-block pair. -/
theorem quadraticMPK_eq {ℓ n1 n2 : PolyExpr} (pk : Quadratic.MPK G ℓ n1 n2 κ pp) :
    quadraticMPK pp pk = pairEncode (groupMatrix pp pk.A1)
      (pairEncode (groupMatrix pp pk.A2) (linearMPK pp pk.linear)) := rfl

/-- Encode the outer master secret with its public matrix metadata. -/
def quadraticMSK {ℓ n1 n2 : PolyExpr} (sk : Quadratic.MSK G ℓ n1 n2 κ pp) : List Bool :=
  pairEncode (groupMatrix pp sk.matrix) (linearMSK pp sk.linear)

/-- The outer master-secret word retains its public matrix and Π's secret word. -/
theorem quadraticMSK_eq {ℓ n1 n2 : PolyExpr} (sk : Quadratic.MSK G ℓ n1 n2 κ pp) :
    quadraticMSK pp sk = pairEncode (groupMatrix pp sk.matrix) (linearMSK pp sk.linear) := rfl

/-- Encode the outer ciphertext by the two masks followed by Π's ciphertext. -/
def quadraticCT {n1 n2 : PolyExpr} (ct : Quadratic.CT G n1 n2 κ pp) : List Bool :=
  groupVector pp ct.y1 ++ groupVector pp ct.y2 ++ linearCT pp ct.linear

/-- The outer ciphertext word is the displayed concatenation. -/
theorem quadraticCT_eq {n1 n2 : PolyExpr} (ct : Quadratic.CT G n1 n2 κ pp) :
    quadraticCT pp ct = groupVector pp ct.y1 ++ groupVector pp ct.y2 ++
      linearCT pp ct.linear := rfl

/-- Encode an outer key by its public matrix and Π's key. -/
def quadraticKey {n1 n2 : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) {f : Fn κ pp.orderParam}
    (sk : Quadratic.Key G n1 n2 PG κ pp f) : List Bool :=
  pairEncode (groupMatrix pp sk.matrix) (linearKey pp PG sk.linear)

/-- The outer key word is the displayed public-matrix and linear-key pair. -/
theorem quadraticKey_eq {n1 n2 : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) {f : Fn κ pp.orderParam}
    (sk : Quadratic.Key G n1 n2 PG κ pp f) :
    quadraticKey pp PG sk = pairEncode (groupMatrix pp sk.matrix)
      (linearKey pp PG sk.linear) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire
