/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.BooleanVector
import TCSlib.Cryptography.Encoding.DyadicLinearAlgebra
import TCSlib.Cryptography.Hashing.SIS.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# An explicit encoded binary matrix-hash evaluator

## Main definitions

* `hashPoly`: expand raw domain bits to residue blocks and run the public matrix-vector loop.

## Main results

The evaluator has an unconditional fixed output width, agrees with the modular binary
matrix product on every canonical matrix and arbitrary raw domain word. Its
efficiency proof awaits the polynomial-time expansion and matrix-loop proofs.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Equation (4.1.1) and Section 5.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Section 2.1 (machine representations).

The raw domain convention is the existing false-padding/truncation map, not canonical
input rejection. Wrong matrix strings still give total fixed-width outputs; the
functional correspondence requires the stated canonical matrix encoding. This adds
no generic CRH contract and assumes no relation between SIS and LWE.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open Complexity Turing

/-- Evaluate the encoded binary matrix hash with fixed polynomial row, column and
residue-width schedules, using existing public numeric machines. -/
def hashPoly (N M W : PolyExpr) (z : List Bool) : List Bool :=
  Encoding.DyadicLinearAlgebra.matVecPoly N M W
    (pairEncode (pairFstD z) (pairEncode (pairFstD (pairSndD z))
      (Encoding.BooleanVector.expandPoly M W
        (pairEncode (pairFstD z) (pairSndD (pairSndD z))))))

/-- The complete evaluator expands the domain bits then passes both encodings to the matrix loop. -/
theorem hashPoly_eq (N M W : PolyExpr) (z : List Bool) :
    hashPoly N M W z = Encoding.DyadicLinearAlgebra.matVecPoly N M W
      (pairEncode (pairFstD z) (pairEncode (pairFstD (pairSndD z))
        (Encoding.BooleanVector.expandPoly M W
          (pairEncode (pairFstD z) (pairSndD (pairSndD z)))))) := rfl

/-- Every raw hash evaluation has exactly row-count times residue-width output bits.

**Proof sketch.** Apply the unconditional matrix-wrapper length theorem and read the
first projection of the explicitly reconstructed outer pair. -/
theorem hashPoly_length (N M W : PolyExpr) (z : List Bool) :
    (hashPoly N M W z).length = N.eval (pairFstD z).length * W.eval (pairFstD z).length := by
  simp only [hashPoly_eq, Encoding.DyadicLinearAlgebra.matVecPoly_length,
    pairFstD_pairEncode]

/-- A canonical matrix and arbitrary raw domain word produce its exact padded binary
matrix product [Pei16, Equation (4.1.1), representation correspondence].

**Proof sketch.** Read `hashPoly_eq`, recover the explicit input pair, and apply
`BooleanVector.expandPoly_encode`. The matrix-vector correspondence then gives the
canonical encoding of the product with exactly those false-padded raw bits. -/
theorem hashPoly_encodeMatrix {q : ℕ} [NeZero q] (N M W : PolyExpr) (u raw : List Bool)
    (hq : q = 2 ^ (W.eval u.length))
    (A : Matrix (Fin (N.eval u.length)) (Fin (M.eval u.length)) (ZMod q)) :
    hashPoly N M W (pairEncode u
      (pairEncode (Encoding.Modular.encodeMatrix (W.eval u.length) A) raw)) =
      Encoding.Modular.encodeVector (W.eval u.length)
        (A.mulVec (fun i => ((padFin (M.eval u.length) raw i).toNat : ZMod q))) := by
  simp only [hashPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    Encoding.BooleanVector.expandPoly_encode M W u raw hq,
    Encoding.DyadicLinearAlgebra.matVecPoly_encodeMatrix N M W u hq]

/-- The complete fixed-schedule hash evaluator is polynomial-time.

**Proof sketch.** Compose the proved-modulo-statement contracts for bit expansion
and matrix-vector multiplication with existing total projection/pairing contracts.
Their underlying loops are the existing public `BinArith.forLoop` host. -/
theorem polyTimeComputable_hashPoly (N M W : PolyExpr) : PolyTimeComputable (hashPoly N M W) := by
  sorry

end TCSlib.Cryptography.Hashing.SIS
