/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complete draw and state words

Every word retains all coordinates of one complete draw or simulator state. Matrix and
vector scalar encodings reuse the public modular API. Function-dependent coordinates are
ordered by the partial garbling's supplied equivalences. No coin decoder or sampler is built.

## Main definitions

* `Wee20.Wire.scalarVector`, `scalarMatrix`: public-width modular representation adapters.
* `Wee20.Wire.linearSetupDraw`, `quadraticSetupDraw`, `quadraticEncDraw`, `linearKeyDraw`:
  complete honest randomness words.
* `Wee20.Wire.linearSimSetupDraw`, `quadraticSimSetupDraw`, `linearSimKeyDraw`:
  complete simulator randomness words.
* `Wee20.Wire.linearSimState`, `quadraticSimState`: complete private state words.

## Main results

Equation readers expose every complete coordinate list.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 3.1-3.2 and 4.2.

These wire encodings are technical glue for the cited algorithms.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire

open Complexity Turing TCSlib.Cryptography.Pairing

variable {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ)

/-- Encode all scalar vector coordinates at the public source-group width. -/
def scalarVector {n : ℕ} (v : Fin n → ZMod pp.group.order) : List Bool :=
  Encoding.Modular.encodeVector (G.wG.eval κ) v

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem scalarVector_eq {n : ℕ} (v : Fin n → ZMod pp.group.order) :
    scalarVector pp v =
      Encoding.Modular.encodeVector (G.wG.eval κ) v := rfl

/-- Encode all scalar matrix coordinates using the shared modular matrix representation. -/
def scalarMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod pp.group.order)) : List Bool :=
  Encoding.Modular.encodeMatrix (G.wG.eval κ) A

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem scalarMatrix_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod pp.group.order)) :
    scalarMatrix pp A =
      Encoding.Modular.encodeMatrix (G.wG.eval κ) A := rfl

/-- Encode all four scalar blocks of a linear setup draw. -/
def linearSetupDraw {ℓ z : PolyExpr} (ω : Linear.SetupDraw G ℓ z κ pp) : List Bool :=
  [scalarMatrix pp ω.1, scalarMatrix pp ω.2.1,
    scalarMatrix pp (fun i j => ω.2.2.1 i (finProdFinEquiv.symm j)),
    scalarMatrix pp ω.2.2.2].foldr pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem linearSetupDraw_eq {ℓ z : PolyExpr} (ω : Linear.SetupDraw G ℓ z κ pp) :
    linearSetupDraw pp ω =
      [scalarMatrix pp ω.1, scalarMatrix pp ω.2.1,
        scalarMatrix pp (fun i j => ω.2.2.1 i (finProdFinEquiv.symm j)),
        scalarMatrix pp ω.2.2.2].foldr pairEncode [] := rfl

/-- Encode the outer masks and the complete linear setup draw. -/
def quadraticSetupDraw {ℓ n1 n2 : PolyExpr}
    (ω : Quadratic.SetupDraw G ℓ n1 n2 κ pp) : List Bool :=
  [scalarMatrix pp ω.1, scalarMatrix pp ω.2.1,
    linearSetupDraw pp ω.2.2].foldr pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem quadraticSetupDraw_eq {ℓ n1 n2 : PolyExpr}
    (ω : Quadratic.SetupDraw G ℓ n1 n2 κ pp) :
    quadraticSetupDraw pp ω =
      [scalarMatrix pp ω.1, scalarMatrix pp ω.2.1,
        linearSetupDraw pp ω.2.2].foldr pairEncode [] := rfl

/-- Encode all six scalar coordinates of an outer encryption draw. -/
def quadraticEncDraw (ω : Quadratic.EncDraw G κ pp) : List Bool :=
  [scalarVector pp ω.1, scalarVector pp ω.2.1,
    scalarVector pp ω.2.2].foldr pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem quadraticEncDraw_eq (ω : Quadratic.EncDraw G κ pp) :
    quadraticEncDraw pp ω =
      [scalarVector pp ω.1, scalarVector pp ω.2.1,
        scalarVector pp ω.2.2].foldr pairEncode [] := rfl

/-- Encode the complete function-dependent T and R draw in its supplied coordinates. -/
def linearKeyDraw {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) {f : Fn κ pp.orderParam}
    (ω : Linear.KeyDraw G PG κ pp f) : List Bool :=
  [scalarMatrix pp (fun i j => ω.1 i ((PG.rowCoord κ pp.orderParam f).symm j)),
    scalarMatrix pp (fun i j => ω.2 i ((PG.mCoord κ pp.orderParam f).symm j))].foldr
    pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem linearKeyDraw_eq {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) {f : Fn κ pp.orderParam}
    (ω : Linear.KeyDraw G PG κ pp f) :
    linearKeyDraw pp PG ω =
      [scalarMatrix pp (fun i j => ω.1 i ((PG.rowCoord κ pp.orderParam f).symm j)),
        scalarMatrix pp (fun i j => ω.2 i ((PG.mCoord κ pp.orderParam f).symm j))].foldr
        pairEncode [] := rfl

/-- Encode all seven independent scalar blocks of a linear simulator setup draw. -/
def linearSimSetupDraw {ℓ z : PolyExpr}
    (ω : Linear.SimSetupDraw G ℓ z κ pp) : List Bool :=
  [scalarMatrix pp ω.1, scalarVector pp ω.2.1, scalarMatrix pp ω.2.2.1,
    scalarMatrix pp (fun i j => ω.2.2.2.1 i (finProdFinEquiv.symm j)),
    scalarMatrix pp ω.2.2.2.2.1, scalarVector pp ω.2.2.2.2.2.1,
    scalarVector pp ω.2.2.2.2.2.2].foldr pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem linearSimSetupDraw_eq {ℓ z : PolyExpr}
    (ω : Linear.SimSetupDraw G ℓ z κ pp) :
    linearSimSetupDraw pp ω =
      [scalarMatrix pp ω.1, scalarVector pp ω.2.1, scalarMatrix pp ω.2.2.1,
        scalarMatrix pp (fun i j => ω.2.2.2.1 i (finProdFinEquiv.symm j)),
        scalarMatrix pp ω.2.2.2.2.1, scalarVector pp ω.2.2.2.2.2.1,
        scalarVector pp ω.2.2.2.2.2.2].foldr pairEncode [] := rfl

/-- Encode both outer masks and the complete linear simulator setup draw. -/
def quadraticSimSetupDraw {ℓ n1 n2 : PolyExpr}
    (ω : Quadratic.SimSetupDraw G ℓ n1 n2 κ pp) : List Bool :=
  [scalarMatrix pp ω.1, scalarMatrix pp ω.2.1,
    linearSimSetupDraw pp ω.2.2].foldr pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem quadraticSimSetupDraw_eq {ℓ n1 n2 : PolyExpr}
    (ω : Quadratic.SimSetupDraw G ℓ n1 n2 κ pp) :
    quadraticSimSetupDraw pp ω =
      [scalarMatrix pp ω.1, scalarMatrix pp ω.2.1,
        linearSimSetupDraw pp ω.2.2].foldr pairEncode [] := rfl

/-- Encode all four blocks of a linear key-simulation draw. -/
def linearSimKeyDraw {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) {f : Fn κ pp.orderParam}
    (ω : Linear.SimKeyDraw G PG κ pp f) : List Bool :=
  [scalarMatrix pp (fun i j => ω.1 i ((PG.rowCoord κ pp.orderParam f).symm j)),
    scalarVector pp (fun j => ω.2.1 ((PG.l1ColCoord κ pp.orderParam f).symm j)),
    scalarMatrix pp (fun i j => ω.2.2.1 i ((PG.mCoord κ pp.orderParam f).symm j)),
    scalarVector pp (fun j => ω.2.2.2 ((PG.rowCoord κ pp.orderParam f).symm j))].foldr
    pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem linearSimKeyDraw_eq {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) {f : Fn κ pp.orderParam}
    (ω : Linear.SimKeyDraw G PG κ pp f) :
    linearSimKeyDraw pp PG ω =
      [scalarMatrix pp (fun i j => ω.1 i ((PG.rowCoord κ pp.orderParam f).symm j)),
        scalarVector pp (fun j => ω.2.1 ((PG.l1ColCoord κ pp.orderParam f).symm j)),
        scalarMatrix pp (fun i j => ω.2.2.1 i ((PG.mCoord κ pp.orderParam f).symm j)),
        scalarVector pp (fun j => ω.2.2.2 ((PG.rowCoord κ pp.orderParam f).symm j))].foldr
        pairEncode [] := rfl

/-- Encode every scalar field of the linear simulator state, including the total inverse. -/
def linearSimState {ℓ z : PolyExpr} (st : Linear.SimState G ℓ z κ pp) : List Bool :=
  [scalarMatrix pp st.A, scalarMatrix pp st.W,
    scalarMatrix pp (fun i j => st.U i (finProdFinEquiv.symm j)), scalarMatrix pp st.V,
    scalarVector pp st.c, scalarVector pp st.w, scalarVector pp st.v,
    scalarMatrix pp st.basisInv].foldr pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem linearSimState_eq {ℓ z : PolyExpr} (st : Linear.SimState G ℓ z κ pp) :
    linearSimState pp st =
      [scalarMatrix pp st.A, scalarMatrix pp st.W,
        scalarMatrix pp (fun i j => st.U i (finProdFinEquiv.symm j)), scalarMatrix pp st.V,
        scalarVector pp st.c, scalarVector pp st.w, scalarVector pp st.v,
        scalarMatrix pp st.basisInv].foldr pairEncode [] := rfl

/-- Encode the outer matrix, complete linear state and both retained scalar masks. -/
def quadraticSimState {ℓ n1 n2 : PolyExpr}
    (st : Quadratic.SimState G ℓ n1 n2 κ pp) : List Bool :=
  [groupMatrix pp st.matrix, linearSimState pp st.linear,
    scalarVector pp st.y1, scalarVector pp st.y2].foldr pairEncode []

/-- The word retains exactly the displayed complete coordinate blocks. -/
theorem quadraticSimState_eq {ℓ n1 n2 : PolyExpr}
    (st : Quadratic.SimState G ℓ n1 n2 κ pp) :
    quadraticSimState pp st =
      [groupMatrix pp st.matrix, linearSimState pp st.linear,
        scalarVector pp st.y1, scalarVector pp st.y2].foldr pairEncode [] := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire
