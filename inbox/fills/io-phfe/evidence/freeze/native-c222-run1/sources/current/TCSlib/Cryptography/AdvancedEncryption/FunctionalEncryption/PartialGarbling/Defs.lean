/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Complexity.Randomized.PPT
import Mathlib.Data.PNat.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Partial garbling with uniform efficiency

The raw interface fixes the corrected matrix syntax of [AGW20, Lemma 2, p.12],
with dimensions read from [AGW20, Appendix A, (32), p.38]. Garbling and simulated
partial garbling are derived from those matrices. Reconstruction holds for every
random draw; privacy is equality of laws, as in [IW14, Definition 1, p.6].

The efficient interface extends the raw family by deterministic polynomial-time
contracts for matrix generation and reconstruction. Each contract chooses one
program before the security parameter and the modulus. The positive modulus and
dimensions of the function class occur explicitly on its input. No sampler is constructed.

The matrix syntax is affine in the public input at fixed randomness. No claim is
made of the stronger single-coordinate syntax called affine in [IW14, Definition 1].

## Main definitions

* `PartialGarbling.publicTensor`: the matrix `x ⊗ I`, with the singleton index removed.
* `PartialGarbling.pgbCore`, `pgbStarCore`: the canonical matrix formulas.
* `PartialGarbling.Raw`: a family of raw algorithms with reconstruction and exact privacy.
* `PartialGarbling.Raw.pgb`, `pgbStar`: derived garblings of a raw family.
* `PartialGarbling`: the raw family together with uniform deterministic efficiency.

## Main results

* `PartialGarbling.kronecker_mul_publicTensor`: the canonical mixed-product identity.
* The equation readers expose every derived definition without foreign unfolding.
* `PartialGarbling.Raw.reconstruct`: reconstruction of every canonical garbling.
* `PartialGarbling.Raw.exactPrivacy`: equality of the real and simulated laws.
* The `toRaw` projection readers expose the efficient interface's underlying algorithms.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, ePrint 2020/1420, Section 4.2, p.10.
* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, Lemma 2, p.12, Appendix A, pp.37–38, (28)–(32).
* [IW14] Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, 2014,
  Definition 1, pp.6–7, Theorem 3, p.8, and §4.2, pp.9–11.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing
open TCSlib.Cryptography.Games

namespace PartialGarbling

section MatrixFormulas

variable {M T : Type} [Fintype M] [Fintype T] [DecidableEq M]
  {p : ℕ+} {l n : ℕ}

/-- The public-input tensor is `x ⊗ I`, with its singleton column index removed.
This is the tensor in [AGW20, Appendix A, (32), p.38]. -/
def publicTensor (x : Fin l → ZMod (p : ℕ)) : Matrix (Fin l × M) M (ZMod (p : ℕ)) :=
  fun iu v => Matrix.kroneckerMap (fun a b => a * b)
    (fun i (_ : Fin 1) => x i) (1 : Matrix M M (ZMod (p : ℕ))) iu (0, v)

/-- The public-input tensor has entry `x i` on matching node coordinates and zero
otherwise: `publicTensor x (i,u) v = x i * (if u=v then 1 else 0)`. -/
theorem publicTensor_apply (x : Fin l → ZMod (p : ℕ)) (i : Fin l) (u v : M) :
    publicTensor x (i, u) v = x i * (if u = v then 1 else 0) := rfl

/-- A known scalar matrix can move through the public-input tensor by the identity
Kronecker block. This is the singleton-column specialization of the mixed-product
law used in [Wee20, §4.2, p.10, (10); AGW20, Appendix A, (32), p.38].

**Proof sketch.** Apply Mathlib's Matrix.mul_kronecker_mul to the identity, the
single-column x matrix, R and the identity. Read the chosen singleton column through
publicTensor_apply and the published matrix/product-index equations. The second
mixed-product specialization uses the one-dimensional identity and gives the right
side after dropping its unique singleton coordinate. Do not reprove the generic
Kronecker mixed-product law. -/
theorem kronecker_mul_publicTensor {p : ℕ+} {l : ℕ} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (x : Fin l → ZMod (p : ℕ)) (R : Matrix I J (ZMod (p : ℕ))) :
    Matrix.kroneckerMap (fun a b => a * b)
        (1 : Matrix (Fin l) (Fin l) (ZMod (p : ℕ))) R *
      publicTensor (p := p) (M := J) x =
        publicTensor (p := p) (M := I) x * R := by
  let X : Matrix (Fin l) (Fin 1) (ZMod (p : ℕ)) := fun i _ => x i
  have hLeft := Matrix.mul_kronecker_mul
    (1 : Matrix (Fin l) (Fin l) (ZMod (p : ℕ))) X R
    (1 : Matrix J J (ZMod (p : ℕ)))
  have hRight := Matrix.mul_kronecker_mul X
    (1 : Matrix (Fin 1) (Fin 1) (ZMod (p : ℕ)))
    (1 : Matrix I I (ZMod (p : ℕ))) R
  simp only [Matrix.one_mul, Matrix.mul_one] at hLeft hRight
  funext iu j
  rcases iu with ⟨i, u⟩
  have h := congrFun (congrFun (hLeft.symm.trans hRight) (i, u)) (0, j)
  simpa only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_one,
    Matrix.kroneckerMap_apply, Matrix.one_apply, publicTensor_apply,
    ite_true, one_mul] using h

/-- The real partial garbling is `(z − last(t), tᵀ(L1(x ⊗ I) + L0))`.
[AGW20, Lemma 2, p.12; Appendix A, (31)–(32), p.38]. The printed L0/L1 shapes
in Lemma 2 are read with the correction forced by (32). -/
def pgbCore
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ)))
    (x : Fin l → ZMod (p : ℕ)) (z : Fin n → ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) : (Fin n ⊕ M) → ZMod (p : ℕ) :=
  Sum.elim (fun j => z j - t (Sum.inr j))
    (Matrix.vecMul t (L1 * publicTensor x + L0))

/-- The real garbling is the displayed concatenation of the masked private input
and the matrix product. -/
theorem pgbCore_eq
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ)))
    (x : Fin l → ZMod (p : ℕ)) (z : Fin n → ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) :
    pgbCore L1 L0 x z t = Sum.elim (fun j => z j - t (Sum.inr j))
      (Matrix.vecMul t (L1 * publicTensor x + L0)) := rfl

/-- The real garbling's first block is the private input masked by the last draw
coordinates: `pgbCore L1 L0 x z t (inl j) = z j − t (inr j)`. -/
theorem pgbCore_inl
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ)))
    (x : Fin l → ZMod (p : ℕ)) (z : Fin n → ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) (j : Fin n) :
    pgbCore L1 L0 x z t (Sum.inl j) = z j - t (Sum.inr j) := rfl

/-- The real garbling's second block is `tᵀ(L1(x ⊗ I) + L0)`. -/
theorem pgbCore_inr
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ)))
    (x : Fin l → ZMod (p : ℕ)) (z : Fin n → ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) (u : M) :
    pgbCore L1 L0 x z t (Sum.inr u) =
      Matrix.vecMul t (L1 * publicTensor x + L0) u := rfl

/-- The simulated partial garbling replaces the first block by `−last(t)` and
adds the allowed value at the distinguished second-block coordinate.
[AGW20, Lemma 2, p.12; Appendix A, (30)–(32), pp.37–38]. -/
def pgbStarCore
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ))) (m0 : M)
    (x : Fin l → ZMod (p : ℕ)) (mu : ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) : (Fin n ⊕ M) → ZMod (p : ℕ) :=
  Sum.elim (fun j => -t (Sum.inr j))
    (fun u => Matrix.vecMul t (L1 * publicTensor x + L0) u + if u = m0 then mu else 0)

/-- The simulated garbling is the canonical masked block followed by the matrix
product with the allowed value added at `m0`. -/
theorem pgbStarCore_eq
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ))) (m0 : M)
    (x : Fin l → ZMod (p : ℕ)) (mu : ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) :
    pgbStarCore L1 L0 m0 x mu t = Sum.elim (fun j => -t (Sum.inr j))
      (fun u => Matrix.vecMul t (L1 * publicTensor x + L0) u +
        if u = m0 then mu else 0) := rfl

/-- The simulated garbling's first block is `−last(t)`. -/
theorem pgbStarCore_inl
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ))) (m0 : M)
    (x : Fin l → ZMod (p : ℕ)) (mu : ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) (j : Fin n) :
    pgbStarCore L1 L0 m0 x mu t (Sum.inl j) = -t (Sum.inr j) := rfl

/-- The simulated garbling's second block is the matrix product with the allowed
value added at `m0`. -/
theorem pgbStarCore_inr
    (L1 : Matrix (T ⊕ Fin n) (Fin l × M) (ZMod (p : ℕ)))
    (L0 : Matrix (T ⊕ Fin n) M (ZMod (p : ℕ))) (m0 : M)
    (x : Fin l → ZMod (p : ℕ)) (mu : ZMod (p : ℕ))
    (t : (T ⊕ Fin n) → ZMod (p : ℕ)) (u : M) :
    pgbStarCore L1 L0 m0 x mu t (Sum.inr u) =
      Matrix.vecMul t (L1 * publicTensor x + L0) u + if u = m0 then mu else 0 := rfl

end MatrixFormulas

/-- The public parameter word contains binary numerals of the positive modulus,
public-input dimension, and output dimension. Each numeral has its canonical
binary width; the modulus is supplied as input rather than computed from κ.
This is encoding glue for the algorithms of [AGW20, Lemma 2, p.12]. -/
def paramWord (l n : PolyExpr) (kappa : ℕ) (p : ℕ+) : List Bool :=
  pairEncode (Candidates.natToList (Nat.size (p : ℕ)) (p : ℕ))
    (pairEncode (Candidates.natToList (Nat.size (l.eval kappa)) (l.eval kappa))
      (Candidates.natToList (Nat.size (n.eval kappa)) (n.eval kappa)))

/-- The public parameter word is the nested pair of the three binary numerals. -/
theorem paramWord_eq (l n : PolyExpr) (kappa : ℕ) (p : ℕ+) :
    paramWord l n kappa p =
      pairEncode (Candidates.natToList (Nat.size (p : ℕ)) (p : ℕ))
        (pairEncode (Candidates.natToList (Nat.size (l.eval kappa)) (l.eval kappa))
          (Candidates.natToList (Nat.size (n.eval kappa)) (n.eval kappa))) := rfl

/-- A raw family of partial-garbling algorithms has the corrected matrix syntax,
reconstruction for every draw, and exact privacy.
[AGW20, Lemma 2, p.12; Appendix A, (28)–(32), pp.37–38; IW14, Definition 1, pp.6–7].
The matrix dimensions use the correction forced by (32). Index equivalences fix
all finite-coordinate encodings. The family ranges over every positive modulus
so that uniform efficiency can choose a program before κ and the modulus. -/
structure Raw (l n : PolyExpr) (Fn : (kappa : ℕ) → ℕ+ → Type) where
  /-- Non-output coordinates, including the distinguished source coordinate. -/
  MIdx : (kappa : ℕ) → (p : ℕ+) → Fn kappa p → Type
  /-- Auxiliary draw coordinates; output coordinates form the final draw block. -/
  TIdx : (kappa : ℕ) → (p : ℕ+) → Fn kappa p → Type
  /-- Each non-output coordinate type is finite. -/
  [mFinite : ∀ kappa p f, Fintype (MIdx kappa p f)]
  /-- Each auxiliary draw-coordinate type is finite. -/
  [tFinite : ∀ kappa p f, Fintype (TIdx kappa p f)]
  /-- Equality of non-output coordinates is decidable. -/
  [mDecEq : ∀ kappa p f, DecidableEq (MIdx kappa p f)]
  /-- Equality of auxiliary draw coordinates is decidable. -/
  [tDecEq : ∀ kappa p f, DecidableEq (TIdx kappa p f)]
  /-- The number of non-output coordinates. -/
  mCount : (kappa : ℕ) → (p : ℕ+) → Fn kappa p → ℕ
  /-- A polynomial bound on the non-output dimension, fixed by the function class
  independently of the modulus and adaptively chosen function. This is the size
  bound in [AGW20, Lemma 2, p.12], not an algorithm-efficiency hypothesis. -/
  mBound : PolyExpr
  /-- Every represented function uses at most the fixed polynomial node bound. -/
  mCount_le_mBound : ∀ kappa p f, mCount kappa p f ≤ mBound.eval kappa
  /-- The number of auxiliary draw coordinates. -/
  auxCount : (kappa : ℕ) → (p : ℕ+) → Fn kappa p → ℕ
  /-- Explicit non-output coordinates in the order used on machine inputs. -/
  mCoord : ∀ kappa p f, MIdx kappa p f ≃ Fin (mCount kappa p f)
  /-- Explicit auxiliary coordinates in the order used on machine inputs. -/
  tCoord : ∀ kappa p f, TIdx kappa p f ≃ Fin (auxCount kappa p f)
  /-- There is one fewer auxiliary coordinate than non-output coordinates. -/
  auxCount_add_one : ∀ kappa p f, auxCount kappa p f + 1 = mCount kappa p f
  /-- The distinguished coordinate receiving the simulated allowed value. -/
  m0 : ∀ kappa p f, MIdx kappa p f
  /-- The distinguished coordinate is the first encoded non-output coordinate. -/
  m0_coord : ∀ kappa p f, (mCoord kappa p f (m0 kappa p f)).val = 0
  /-- The width of a function's binary description. -/
  fnLen : ℕ → ℕ+ → ℕ
  /-- The fixed-width encoding of a function. -/
  encFn : ∀ kappa p, Fn kappa p → Fin (fnLen kappa p) → Bool
  /-- Equal function descriptions represent equal functions of the family. -/
  encFn_inj : ∀ kappa p, Function.Injective (encFn kappa p)
  /-- Evaluation of the represented polynomial vector at the public input. -/
  eval : ∀ kappa p, Fn kappa p → (Fin (l.eval kappa) → ZMod (p : ℕ)) →
    Fin (n.eval kappa) → ZMod (p : ℕ)
  /-- The public-variable coefficient matrix, with corrected shape t×(ℓm). -/
  L1 : ∀ kappa p f,
    Matrix (TIdx kappa p f ⊕ Fin (n.eval kappa))
      (Fin (l.eval kappa) × MIdx kappa p f) (ZMod (p : ℕ))
  /-- The constant coefficient matrix, with corrected shape t×m. -/
  L0 : ∀ kappa p f,
    Matrix (TIdx kappa p f ⊕ Fin (n.eval kappa)) (MIdx kappa p f) (ZMod (p : ℕ))
  /-- The reconstruction vector, with output coordinates followed by non-output ones. -/
  recVec : ∀ (kappa : ℕ) (p : ℕ+) (f : Fn kappa p), (Fin (l.eval kappa) → ZMod (p : ℕ)) →
    (Fin (n.eval kappa) ⊕ MIdx kappa p f) → ZMod (p : ℕ)
  /-- Every draw reconstructs the allowed scalar by the displayed dot product. -/
  rec_spec : ∀ kappa p f x z t,
    dotProduct (pgbCore (L1 kappa p f) (L0 kappa p f) x z t) (recVec kappa p f x) =
      dotProduct z (eval kappa p f x)
  /-- Real and simulated garblings have exactly equal expectations for every test. -/
  privacy : ∀ kappa p f x z
    (test : ((Fin (n.eval kappa) ⊕ MIdx kappa p f) → ZMod (p : ℕ)) → ℝ),
    ProbComp.expect
        (ProbComp.sample ((TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)))
        (fun t => test (pgbCore (L1 kappa p f) (L0 kappa p f) x z t)) =
      ProbComp.expect
        (ProbComp.sample ((TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)))
        (fun t => test (pgbStarCore (L1 kappa p f) (L0 kappa p f) (m0 kappa p f)
          x (dotProduct z (eval kappa p f x)) t))

namespace Raw

variable {l n : PolyExpr} {Fn : (kappa : ℕ) → ℕ+ → Type}

instance instFintypeM (S : Raw l n Fn) (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    Fintype (S.MIdx kappa p f) := S.mFinite kappa p f

instance instFintypeT (S : Raw l n Fn) (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    Fintype (S.TIdx kappa p f) := S.tFinite kappa p f

instance instDecidableEqM (S : Raw l n Fn) (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    DecidableEq (S.MIdx kappa p f) := S.mDecEq kappa p f

instance instDecidableEqT (S : Raw l n Fn) (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    DecidableEq (S.TIdx kappa p f) := S.tDecEq kappa p f

variable (S : Raw l n Fn)

/-- The real partial garbling of a raw family is defined from its two matrices.
[AGW20, Lemma 2, p.12, corrected by Appendix A, (32), p.38]. -/
def pgb (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ))
    (z : Fin (n.eval kappa) → ZMod (p : ℕ))
    (t : (S.TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)) :
    (Fin (n.eval kappa) ⊕ S.MIdx kappa p f) → ZMod (p : ℕ) :=
  pgbCore (S.L1 kappa p f) (S.L0 kappa p f) x z t

/-- The real garbling is `pgbCore` of the raw family's matrices. -/
theorem pgb_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ))
    (z : Fin (n.eval kappa) → ZMod (p : ℕ))
    (t : (S.TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)) :
    S.pgb kappa p f x z t = pgbCore (S.L1 kappa p f) (S.L0 kappa p f) x z t := rfl

/-- The simulated partial garbling is defined from the raw matrices and its
first non-output coordinate. [AGW20, Lemma 2, p.12; Appendix A, p.38]. -/
def pgbStar (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ)) (mu : ZMod (p : ℕ))
    (t : (S.TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)) :
    (Fin (n.eval kappa) ⊕ S.MIdx kappa p f) → ZMod (p : ℕ) :=
  pgbStarCore (S.L1 kappa p f) (S.L0 kappa p f) (S.m0 kappa p f) x mu t

/-- The simulated garbling is `pgbStarCore` of the raw matrices and distinguished
coordinate. -/
theorem pgbStar_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ)) (mu : ZMod (p : ℕ))
    (t : (S.TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)) :
    S.pgbStar kappa p f x mu t =
      pgbStarCore (S.L1 kappa p f) (S.L0 kappa p f) (S.m0 kappa p f) x mu t := rfl

/-- Every canonical real garbling reconstructs the allowed scalar, for every draw.
[AGW20, Lemma 2, p.12]. -/
theorem reconstruct (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ))
    (z : Fin (n.eval kappa) → ZMod (p : ℕ))
    (t : (S.TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)) :
    dotProduct (S.pgb kappa p f x z t) (S.recVec kappa p f x) =
      dotProduct z (S.eval kappa p f x) := S.rec_spec kappa p f x z t

/-- Real and simulated canonical garblings have identical laws, expressed by
expectation equality for every real-valued test. [IW14, Definition 1, p.6]. -/
theorem exactPrivacy (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ))
    (z : Fin (n.eval kappa) → ZMod (p : ℕ))
    (test : ((Fin (n.eval kappa) ⊕ S.MIdx kappa p f) → ZMod (p : ℕ)) → ℝ) :
    ProbComp.expect
        (ProbComp.sample ((S.TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)))
        (fun t => test (S.pgb kappa p f x z t)) =
      ProbComp.expect
        (ProbComp.sample ((S.TIdx kappa p f ⊕ Fin (n.eval kappa)) → ZMod (p : ℕ)))
        (fun t => test (S.pgbStar kappa p f x (dotProduct z (S.eval kappa p f x)) t)) :=
  S.privacy kappa p f x z test

/-- Draw rows are ordered with auxiliary coordinates first, followed by the last
n output coordinates, exactly as in [AGW20, Appendix A, (31), p.38]. -/
def rowCoord (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    (S.TIdx kappa p f ⊕ Fin (n.eval kappa)) ≃
      Fin (S.auxCount kappa p f + n.eval kappa) :=
  (Equiv.sumCongr (S.tCoord kappa p f) (Equiv.refl _)).trans finSumFinEquiv

/-- The draw-row coordinate equivalence is the sum of the supplied auxiliary
coordinate equivalence and the identity, followed by `finSumFinEquiv`. -/
theorem rowCoord_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    S.rowCoord kappa p f =
      (Equiv.sumCongr (S.tCoord kappa p f) (Equiv.refl _)).trans finSumFinEquiv := rfl

/-- L1 columns are ordered by public-variable coordinate and then non-output
coordinate. This is the block ordering in [AGW20, Appendix A, (32), p.38]. -/
def l1ColCoord (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    (Fin (l.eval kappa) × S.MIdx kappa p f) ≃
      Fin (l.eval kappa * S.mCount kappa p f) :=
  (Equiv.prodCongr (Equiv.refl _) (S.mCoord kappa p f)).trans finProdFinEquiv

/-- The L1 column equivalence is the product of the identity and the supplied
non-output coordinate equivalence, followed by `finProdFinEquiv`. -/
theorem l1ColCoord_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    S.l1ColCoord kappa p f =
      (Equiv.prodCongr (Equiv.refl _) (S.mCoord kappa p f)).trans finProdFinEquiv := rfl

/-- Garbling coordinates are ordered with output coordinates first, then
non-output coordinates, as in [AGW20, Appendix A, (31), p.38]. -/
def outputCoord (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    (Fin (n.eval kappa) ⊕ S.MIdx kappa p f) ≃
      Fin (n.eval kappa + S.mCount kappa p f) :=
  (Equiv.sumCongr (Equiv.refl _) (S.mCoord kappa p f)).trans finSumFinEquiv

/-- The output-coordinate equivalence is the sum of the identity and the
supplied non-output coordinate equivalence, followed by `finSumFinEquiv`. -/
theorem outputCoord_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    S.outputCoord kappa p f =
      (Equiv.sumCongr (Equiv.refl _) (S.mCoord kappa p f)).trans finSumFinEquiv := rfl

/-- A non-output index is encoded by the fixed-width binary numeral of its
supplied finite coordinate. This is representation glue. -/
def encMIdx (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) (u : S.MIdx kappa p f) : List Bool :=
  Candidates.natToList (Nat.size (S.mCount kappa p f)) (S.mCoord kappa p f u).val

/-- The non-output index encoding is the numeral of its finite coordinate. -/
theorem encMIdx_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) (u : S.MIdx kappa p f) :
    S.encMIdx kappa p f u =
      Candidates.natToList (Nat.size (S.mCount kappa p f)) (S.mCoord kappa p f u).val := rfl

/-- An auxiliary index is encoded by the fixed-width binary numeral of its
supplied finite coordinate. This is representation glue. -/
def encTIdx (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) (u : S.TIdx kappa p f) : List Bool :=
  Candidates.natToList (Nat.size (S.auxCount kappa p f)) (S.tCoord kappa p f u).val

/-- The auxiliary index encoding is the numeral of its finite coordinate. -/
theorem encTIdx_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) (u : S.TIdx kappa p f) :
    S.encTIdx kappa p f u =
      Candidates.natToList (Nat.size (S.auxCount kappa p f)) (S.tCoord kappa p f u).val := rfl

/-- The matrix-generation output is the nested pair of the two row-major matrix
encodings, at the modulus's binary width. Existing modular encodings are reused. -/
def encLgen (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) : List Bool :=
  pairEncode
    (Encoding.Modular.encodeMatrix (Nat.size (p : ℕ))
      (fun i j => S.L1 kappa p f ((S.rowCoord kappa p f).symm i)
        ((S.l1ColCoord kappa p f).symm j)))
    (Encoding.Modular.encodeMatrix (Nat.size (p : ℕ))
      (fun i j => S.L0 kappa p f ((S.rowCoord kappa p f).symm i)
        ((S.mCoord kappa p f).symm j)))

/-- The matrix-generation output is the pair of the displayed modular matrix
encodings, in the supplied canonical coordinate orders. -/
theorem encLgen_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    S.encLgen kappa p f = pairEncode
      (Encoding.Modular.encodeMatrix (Nat.size (p : ℕ))
        (fun i j => S.L1 kappa p f ((S.rowCoord kappa p f).symm i)
          ((S.l1ColCoord kappa p f).symm j)))
      (Encoding.Modular.encodeMatrix (Nat.size (p : ℕ))
        (fun i j => S.L0 kappa p f ((S.rowCoord kappa p f).symm i)
          ((S.mCoord kappa p f).symm j))) := rfl

/-- The reconstruction output is the fixed-width modular vector encoding in the
canonical garbling-coordinate order. Existing modular encodings are reused. -/
def encRec (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ)) : List Bool :=
  Encoding.Modular.encodeVector (Nat.size (p : ℕ))
    (fun i => S.recVec kappa p f x ((S.outputCoord kappa p f).symm i))

/-- The reconstruction output is the displayed modular vector encoding. -/
theorem encRec_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ)) :
    S.encRec kappa p f x = Encoding.Modular.encodeVector (Nat.size (p : ℕ))
      (fun i => S.recVec kappa p f x ((S.outputCoord kappa p f).symm i)) := rfl

/-- Matrix generation reads the unary security parameter and the pair of public
parameters with the function description. This is uniform input-layout glue. -/
def lgenInput (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) : List Bool :=
  NUPPT.advInput kappa (pairEncode (paramWord l n kappa p) (List.ofFn (S.encFn kappa p f)))

/-- The matrix-generation input is the displayed adversary-input layout, with
modulus and dimensions supplied in `paramWord`. -/
theorem lgenInput_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p) :
    S.lgenInput kappa p f = NUPPT.advInput kappa
      (pairEncode (paramWord l n kappa p) (List.ofFn (S.encFn kappa p f))) := rfl

/-- Reconstruction reads the security parameter, public parameters, function
and public input. All residues use the positive modulus supplied on the input. -/
def recInput (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ)) : List Bool :=
  NUPPT.advInput kappa (pairEncode (paramWord l n kappa p)
    (pairEncode (List.ofFn (S.encFn kappa p f))
      (Encoding.Modular.encodeVector (Nat.size (p : ℕ)) x)))

/-- The reconstruction input is the displayed nested pair containing the
function description and fixed-width public-input residues. -/
theorem recInput_eq (kappa : ℕ) (p : ℕ+) (f : Fn kappa p)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ)) :
    S.recInput kappa p f x = NUPPT.advInput kappa (pairEncode (paramWord l n kappa p)
      (pairEncode (List.ofFn (S.encFn kappa p f))
        (Encoding.Modular.encodeVector (Nat.size (p : ℕ)) x))) := rfl

end Raw
end PartialGarbling

/-- A partial-garbling interface includes uniform efficient matrix generation
and reconstruction. [AGW20, Lemma 2, p.12; IW14, Definition 1 continuation, p.7].
One polynomial-time map is chosen before κ and the positive modulus in each
field. The other two algorithms are the canonical matrix formulas, so they
require no independently chosen algorithm or sampler. -/
structure PartialGarbling (l n : PolyExpr) (Fn : (kappa : ℕ) → ℕ+ → Type)
    extends PartialGarbling.Raw l n Fn where
  /-- One deterministic polynomial-time map generates both encoded matrices for
  all security parameters, positive moduli and encoded functions. -/
  lgen_eff : ∃ a : List Bool → List Bool, PolyTimeComputable a ∧
    ∀ kappa (p : ℕ+) (f : Fn kappa p),
      a (toRaw.lgenInput kappa p f) = toRaw.encLgen kappa p f
  /-- One deterministic polynomial-time map reconstructs the encoded vector for
  all security parameters, positive moduli, functions and public inputs. -/
  rec_eff : ∃ a : List Bool → List Bool, PolyTimeComputable a ∧
    ∀ kappa (p : ℕ+) (f : Fn kappa p) (x : Fin (l.eval kappa) → ZMod (p : ℕ)),
      a (toRaw.recInput kappa p f x) = toRaw.encRec kappa p f x

namespace PartialGarbling

variable {l n : PolyExpr} {Fn : (kappa : ℕ) → ℕ+ → Type} (S : PartialGarbling l n Fn)

/-- The efficient interface's raw family has the same non-output index types. -/
theorem toRaw_MIdx : S.toRaw.MIdx = S.MIdx := rfl

/-- The efficient interface's raw family has the same auxiliary index types. -/
theorem toRaw_TIdx : S.toRaw.TIdx = S.TIdx := rfl

/-- The efficient interface's raw family has the same coefficient matrices L1. -/
theorem toRaw_L1 : S.toRaw.L1 = S.L1 := rfl

/-- The efficient interface's raw family has the same constant matrices L0. -/
theorem toRaw_L0 : S.toRaw.L0 = S.L0 := rfl

/-- The efficient interface's raw family has the same reconstruction vectors. -/
theorem toRaw_rec : S.toRaw.recVec = S.recVec := rfl

/-- The efficient interface's raw family has the same evaluated vector functions. -/
theorem toRaw_eval : S.toRaw.eval = S.eval := rfl

end PartialGarbling

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
