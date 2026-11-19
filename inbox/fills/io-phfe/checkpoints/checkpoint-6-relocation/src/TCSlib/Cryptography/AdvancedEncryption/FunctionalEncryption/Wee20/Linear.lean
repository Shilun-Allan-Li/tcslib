/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Exponents
import TCSlib.Cryptography.Pairing.MatrixDH.Parameters
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The raw linear PHFE building block

The internal scheme Π encrypts a group-valued private vector and issues keys carrying an
arbitrary source-group matrix. All algorithms are explicit deterministic cores with one
finite draw type for each randomized algorithm. A function's partial-garbling coordinates
may depend on the function; its key draw has those same coordinates.

## Main definitions

* `Wee20.Linear.MPK`, `MSK`, `CT`, `Key`: the typed keys and ciphertext of Π.
* `Wee20.Linear.SetupDraw`, `EncDraw`, `KeyDraw`: the honest algorithms' exact draw types.
* `Wee20.Linear.setupCore`, `encCore`, `keyCore`, `dec`: the algorithms of Π.
* `Wee20.Linear.setup`, `enc`, `keyGen`: the exact core-plus-draw laws.
* `Wee20.Linear.leak`: source-group evaluation of a group matrix at known scalar inputs.
* `Wee20.Linear.RawAlgorithms`, `scheme_raw`: the internal raw algorithm bundle.

## Main results

Equation readers expose every core, draw type, law and raw bundle. Correctness is stated in
`LinearCorrect`; the simulator is in `LinearSimulator`.

The private input length and function-vector output length are separate parameters. In
particular, the last block of `T` has the function-vector output length, so `T̲+WM` is valid
for the rectangular matrices used by the outer construction. No group element is decoded
to a scalar, and no discrete logarithm is used.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §4, p. 8 (group-matrix keys),
  §4.2, pp. 9–10 (Π and correctness equations (6)–(11)).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Π's public key holds `[A]`, `[AW]`, `[AU]` and `[AV]`
[Wee20, §4.2, p. 9, Setup]. -/
structure MPK (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The two-by-three implicit matrix. -/
  A : Matrix (Fin 2) (Fin 3) pp.group.G
  /-- The implicit private-input mask. -/
  AW : Matrix (Fin 2) (Fin (zDim.eval κ)) pp.group.G
  /-- The implicit public-variable mask. -/
  AU : Matrix (Fin 2) (Fin (ℓ.eval κ) × Fin 2) pp.group.G
  /-- The implicit constant mask. -/
  AV : Matrix (Fin 2) (Fin 2) pp.group.G

/-- Π's master secret consists of its three scalar masking matrices
[Wee20, §4.2, p. 9, Setup]. -/
structure MSK (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The private-input masking matrix. -/
  W : Matrix (Fin 3) (Fin (zDim.eval κ)) (ZMod pp.group.order)
  /-- The public-variable masking matrix. -/
  U : Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) (ZMod pp.group.order)
  /-- The constant masking matrix. -/
  V : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)

/-- Π's ciphertext has its three source-group blocks, with the public input supplied
separately to decryption [Wee20, §4.2, p. 9, Enc]. -/
structure CT (G : BilinearGen) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The three-coordinate mask `[sA]`. -/
  c0 : Fin 3 → pp.group.G
  /-- The masked private input. -/
  c1 : Fin (zDim.eval κ) → pp.group.G
  /-- The two-coordinate public-input mask. -/
  c2 : Fin 2 → pp.group.G

/-- A function key contains the three garbling blocks and `[R]`
[Wee20, §4.2, p. 9, KeyGen]. The function and its group matrix are explicit key metadata. -/
structure Key (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) where
  /-- The three-by-output first block. -/
  K1 : Matrix (Fin 3) (Fin (n'.eval κ)) pp.group.G
  /-- The public-variable garbling block. -/
  K2 : Matrix (Fin 3) (Fin (ℓ.eval κ) × PG.MIdx κ pp.orderParam f) pp.group.G
  /-- The constant garbling block. -/
  K3 : Matrix (Fin 3) (PG.MIdx κ pp.orderParam f) pp.group.G
  /-- The two-row reconstruction mask. -/
  R : Matrix (Fin 2) (PG.MIdx κ pp.orderParam f) pp.group.G

/-- Setup's single draw contains independent uniform `A,W,U,V`
[Wee20, §4.2, p. 9, Setup]. -/
abbrev SetupDraw (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  Matrix (Fin 2) (Fin 3) (ZMod pp.group.order) ×
    Matrix (Fin 3) (Fin (zDim.eval κ)) (ZMod pp.group.order) ×
    Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) (ZMod pp.group.order) ×
    Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)

/-- The setup draw type is exactly its four scalar matrices. -/
theorem setupDraw_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    SetupDraw G ℓ zDim κ pp =
      (Matrix (Fin 2) (Fin 3) (ZMod pp.group.order) ×
        Matrix (Fin 3) (Fin (zDim.eval κ)) (ZMod pp.group.order) ×
        Matrix (Fin 3) (Fin (ℓ.eval κ) × Fin 2) (ZMod pp.group.order) ×
        Matrix (Fin 3) (Fin 2) (ZMod pp.group.order)) := rfl

/-- Encryption draws its two scalar coefficients [Wee20, §4.2, p. 9, Enc]. -/
abbrev EncDraw (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :=
  Fin 2 → ZMod pp.group.order

/-- Encryption randomness is a two-coordinate scalar vector. -/
theorem encDraw_eq (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :
    EncDraw G κ pp = (Fin 2 → ZMod pp.group.order) := rfl

/-- Key generation draws `T` and `R` in the function's actual garbling coordinates
[Wee20, §4.2, p. 9, KeyGen]. The last block of `T` has output length `n'`. -/
abbrev KeyDraw (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :=
  Matrix (Fin 3) (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) (ZMod pp.group.order) ×
    Matrix (Fin 2) (PG.MIdx κ pp.orderParam f) (ZMod pp.group.order)

/-- The key draw type is the product of the `T` and `R` matrix types. -/
theorem keyDraw_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :
    KeyDraw G PG κ pp f =
      (Matrix (Fin 3) (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ))
          (ZMod pp.group.order) ×
        Matrix (Fin 2) (PG.MIdx κ pp.orderParam f) (ZMod pp.group.order)) := rfl

instance instSetupDrawFinite (G : BilinearGen) (ℓ z : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    Fintype (SetupDraw G ℓ z κ pp) := inferInstance

instance instSetupDrawNonempty (G : BilinearGen) (ℓ z : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    Nonempty (SetupDraw G ℓ z κ pp) := inferInstance

instance instEncDrawFinite (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :
    Fintype (EncDraw G κ pp) := inferInstance

instance instEncDrawNonempty (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :
    Nonempty (EncDraw G κ pp) := inferInstance

instance instKeyDrawFinite (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :
    Fintype (KeyDraw G PG κ pp f) := inferInstance

instance instKeyDrawNonempty (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :
    Nonempty (KeyDraw G PG κ pp f) := inferInstance

/-- Setup exponentiates the four public matrices and retains `W,U,V`
[Wee20, §4.2, p. 9, Setup]. -/
def setupCore (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SetupDraw G ℓ zDim κ pp) : MPK G ℓ zDim κ pp × MSK G ℓ zDim κ pp :=
  let A := ω.1
  let W := ω.2.1
  let U := ω.2.2.1
  let V := ω.2.2.2
  (⟨pp.group.expMat pp.generator A, pp.group.expMat pp.generator (A * W),
    pp.group.expMat pp.generator (A * U), pp.group.expMat pp.generator (A * V)⟩,
    ⟨W, U, V⟩)

/-- Setup's core is the displayed public exponentiation and secret-matrix tuple. -/
theorem setupCore_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SetupDraw G ℓ zDim κ pp) :
    setupCore G ℓ zDim κ pp ω =
      (⟨pp.group.expMat pp.generator ω.1,
        pp.group.expMat pp.generator (ω.1 * ω.2.1),
        pp.group.expMat pp.generator (ω.1 * ω.2.2.1),
        pp.group.expMat pp.generator (ω.1 * ω.2.2.2)⟩, ⟨ω.2.1, ω.2.2.1, ω.2.2.2⟩) := rfl

/-- Encryption forms the three group ciphertext blocks from a group-valued private input
[Wee20, §4.2, p. 9, Enc]. Only products and powers by known scalars are used. -/
def encCore (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (pk : MPK G ℓ zDim κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → pp.group.G) (s : EncDraw G κ pp) : CT G zDim κ pp :=
  ⟨groupVecMul s pk.A, z * groupVecMul s pk.AW,
    groupVecMul s (groupMatMul pk.AU
      (PartialGarbling.publicTensor (p := pp.orderParam) (M := Fin 2) x)) *
      groupVecMul s pk.AV⟩

/-- The encryption core uses the canonical public tensor and the three public-key blocks. -/
theorem encCore_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (pk : MPK G ℓ zDim κ pp)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (z : Fin (zDim.eval κ) → pp.group.G)
    (s : EncDraw G κ pp) :
    encCore G ℓ zDim κ pp pk x z s =
      ⟨groupVecMul s pk.A, z * groupVecMul s pk.AW,
        groupVecMul s (groupMatMul pk.AU
          (PartialGarbling.publicTensor (p := pp.orderParam) (M := Fin 2) x)) *
          groupVecMul s pk.AV⟩ := rfl

/-- Key generation computes `[T̲+WM]`, `[TL1+U(I⊗R)]`, `[TL0+VR]`, `[R]`
[Wee20, §4.2, p. 9, KeyGen]. The matrix `M` is supplied only in the source group. -/
def keyCore (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (msk : MSK G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (ω : KeyDraw G PG κ pp f) : Key G PG κ pp f :=
  let T := ω.1
  let R := ω.2
  let Tbar := fun i j => T i (Sum.inr j)
  let tensorR := Matrix.kroneckerMap (fun a b => a * b)
    (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) R
  ⟨pp.group.expMat pp.generator Tbar ⊙ matMulGroup msk.W M,
    pp.group.expMat pp.generator (T * (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ
      pp.orderParam f) + msk.U * tensorR),
    pp.group.expMat pp.generator (T * (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ
      pp.orderParam f) + msk.V * R),
    pp.group.expMat pp.generator R⟩

/-- Key generation is the displayed scalar garbling arithmetic and group matrix action. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem keyCore_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (msk : MSK G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (ω : KeyDraw G PG κ pp f) :
    keyCore G PG zDim κ pp msk f M ω =
      let tensorR := Matrix.kroneckerMap (fun a b => a * b)
        (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) ω.2
      ⟨pp.group.expMat pp.generator (fun i j => ω.1 i (Sum.inr j)) ⊙ matMulGroup msk.W M,
        pp.group.expMat pp.generator
          (ω.1 * (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) + msk.U *
            tensorR),
        pp.group.expMat pp.generator
          (ω.1 * (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f) + msk.V *
            ω.2),
        pp.group.expMat pp.generator ω.2⟩ := rfl

/-- Decryption's first block is `e(c1,M)/e(c0,K1)`
[Wee20, §4.2, p. 9, (6)]. -/
def decFirst (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (sk : Key G PG κ pp f) (ct : CT G zDim κ pp) : Fin (n'.eval κ) → pp.group.GT :=
  fun j => pp.group.pairVec ct.c1 (fun a => M a j) *
    (pp.group.pairVec ct.c0 (fun i => sk.K1 i j))⁻¹

/-- Each first-block coordinate is its two vector-pairing factors. -/
theorem decFirst_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (sk : Key G PG κ pp f) (ct : CT G zDim κ pp) :
    decFirst G PG zDim κ pp f M sk ct = fun j =>
      pp.group.pairVec ct.c1 (fun a => M a j) *
        (pp.group.pairVec ct.c0 (fun i => sk.K1 i j))⁻¹ := rfl

/-- Decryption's second block cancels the public-input mask by pairings
[Wee20, §4.2, p. 9, (7)]. -/
def decSecond (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (sk : Key G PG κ pp f) (ct : CT G zDim κ pp) : PG.MIdx κ pp.orderParam f → pp.group.GT :=
  let K := groupMatMul sk.K2
    (PartialGarbling.publicTensor (p := pp.orderParam) (M := PG.MIdx κ pp.orderParam f) x)
  fun u => pp.group.pairVec ct.c0 (fun i => K i u * sk.K3 i u) *
    (pp.group.pairVec ct.c2 (fun i => sk.R i u))⁻¹

/-- The second block uses the canonical public tensor on the function's garbling nodes. -/
theorem decSecond_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (sk : Key G PG κ pp f) (ct : CT G zDim κ pp) :
    decSecond G PG zDim κ pp f x sk ct =
      let K := groupMatMul sk.K2
        (PartialGarbling.publicTensor (p := pp.orderParam)
          (M := PG.MIdx κ pp.orderParam f) x)
      fun u => pp.group.pairVec ct.c0 (fun i => K i u * sk.K3 i u) *
        (pp.group.pairVec ct.c2 (fun i => sk.R i u))⁻¹ := rfl

/-- Decryption applies the scalar reconstruction vector to the paired garbling blocks
[Wee20, §4.2, p. 9, (8)]. It returns the result in the target group. -/
def dec (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (sk : Key G PG κ pp f)
    (ct : CT G zDim κ pp) : pp.group.GT :=
  groupDot (Sum.elim (decFirst G PG zDim κ pp f M sk ct)
    (decSecond G PG zDim κ pp f x sk ct)) (PG.recVec κ pp.orderParam f x)

/-- Decryption is the known-power product specified by the reconstruction vector. -/
theorem dec_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (sk : Key G PG κ pp f)
    (ct : CT G zDim κ pp) :
    dec G PG zDim κ pp f M x sk ct =
      groupDot (Sum.elim (decFirst G PG zDim κ pp f M sk ct)
        (decSecond G PG zDim κ pp f x sk ct)) (PG.recVec κ pp.orderParam f x) := rfl

/-- Compute `[z M f(x)^T]` from an arbitrary group matrix and the known scalar input and
function value [Wee20, §4, p. 8]. This is Π's simulator leakage. -/
def leak (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order) : pp.group.G :=
  groupDot (groupMulVec M (PG.eval κ pp.orderParam f x)) z

/-- The leakage uses only known powers of the supplied group matrix. -/
theorem leak_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order) :
    leak G PG zDim κ pp f M x z =
      groupDot (groupMulVec M (PG.eval κ pp.orderParam f x)) z := rfl

/-- Honest setup is uniform sampling of its one draw type followed by the core
[Wee20, §4.2, p. 9]. -/
noncomputable def setup (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : ProbComp (MPK G ℓ zDim κ pp × MSK G ℓ zDim κ pp) :=
  (setupCore G ℓ zDim κ pp <$> (ProbComp.sample (SetupDraw G ℓ zDim κ pp)))

/-- Honest setup has the displayed core-plus-draw law. -/
theorem setup_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    setup G ℓ zDim κ pp =
      (setupCore G ℓ zDim κ pp <$> (ProbComp.sample (SetupDraw G ℓ zDim κ pp))) := rfl

/-- Honest encryption samples its two scalars and applies the core [Wee20, §4.2, p. 9]. -/
noncomputable def enc (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (pk : MPK G ℓ zDim κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → pp.group.G) : ProbComp (CT G zDim κ pp) :=
  (encCore G ℓ zDim κ pp pk x z <$> (ProbComp.sample (EncDraw G κ pp)))

/-- Honest encryption has the displayed core-plus-draw law. -/
theorem enc_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (pk : MPK G ℓ zDim κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → pp.group.G) :
    enc G ℓ zDim κ pp pk x z =
      (encCore G ℓ zDim κ pp pk x z <$> (ProbComp.sample (EncDraw G κ pp))) := rfl

/-- Honest key generation samples its actual function-dependent matrices and applies the
core [Wee20, §4.2, p. 9]. This is one draw, not a product-sampler construction. -/
noncomputable def keyGen (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (msk : MSK G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G) :
    ProbComp (Key G PG κ pp f) :=
  (keyCore G PG zDim κ pp msk f M <$> (ProbComp.sample (KeyDraw G PG κ pp f)))

/-- Honest key generation has the displayed core-plus-draw law. -/
theorem keyGen_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (msk : MSK G ℓ zDim κ pp) (f : Fn κ pp.orderParam)
    (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G) :
    keyGen G PG zDim κ pp msk f M =
      (keyCore G PG zDim κ pp msk f M <$> (ProbComp.sample (KeyDraw G PG κ pp f))) := rfl

/-- Π is an internal raw bundle of cores, with efficiency supplied only through the outer
construction's targets [Wee20, §4.2, pp. 9–10]. -/
structure RawAlgorithms (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- Honest setup core. -/
  setupCore : SetupDraw G ℓ zDim κ pp → MPK G ℓ zDim κ pp × MSK G ℓ zDim κ pp
  /-- Honest encryption core on a source-group private vector. -/
  encCore : MPK G ℓ zDim κ pp → (Fin (ℓ.eval κ) → ZMod pp.group.order) →
    (Fin (zDim.eval κ) → pp.group.G) → EncDraw G κ pp → CT G zDim κ pp
  /-- Honest function-dependent key-generation core. -/
  keyCore : MSK G ℓ zDim κ pp → (f : Fn κ pp.orderParam) →
    Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G →
    KeyDraw G PG κ pp f → Key G PG κ pp f
  /-- Deterministic decryption in the target group. -/
  dec : (f : Fn κ pp.orderParam) →
    Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G →
    (Fin (ℓ.eval κ) → ZMod pp.group.order) → Key G PG κ pp f → CT G zDim κ pp → pp.group.GT

/-- Assemble the four explicit cores into Π's internal raw bundle
[Wee20, §4.2, pp. 9–10]. No efficient interface is instantiated here. -/
def scheme_raw (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    RawAlgorithms G PG zDim κ pp :=
  ⟨setupCore G ℓ zDim κ pp, encCore G ℓ zDim κ pp,
    keyCore G PG zDim κ pp, dec G PG zDim κ pp⟩

/-- The raw bundle contains exactly the four explicitly defined cores. -/
theorem scheme_raw_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    scheme_raw G PG zDim κ pp =
      ⟨setupCore G ℓ zDim κ pp, encCore G ℓ zDim κ pp,
        keyCore G PG zDim κ pp, dec G PG zDim κ pp⟩ := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
