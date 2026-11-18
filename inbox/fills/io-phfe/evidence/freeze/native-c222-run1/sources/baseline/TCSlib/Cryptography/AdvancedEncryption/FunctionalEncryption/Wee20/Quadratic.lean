/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The raw quadratic PHFE construction

The public key stores the two masking matrices in the source group and Π's public key.
Encryption knows its private scalars and its fresh masks but only knows `y1` in the source
group. The signal supplied to Π therefore uses known powers of group `y1`; it never
recovers the sampled public matrix or the masked input as scalars.

## Main definitions

* `Wee20.Quadratic.piDim`, `signalCoord`: the linear input length and canonical coordinates.
* `Wee20.Quadratic.mixScalar`, `mixGroup`: the two Kronecker blocks of the fixed matrix.
* `Wee20.Quadratic.signalScalar`, `signalGroup`: the scalar proof representation and actual
  group algorithm for the signal supplied to Π.
* `Wee20.Quadratic.MPK`, `MSK`, `CT`, `Key`: the outer raw data.
* `Wee20.Quadratic.setupCore`, `encCore`, `keyCore`, `dec`: the explicit outer algorithms.
* `Wee20.Quadratic.setup`, `enc`, `keyGen`: their exact core-plus-draw laws.
* `Wee20.Quadratic.value`, `RawAlgorithms`, `scheme_raw`: scalar evaluation and raw bundle.

## Main results

Every definition has an equation reader. Correctness is in `QuadraticCorrect` and the
stateful raw simulator is in `QuadraticSimulator`.

The fixed group matrix is public metadata retained with the master key and each function
key, matching Π's per-key group-matrix form. In the symmetric group the two source-group
copies of the first masking matrix coincide. No unused outer `s0` is sampled.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3.1, p. 6, Setup, Enc,
  KeyGen, Dec, and equations (4)–(5); §4, p. 8 (per-key group matrices).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Π's private input has length `2*n2+n1*2`, the concatenated cross terms
[Wee20, §3.1, p. 6, Enc, with k=k'=2]. -/
def piDim (n1 n2 : PolyExpr) : PolyExpr :=
  ((PolyExpr.const 2).mul n2).add (n1.mul (PolyExpr.const 2))

/-- The linear private-input dimension is the displayed sum of two product dimensions. -/
theorem piDim_eq (n1 n2 : PolyExpr) :
    piDim n1 n2 = ((PolyExpr.const 2).mul n2).add (n1.mul (PolyExpr.const 2)) := rfl

/-- Signal coordinates order the first tensor block before the second, using the existing
finite-product and finite-sum equivalences [Wee20, §3.1, p. 6, Enc]. -/
def signalCoord (n1 n2 : ℕ) :
    ((Fin 2 × Fin n2) ⊕ (Fin n1 × Fin 2)) ≃ Fin (2 * n2 + n1 * 2) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

/-- The signal ordering is the canonical finite product/sum ordering. -/
theorem signalCoord_eq (n1 n2 : ℕ) :
    signalCoord n1 n2 =
      (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv := rfl

/-- The scalar matrix stacks `A1⊗I_n2` over `I_n1⊗A2`
[Wee20, §3.1, p. 6, Setup]. It is used for algebraic statements about sampled setup coins. -/
def mixScalar {p : ℕ+} {n1 n2 : ℕ}
    (A1 : Matrix (Fin 2) (Fin n1) (ZMod (p : ℕ)))
    (A2 : Matrix (Fin 2) (Fin n2) (ZMod (p : ℕ))) :
    Matrix (Fin (2 * n2 + n1 * 2)) (Fin (n1 * n2)) (ZMod (p : ℕ)) :=
  let top := Matrix.kroneckerMap (fun a b => a * b) A1
    (1 : Matrix (Fin n2) (Fin n2) (ZMod (p : ℕ)))
  let bottom := Matrix.kroneckerMap (fun a b => a * b)
    (1 : Matrix (Fin n1) (Fin n1) (ZMod (p : ℕ))) A2
  fun i j => Sum.elim (fun u => top u (finProdFinEquiv.symm j))
    (fun u => bottom u (finProdFinEquiv.symm j)) ((signalCoord n1 n2).symm i)

/-- The scalar mixing matrix is the displayed pair of canonical Kronecker blocks. -/
theorem mixScalar_eq {p : ℕ+} {n1 n2 : ℕ}
    (A1 : Matrix (Fin 2) (Fin n1) (ZMod (p : ℕ)))
    (A2 : Matrix (Fin 2) (Fin n2) (ZMod (p : ℕ))) :
    mixScalar (p := p) A1 A2 =
      let top := Matrix.kroneckerMap (fun a b => a * b) A1
        (1 : Matrix (Fin n2) (Fin n2) (ZMod (p : ℕ)))
      let bottom := Matrix.kroneckerMap (fun a b => a * b)
        (1 : Matrix (Fin n1) (Fin n1) (ZMod (p : ℕ))) A2
      fun i j => Sum.elim (fun u => top u (finProdFinEquiv.symm j))
        (fun u => bottom u (finProdFinEquiv.symm j)) ((signalCoord n1 n2).symm i) := rfl

/-- Compute the fixed group matrix from public group matrices, using known identity-matrix
powers only [Wee20, §3.1, p. 6, Setup]. -/
def mixGroup (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (A1 : Matrix (Fin 2) (Fin (n1.eval κ)) pp.group.G)
    (A2 : Matrix (Fin 2) (Fin (n2.eval κ)) pp.group.G) :
    Matrix (Fin ((piDim n1 n2).eval κ)) (Fin ((n1.mul n2).eval κ)) pp.group.G :=
  let top := Matrix.kroneckerMap (fun a b => a ^ b.val) A1
    (1 : Matrix (Fin (n2.eval κ)) (Fin (n2.eval κ)) (ZMod pp.group.order))
  let bottom := Matrix.kroneckerMap (fun a b => b ^ a.val)
    (1 : Matrix (Fin (n1.eval κ)) (Fin (n1.eval κ)) (ZMod pp.group.order)) A2
  fun i j => Sum.elim (fun u => top u (finProdFinEquiv.symm j))
    (fun u => bottom u (finProdFinEquiv.symm j))
    ((signalCoord (n1.eval κ) (n2.eval κ)).symm i)

/-- The group matrix is the canonical source-group Kronecker computation. -/
theorem mixGroup_eq (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (A1 : Matrix (Fin 2) (Fin (n1.eval κ)) pp.group.G)
    (A2 : Matrix (Fin 2) (Fin (n2.eval κ)) pp.group.G) :
    mixGroup G n1 n2 κ pp A1 A2 =
      let top := Matrix.kroneckerMap (fun a b => a ^ b.val) A1
        (1 : Matrix (Fin (n2.eval κ)) (Fin (n2.eval κ)) (ZMod pp.group.order))
      let bottom := Matrix.kroneckerMap (fun a b => b ^ a.val)
        (1 : Matrix (Fin (n1.eval κ)) (Fin (n1.eval κ)) (ZMod pp.group.order)) A2
      fun i j => Sum.elim (fun u => top u (finProdFinEquiv.symm j))
        (fun u => bottom u (finProdFinEquiv.symm j))
        ((signalCoord (n1.eval κ) (n2.eval κ)).symm i) := rfl

/-- The scalar cross-term signal concatenates `s1⊗z2` with `y1⊗s2`
[Wee20, §3.1, p. 6, Enc]. This reuses the class's scalar tensor representation. -/
def signalScalar {p : ℕ+} {n1 n2 : ℕ} (s1 : Fin 2 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) (y1 : Fin n1 → ZMod (p : ℕ))
    (s2 : Fin 2 → ZMod (p : ℕ)) : Fin (2 * n2 + n1 * 2) → ZMod (p : ℕ) :=
  fun i => Sum.elim
    (fun u => privateTensor (p := p) s1 z2 (finProdFinEquiv u))
    (fun u => privateTensor (p := p) y1 s2 (finProdFinEquiv u)) ((signalCoord n1 n2).symm i)

/-- The scalar signal uses the existing private-tensor and product/sum coordinate maps. -/
theorem signalScalar_eq {p : ℕ+} {n1 n2 : ℕ} (s1 : Fin 2 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) (y1 : Fin n1 → ZMod (p : ℕ))
    (s2 : Fin 2 → ZMod (p : ℕ)) :
    signalScalar (p := p) s1 z2 y1 s2 = fun i => Sum.elim
      (fun u => privateTensor (p := p) s1 z2 (finProdFinEquiv u))
      (fun u => privateTensor (p := p) y1 s2 (finProdFinEquiv u))
      ((signalCoord n1 n2).symm i) := rfl

/-- Encryption forms its signal from known `s1,z2,s2` and GROUP `y1`
[Wee20, §3.1, p. 6, Enc]. The second block is computed by known powers of `y1`. -/
def signalGroup (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (s1 : Fin 2 → ZMod pp.group.order) (z2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → pp.group.G) (s2 : Fin 2 → ZMod pp.group.order) :
    Fin ((piDim n1 n2).eval κ) → pp.group.G :=
  fun i => Sum.elim
    (fun u => pp.group.expVec pp.generator
      (privateTensor (p := pp.orderParam) s1 z2) (finProdFinEquiv u))
    (fun u => y1 u.1 ^ (s2 u.2).val) ((signalCoord (n1.eval κ) (n2.eval κ)).symm i)

/-- The actual signal exponentiates its known first block and powers its group second block. -/
theorem signalGroup_eq (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (s1 : Fin 2 → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order) (y1 : Fin (n1.eval κ) → pp.group.G)
    (s2 : Fin 2 → ZMod pp.group.order) :
    signalGroup G n1 n2 κ pp s1 z2 y1 s2 = fun i => Sum.elim
      (fun u => pp.group.expVec pp.generator
        (privateTensor (p := pp.orderParam) s1 z2) (finProdFinEquiv u))
      (fun u => y1 u.1 ^ (s2 u.2).val) ((signalCoord (n1.eval κ) (n2.eval κ)).symm i) := rfl

/-- The public key stores the two group masking matrices and Π's public key
[Wee20, §3.1, p. 6, Setup]. Source-group copies coincide in the symmetric setting. -/
structure MPK (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The first public group mask. -/
  A1 : Matrix (Fin 2) (Fin (n1.eval κ)) pp.group.G
  /-- The second public group mask. -/
  A2 : Matrix (Fin 2) (Fin (n2.eval κ)) pp.group.G
  /-- The linear building block's public key. -/
  linear : Linear.MPK G ℓ (piDim n1 n2) κ pp

/-- The master key retains Π's secret key and the fixed PUBLIC group matrix needed by
per-key Π.KeyGen [Wee20, §3.1, p. 6; §4, p. 8, per-key matrix form]. -/
structure MSK (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The fixed public group matrix. -/
  matrix : Matrix (Fin ((piDim n1 n2).eval κ)) (Fin ((n1.mul n2).eval κ)) pp.group.G
  /-- The linear master secret key. -/
  linear : Linear.MSK G ℓ (piDim n1 n2) κ pp

/-- The ciphertext contains the two group masks and Π's ciphertext
[Wee20, §3.1, p. 6, Enc]. The public input remains separate. -/
structure CT (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The first masked private vector. -/
  y1 : Fin (n1.eval κ) → pp.group.G
  /-- The second masked private vector. -/
  y2 : Fin (n2.eval κ) → pp.group.G
  /-- The linear ciphertext for the group signal. -/
  linear : Linear.CT G (piDim n1 n2) κ pp

/-- A function key stores the public matrix metadata and the linear function key
[Wee20, §3.1, p. 6, Dec; §4, p. 8]. -/
structure Key (G : BilinearGen) (n1 n2 : PolyExpr) {ℓ : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) where
  /-- The fixed public matrix, needed without a public-key argument to decryption. -/
  matrix : Matrix (Fin ((piDim n1 n2).eval κ)) (Fin ((n1.mul n2).eval κ)) pp.group.G
  /-- The linear key for this function and matrix. -/
  linear : Linear.Key G PG κ pp f

/-- Setup draws its two scalar public masks and the linear setup randomness
[Wee20, §3.1, p. 6]. -/
abbrev SetupDraw (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  Matrix (Fin 2) (Fin (n1.eval κ)) (ZMod pp.group.order) ×
    Matrix (Fin 2) (Fin (n2.eval κ)) (ZMod pp.group.order) ×
    Linear.SetupDraw G ℓ (piDim n1 n2) κ pp

/-- The outer setup draw consists of its two masks and Π's setup draw. -/
theorem setupDraw_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    SetupDraw G ℓ n1 n2 κ pp =
      (Matrix (Fin 2) (Fin (n1.eval κ)) (ZMod pp.group.order) ×
        Matrix (Fin 2) (Fin (n2.eval κ)) (ZMod pp.group.order) ×
        Linear.SetupDraw G ℓ (piDim n1 n2) κ pp) := rfl

/-- Encryption draws its two masks and Π's encryption randomness. The unused outer `s0`
printed in [Wee20, §3.1, p. 6] is omitted. -/
abbrev EncDraw (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :=
  (Fin 2 → ZMod pp.group.order) × (Fin 2 → ZMod pp.group.order) × Linear.EncDraw G κ pp

/-- Outer encryption randomness is exactly its two masks and Π's draw. -/
theorem encDraw_eq (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :
    EncDraw G κ pp =
      ((Fin 2 → ZMod pp.group.order) × (Fin 2 → ZMod pp.group.order) ×
        Linear.EncDraw G κ pp) := rfl

instance instSetupDrawFinite (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
  :
    Fintype (SetupDraw G ℓ n1 n2 κ pp) := inferInstance

instance instSetupDrawNonempty (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G
  κ) :
    Nonempty (SetupDraw G ℓ n1 n2 κ pp) := inferInstance

instance instEncDrawFinite (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :
    Fintype (EncDraw G κ pp) := inferInstance

instance instEncDrawNonempty (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :
    Nonempty (EncDraw G κ pp) := inferInstance

/-- Setup exponentiates the two masking matrices, computes the fixed group matrix and
runs Π's setup core [Wee20, §3.1, p. 6]. -/
def setupCore (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SetupDraw G ℓ n1 n2 κ pp) : MPK G ℓ n1 n2 κ pp × MSK G ℓ n1 n2 κ pp :=
  let A1 := pp.group.expMat pp.generator ω.1
  let A2 := pp.group.expMat pp.generator ω.2.1
  let linear := Linear.setupCore G ℓ (piDim n1 n2) κ pp ω.2.2
  (⟨A1, A2, linear.1⟩, ⟨mixGroup G n1 n2 κ pp A1 A2, linear.2⟩)

/-- Setup's output is the two group masks, fixed group matrix and Π's output. -/
theorem setupCore_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SetupDraw G ℓ n1 n2 κ pp) :
    setupCore G ℓ n1 n2 κ pp ω =
      let A1 := pp.group.expMat pp.generator ω.1
      let A2 := pp.group.expMat pp.generator ω.2.1
      let linear := Linear.setupCore G ℓ (piDim n1 n2) κ pp ω.2.2
      (⟨A1, A2, linear.1⟩, ⟨mixGroup G n1 n2 κ pp A1 A2, linear.2⟩) := rfl

/-- Encryption computes the group masks and the group-only signal sent to Π
[Wee20, §3.1, p. 6]. -/
def encCore (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (pk : MPK G ℓ n1 n2 κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order) (ω : EncDraw G κ pp) : CT G n1 n2 κ pp :=
  let y1 := groupVecMul ω.1 pk.A1 * pp.group.expVec pp.generator z1
  let y2 := groupVecMul ω.2.1 pk.A2 * pp.group.expVec pp.generator z2
  ⟨y1, y2, Linear.encCore G ℓ (piDim n1 n2) κ pp pk.linear x
    (signalGroup G n1 n2 κ pp ω.1 z2 y1 ω.2.1) ω.2.2⟩

/-- Encryption uses only the two public group masks, known scalars and Π's group input. -/
theorem encCore_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (pk : MPK G ℓ n1 n2 κ pp)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order) (ω : EncDraw G κ pp) :
    encCore G ℓ n1 n2 κ pp pk x z1 z2 ω =
      let y1 := groupVecMul ω.1 pk.A1 * pp.group.expVec pp.generator z1
      let y2 := groupVecMul ω.2.1 pk.A2 * pp.group.expVec pp.generator z2
      ⟨y1, y2, Linear.encCore G ℓ (piDim n1 n2) κ pp pk.linear x
        (signalGroup G n1 n2 κ pp ω.1 z2 y1 ω.2.1) ω.2.2⟩ := rfl

/-- Key generation forwards its function and fixed group matrix to Π
[Wee20, §3.1, p. 6; §4, p. 8]. -/
def keyCore (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ) (pp : PublicParams G κ)
    (msk : MSK G ℓ n1 n2 κ pp) (f : Fn κ pp.orderParam)
    (ω : Linear.KeyDraw G PG κ pp f) : Key G n1 n2 PG κ pp f :=
  ⟨msk.matrix, Linear.keyCore G PG (piDim n1 n2) κ pp msk.linear f msk.matrix ω⟩

/-- The key stores its public matrix metadata and Π's function key. -/
theorem keyCore_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (msk : MSK G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) (ω : Linear.KeyDraw G PG κ pp f) :
    keyCore G n1 n2 PG κ pp msk f ω =
      ⟨msk.matrix, Linear.keyCore G PG (piDim n1 n2) κ pp msk.linear f msk.matrix ω⟩ := rfl

/-- Scalar quadratic evaluation uses the existing private tensor and the supplied raw
partial-garbling function evaluation [Wee20, §3, p. 6]. -/
def value (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order) : ZMod pp.group.order :=
  dotProduct (privateTensor (p := pp.orderParam) z1 z2) (PG.eval κ pp.orderParam f x)

/-- The allowed scalar is exactly the tensor/function-vector dot product. -/
theorem value_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order) :
    value G n1 n2 PG κ pp f x z1 z2 =
      dotProduct (privateTensor (p := pp.orderParam) z1 z2) (PG.eval κ pp.orderParam f x) := rfl

/-- Decryption pairs the two outer masks, weights by the function value, and divides by
Π's decryption [Wee20, §3.1, p. 6, Dec and (5)]. -/
def dec (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (sk : Key G n1 n2 PG κ pp f) (ct : CT G n1 n2 κ pp) : pp.group.GT :=
  groupDot (fun i => pp.group.pairTensor ct.y1 ct.y2 (finProdFinEquiv.symm i))
      (PG.eval κ pp.orderParam f x) *
    (Linear.dec G PG (piDim n1 n2) κ pp f sk.matrix x sk.linear ct.linear)⁻¹

/-- Decryption is the weighted tensor pairing divided by the linear decryption. -/
theorem dec_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (sk : Key G n1 n2 PG κ pp f) (ct : CT G n1 n2 κ pp) :
    dec G n1 n2 PG κ pp f x sk ct =
      groupDot (fun i => pp.group.pairTensor ct.y1 ct.y2 (finProdFinEquiv.symm i))
          (PG.eval κ pp.orderParam f x) *
        (Linear.dec G PG (piDim n1 n2) κ pp f sk.matrix x sk.linear ct.linear)⁻¹ := rfl

/-- The exact setup law samples its single product draw and applies the core. -/
noncomputable def setup (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : ProbComp (MPK G ℓ n1 n2 κ pp × MSK G ℓ n1 n2 κ pp) :=
  (setupCore G ℓ n1 n2 κ pp <$> (ProbComp.sample (SetupDraw G ℓ n1 n2 κ pp)))

/-- Setup has the displayed exact core-plus-draw law. -/
theorem setup_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    setup G ℓ n1 n2 κ pp =
      (setupCore G ℓ n1 n2 κ pp <$> (ProbComp.sample (SetupDraw G ℓ n1 n2 κ pp))) := rfl

/-- The exact encryption law samples its two masks and Π's randomness. -/
noncomputable def enc (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (pk : MPK G ℓ n1 n2 κ pp)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order) : ProbComp (CT G n1 n2 κ pp) :=
  (encCore G ℓ n1 n2 κ pp pk x z1 z2 <$> (ProbComp.sample (EncDraw G κ pp)))

/-- Encryption has the displayed exact core-plus-draw law. -/
theorem enc_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (pk : MPK G ℓ n1 n2 κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order) :
    enc G ℓ n1 n2 κ pp pk x z1 z2 =
      (encCore G ℓ n1 n2 κ pp pk x z1 z2 <$> (ProbComp.sample (EncDraw G κ pp))) := rfl

/-- The exact key law uses Π's function-dependent key draw. -/
noncomputable def keyGen (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (msk : MSK G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) : ProbComp (Key G n1 n2 PG κ pp f) :=
  (keyCore G n1 n2 PG κ pp msk f <$> (ProbComp.sample (Linear.KeyDraw G PG κ pp f)))

/-- Key generation has the displayed exact core-plus-draw law. -/
theorem keyGen_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (msk : MSK G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) :
    keyGen G n1 n2 PG κ pp msk f =
      (keyCore G n1 n2 PG κ pp msk f <$> (ProbComp.sample (Linear.KeyDraw G PG κ pp f))) := rfl

/-- The quadratic construction is an internal raw algorithm bundle
[Wee20, §3.1, p. 6]. Uniform efficiency is supplied by the outer targets. -/
structure RawAlgorithms (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) where
  /-- Honest setup core. -/
  setupCore : SetupDraw G ℓ n1 n2 κ pp → MPK G ℓ n1 n2 κ pp × MSK G ℓ n1 n2 κ pp
  /-- Honest encryption core. -/
  encCore : MPK G ℓ n1 n2 κ pp → (Fin (ℓ.eval κ) → ZMod pp.group.order) →
    (Fin (n1.eval κ) → ZMod pp.group.order) → (Fin (n2.eval κ) → ZMod pp.group.order) →
    EncDraw G κ pp → CT G n1 n2 κ pp
  /-- Honest function-key core. -/
  keyCore : MSK G ℓ n1 n2 κ pp → (f : Fn κ pp.orderParam) →
    Linear.KeyDraw G PG κ pp f → Key G n1 n2 PG κ pp f
  /-- Deterministic decryption. -/
  dec : (f : Fn κ pp.orderParam) → (Fin (ℓ.eval κ) → ZMod pp.group.order) →
    Key G n1 n2 PG κ pp f → CT G n1 n2 κ pp → pp.group.GT

/-- Assemble the explicit raw quadratic cores [Wee20, §3.1, p. 6]. -/
def scheme_raw (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) : RawAlgorithms G n1 n2 PG κ pp :=
  ⟨setupCore G ℓ n1 n2 κ pp, encCore G ℓ n1 n2 κ pp,
    keyCore G n1 n2 PG κ pp, dec G n1 n2 PG κ pp⟩

/-- The raw quadratic bundle contains exactly the four displayed cores. -/
theorem scheme_raw_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) :
    scheme_raw G n1 n2 PG κ pp =
      ⟨setupCore G ℓ n1 n2 κ pp, encCore G ℓ n1 n2 κ pp,
        keyCore G n1 n2 PG κ pp, dec G n1 n2 PG κ pp⟩ := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
