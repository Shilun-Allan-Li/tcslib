/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite fixed-prime advice for quadratic security reductions

## Main definitions

* `Wee20.Quadratic.MaskAdvice`, `maskAdviceDraw`: scalar outer tape and public-order cast.
* `Wee20.Quadratic.Advice`, `adviceDraw`: full outer and linear advice.
* `Wee20.Quadratic.maskAdviceEnc`, `adviceEnc`, `adviceLen`: canonical words and bounds.

## Main results

Nonempty/finite statements and equation readers expose the advice. Length and injectivity
proof obligations are stated in `Theorems`; no scalar or realisation codec is duplicated.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3.3, pp. 7–8, Games 0–4.
  The finite tape is explicit fixed-advice bookkeeping for its reductions.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- Outer reduction advice is a scalar tape over the fixed order schedule. -/
abbrev MaskAdvice (n1 n2 : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) :=
  Fin ((maskCount n1 n2).eval κ) → ZMod (p κ)

/-- Outer advice has its displayed fixed-prime function type. -/
theorem maskAdvice_eq (n1 n2 : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) :
    MaskAdvice n1 n2 p κ = (Fin ((maskCount n1 n2).eval κ) → ZMod (p κ)) := rfl

/-- The zero vector inhabits every outer advice type. -/
theorem maskAdvice_nonempty (n1 n2 : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) :
    Nonempty (MaskAdvice n1 n2 p κ) := ⟨0⟩

/-- Outer advice is finite under the shared fixed-order hypothesis. -/
theorem maskAdvice_finite (G : BilinearGen) (n1 n2 : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) : Finite (MaskAdvice n1 n2 p κ) :=
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  inferInstance

/-- Transport known outer advice to the actual public group order using the shared
Mathlib ring equivalence; this never extracts a scalar from a group element. -/
def maskAdviceDraw (G : BilinearGen) (n1 n2 : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (pp : PublicParams G κ)
    (ω : MaskAdvice n1 n2 p κ) : MaskDraw G n1 n2 κ pp :=
  fun i => ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm (ω i)

/-- The outer advice cast is coordinatewise ringEquivCongr. -/
theorem maskAdviceDraw_eq (G : BilinearGen) (n1 n2 : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (pp : PublicParams G κ)
    (ω : MaskAdvice n1 n2 p κ) : maskAdviceDraw G n1 n2 p hp κ pp ω =
      fun i => ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm (ω i) := rfl

/-- Full outer reduction advice retains the independent linear tape as well. -/
abbrev Advice {ℓ : PolyExpr} (n1 n2 q : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ) (κ : ℕ) :=
  MaskAdvice n1 n2 p κ × Linear.Advice PG (piDim n1 n2) q p κ

/-- Full advice is the displayed pair of scalar tapes. -/
theorem advice_eq {ℓ : PolyExpr} (n1 n2 q : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ) (κ : ℕ) :
    Advice n1 n2 q PG p κ = (MaskAdvice n1 n2 p κ × Linear.Advice PG (piDim n1 n2) q p κ) :=
  rfl

/-- The pair of zero tapes inhabits full advice. -/
theorem advice_nonempty {ℓ : PolyExpr} (n1 n2 q : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ) (κ : ℕ) :
    Nonempty (Advice n1 n2 q PG p κ) := ⟨(0, 0)⟩

/-- Full advice is finite without an extra positivity restriction. -/
theorem advice_finite (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) : Finite (Advice n1 n2 q PG p κ) :=
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  inferInstance

/-- Cast both known scalar tapes through the shared public-order equality. -/
def adviceDraw (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (pp : PublicParams G κ)
    (ω : Advice n1 n2 q PG p κ) : SecurityDraw G n1 n2 q PG κ pp :=
  (maskAdviceDraw G n1 n2 p hp κ pp ω.1,
    Linear.adviceDraw G PG (piDim n1 n2) q p hp κ pp ω.2)

/-- The full advice cast is the pair of its published component casts. -/
theorem adviceDraw_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (pp : PublicParams G κ)
    (ω : Advice n1 n2 q PG p κ) : adviceDraw G n1 n2 q PG p hp κ pp ω =
      (maskAdviceDraw G n1 n2 p hp κ pp ω.1,
        Linear.adviceDraw G PG (piDim n1 n2) q p hp κ pp ω.2) := rfl

/-- Public metadata encodes unary κ and both separate dimension numbers. -/
def maskAdviceMeta (n1 n2 : PolyExpr) (κ : ℕ) : List Bool :=
  let num := fun n => Candidates.natToList (Nat.size n) n
  pairEncode (List.replicate κ true) (pairEncode (num (n1.eval κ)) (num (n2.eval κ)))

/-- Metadata is the displayed unary/binary header. -/
theorem maskAdviceMeta_eq (n1 n2 : PolyExpr) (κ : ℕ) : maskAdviceMeta n1 n2 κ =
    let num := fun n => Candidates.natToList (Nat.size n) n
    pairEncode (List.replicate κ true) (pairEncode (num (n1.eval κ)) (num (n2.eval κ))) := rfl

/-- Encode known outer advice using the existing modular-vector encoder. -/
def maskAdviceEnc (G : BilinearGen) (n1 n2 : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : MaskAdvice n1 n2 p κ) : List Bool :=
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  pairEncode (maskAdviceMeta n1 n2 κ) (Encoding.Modular.encodeVector (G.wG.eval κ) ω)

/-- Outer advice encoding exposes its header and modular vector. -/
theorem maskAdviceEnc_eq (G : BilinearGen) (n1 n2 : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : MaskAdvice n1 n2 p κ) :
    maskAdviceEnc G n1 n2 p hp κ ω =
      letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
      pairEncode (maskAdviceMeta n1 n2 κ) (Encoding.Modular.encodeVector (G.wG.eval κ) ω) := rfl

/-- A polynomial bounds both the explicit dimension header and scalar mask word. -/
def maskAdviceLen (G : BilinearGen) (n1 n2 : PolyExpr) : PolyExpr :=
  ((((PolyExpr.const 4).mul PolyExpr.var).add ((PolyExpr.const 4).mul n1)).add
    (((PolyExpr.const 2).mul n2).add (PolyExpr.const 20))).add ((maskCount n1 n2).mul G.wG)

/-- The mask word bound is its displayed polynomial. -/
theorem maskAdviceLen_eq (G : BilinearGen) (n1 n2 : PolyExpr) : maskAdviceLen G n1 n2 =
    ((((PolyExpr.const 4).mul PolyExpr.var).add ((PolyExpr.const 4).mul n1)).add
      (((PolyExpr.const 2).mul n2).add (PolyExpr.const 20))).add ((maskCount n1 n2).mul G.wG) := rfl

/-- The full advice word pairs the existing outer and linear scalar encodings. -/
def adviceEnc (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : Advice n1 n2 q PG p κ) : List Bool :=
  pairEncode (maskAdviceEnc G n1 n2 p hp κ ω.1)
    (Linear.adviceEnc G PG (piDim n1 n2) q p hp κ ω.2)

/-- The full word is the displayed pair of component encodings. -/
theorem adviceEnc_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : Advice n1 n2 q PG p κ) :
    adviceEnc G n1 n2 q PG p hp κ ω = pairEncode (maskAdviceEnc G n1 n2 p hp κ ω.1)
      (Linear.adviceEnc G PG (piDim n1 n2) q p hp κ ω.2) := rfl

/-- The pair-length reader gives the full advice polynomial. -/
def adviceLen (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) : PolyExpr :=
  (((PolyExpr.const 2).mul (maskAdviceLen G n1 n2)).add (PolyExpr.const 2)).add
    (Linear.adviceLen G PG (piDim n1 n2) q)

/-- The full advice bound is twice the left bound plus two plus the right bound. -/
theorem adviceLen_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) :
    adviceLen G n1 n2 q PG =
      (((PolyExpr.const 2).mul (maskAdviceLen G n1 n2)).add (PolyExpr.const 2)).add
        (Linear.adviceLen G PG (piDim n1 n2) q) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
