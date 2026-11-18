/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Core
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Embedding
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Encodings
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The raw public-key PHFE bundle

The raw bundle gives the generic functional-encryption interface explicit typed quadratic
cores and exact finite draw types. The private vector is duplicated, giving the quadratic
duplicated private class of GJLS21. Uniform efficiency remains an explicit later target; this module
constructs no efficient primitive, simulator, machine, or sampler.

## Main definitions

* `Wee20.wee20PHFE_raw`: the complete raw PHFE bundle over a supplied raw garbling.

## Main results

Projection readers specify every honest core and the public modulus. Correctness is in
`PHFE.Correctness`; assembly into efficient primitives is in `Targets`.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1-4.2 and Section 9.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Section 3.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity TCSlib.Cryptography.Pairing

/-- The raw public-key PHFE bundle is Wee's quadratic scheme at the duplicated private
input, with values embedded in the target group [GJLS21, Section 9; Wee20, Section 3.1].
A supplied garbling's semantic agreement with the tensor class is a separate correctness
hypothesis; no efficiency target is a hypothesis of raw correctness or security. -/
def wee20PHFE_raw (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    FEScheme.Raw (phfeClass ℓ n G.wG d) where
  G := G
  cprm := PHFE.classParam G ℓ n d
  mpkLen := PHFE.mpkLen G ℓ n
  mskLen := PHFE.mskLen G ℓ n
  skLen := PHFE.skLen G PG
  ctLen := PHFE.ctLen G n
  decOutLen := G.wT
  MPK := Quadratic.MPK G ℓ n n
  MSK := Quadratic.MSK G ℓ n n
  SK := PHFE.Key G PG
  CT := Quadratic.CT G n n
  DecOut := fun _ pp => pp.group.GT
  embed := PHFE.embedValue G ℓ n d
  embed_injective := PHFE.embedValue_injective G ℓ n d
  SetupDraw := Quadratic.SetupDraw G ℓ n n
  setupDrawFintype := fun κ pp => inferInstance
  setupDrawNonempty := fun κ pp => inferInstance
  setupCore := PHFE.setupCore G ℓ n
  EncDraw := fun κ pp _ _ _ => Quadratic.EncDraw G κ pp
  encDrawFintype := fun κ pp _ _ _ => inferInstance
  encDrawNonempty := fun κ pp _ _ _ => inferInstance
  encCore := PHFE.encCore G ℓ n d
  KeyDraw := fun κ pp _ f => Linear.KeyDraw G PG κ pp (PHFE.decodeFunction G ℓ n d κ pp f)
  keyDrawFintype := fun κ pp _ f => inferInstance
  keyDrawNonempty := fun κ pp _ f => inferInstance
  keyCore := PHFE.keyCore G PG
  dec := PHFE.dec G PG
  encMPK := PHFE.encMPK G ℓ n
  encMSK := PHFE.encMSK G ℓ n
  encSK := PHFE.encSK G PG
  encCT := PHFE.encCT G n
  encDecOut := fun _ pp => pp.group.encT
  encSetupDraw := fun _ pp => Wire.quadraticSetupDraw pp
  encEncDraw := fun _ pp _ _ _ => Wire.quadraticEncDraw pp
  encKeyDraw := fun _ pp _ _ => Wire.linearKeyDraw pp PG
  encMPK_inj := fun κ pp _ _ h => PHFE.encMPK_injective G ℓ n κ pp h
  encSK_inj := fun κ pp _ _ _ _ _ h => PHFE.encSK_injective G PG κ pp h
  encCT_inj := fun κ pp _ _ _ _ _ _ _ h => PHFE.encCT_injective G n κ pp h
  encDecOut_injective := fun _ pp => pp.group.encT_injective

/-- The raw PHFE bundle keeps the supplied group-description generator. -/
theorem wee20PHFE_raw_G (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).G = G := rfl

/-- The raw class parameter is the order read from the public group. -/
theorem wee20PHFE_raw_cprm (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d))
    (pp : PublicParams G κ) :
    (wee20PHFE_raw G ℓ n d PG).cprm κ pp = PHFE.classParam G ℓ n d κ pp := rfl

/-- Raw PHFE setup is the typed quadratic setup adapter. -/
theorem wee20PHFE_raw_setupCore (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).setupCore = PHFE.setupCore G ℓ n := rfl

/-- Raw PHFE encryption duplicates the decoded private vector in the quadratic core. -/
theorem wee20PHFE_raw_encCore (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).encCore = PHFE.encCore G ℓ n d := rfl

/-- Raw PHFE key generation retains the original function description. -/
theorem wee20PHFE_raw_keyCore (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).keyCore = PHFE.keyCore G PG := rfl

/-- Raw PHFE decryption returns the typed quadratic result. -/
theorem wee20PHFE_raw_dec (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).dec = PHFE.dec G PG := rfl

/-- The raw PHFE output embedding is precisely the published class-value embedding
at every security parameter and public parameter; no efficiency or correctness premise
is needed. This projection reader preserves the parameter-dependent value/output types. -/
theorem wee20PHFE_raw_embed (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).embed = PHFE.embedValue G ℓ n d := rfl

/-- The raw PHFE ciphertext width has exactly `6n+5` group entries. -/
theorem wee20PHFE_raw_ctLen (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).ctLen = PHFE.ctLen G n := rfl

/-- The raw PHFE mpkLen projection is its specified polynomial width. -/
theorem wee20PHFE_raw_mpkLen (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).mpkLen = PHFE.mpkLen G ℓ n := rfl

/-- The raw PHFE mskLen projection is its specified polynomial width. -/
theorem wee20PHFE_raw_mskLen (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).mskLen = PHFE.mskLen G ℓ n := rfl

/-- The raw PHFE skLen projection is its specified polynomial width. -/
theorem wee20PHFE_raw_skLen (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).skLen = PHFE.skLen G PG := rfl

/-- The raw PHFE decOutLen projection is its specified polynomial width. -/
theorem wee20PHFE_raw_decOutLen (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).decOutLen = G.wT := rfl

namespace PHFE

/-- Transport the raw bundle's public parameters to its underlying group generator.
This explicit codec prevents consumers from unfolding the raw bundle. -/
def publicParamsEquiv (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ) :
    PublicParams (wee20PHFE_raw G ℓ n d PG).G κ ≃ PublicParams G κ := Equiv.refl _

/-- The public-parameter codec is internally the identity equivalence. -/
theorem publicParamsEquiv_eq (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ) :
    publicParamsEquiv G ℓ n d PG κ = Equiv.refl (PublicParams G κ) := rfl

/-- Transport the raw bundle's MPK values through its public-parameter codec. -/
def mpkEquiv (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    (wee20PHFE_raw G ℓ n d PG).MPK κ pp ≃
      Quadratic.MPK G ℓ n n κ (publicParamsEquiv G ℓ n d PG κ pp) := Equiv.refl _

/-- The data codec is internally the identity equivalence. -/
theorem mpkEquiv_eq (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    mpkEquiv G ℓ n d PG κ pp = Equiv.refl (Quadratic.MPK G ℓ n n κ (publicParamsEquiv G ℓ n d PG κ
      pp)) := rfl

/-- Transport the raw bundle's SK values through its public-parameter codec. -/
def keyEquiv (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    (wee20PHFE_raw G ℓ n d PG).SK κ pp ≃
      Key G PG κ (publicParamsEquiv G ℓ n d PG κ pp) := Equiv.refl _

/-- The data codec is internally the identity equivalence. -/
theorem keyEquiv_eq (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    keyEquiv G ℓ n d PG κ pp = Equiv.refl (Key G PG κ (publicParamsEquiv G ℓ n d PG κ pp)) := rfl

/-- Transport the raw bundle's CT values through its public-parameter codec. -/
def ctEquiv (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    (wee20PHFE_raw G ℓ n d PG).CT κ pp ≃
      Quadratic.CT G n n κ (publicParamsEquiv G ℓ n d PG κ pp) := Equiv.refl _

/-- The data codec is internally the identity equivalence. -/
theorem ctEquiv_eq (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    ctEquiv G ℓ n d PG κ pp = Equiv.refl (Quadratic.CT G n n κ (publicParamsEquiv G ℓ n d PG κ pp))
      := rfl

/-- Transport a raw class value to its scalar at the drawn public modulus. -/
def scalarValueEquiv (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    (phfeClass ℓ n G.wG d).Out κ ((wee20PHFE_raw G ℓ n d PG).cprm κ pp) ≃
      ZMod (publicParamsEquiv G ℓ n d PG κ pp).group.order :=
  valueEquiv G ℓ n d κ (publicParamsEquiv G ℓ n d PG κ pp)

/-- The scalar-value codec is the published class codec at the public modulus. -/
theorem scalarValueEquiv_eq (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ) :
    scalarValueEquiv G ℓ n d PG κ pp =
      valueEquiv G ℓ n d κ (publicParamsEquiv G ℓ n d PG κ pp) := rfl

end PHFE

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
