/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PHFE class adapter

The private input is used in both slots of Wee's quadratic scheme. The public input and
function descriptions are decoded modulo the order read from public parameters. Explicit
parameter and value codecs transport arbitrary class parameters and values to their residue
  interpretation;
foreign class bundles need not be unfolded by a consumer.

## Main definitions

* `Wee20.PHFE.TensorFn`: coefficient tensors for the quadratic output vector.
* `Wee20.PHFE.classParam`, `embedValue`: the drawn modulus and target-group embedding.
* `Wee20.PHFE.decodePublic`, `decodePrivate`, `decodeFunction`: the three input adapters.
* `Wee20.PHFE.Key`: an original function word together with its typed quadratic key.
* `Wee20.PHFE.PGSound`: semantic agreement of a supplied garbling with tensor evaluation.

## Main results

Embedding faithfulness is proved in `PHFE.Embedding`; the adapters have width and equation
readers.
* Width and equation readers expose the adapters without foreign unfolding.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1-4.3 and Section 9.
* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, Lemma 2 and Appendix A.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 3.1-3.2.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE

open Complexity Turing TCSlib.Cryptography.Pairing

/-- The PHFE function family is a polynomial vector with one output per private pair
[GJLS21, Section 9; Wee20, Section 3.1]. -/
abbrev TensorFn (ℓ n : PolyExpr) (d κ : ℕ) (p : ℕ+) : Type :=
  PolyTensor p (ℓ.eval κ) (n.eval κ * n.eval κ) d

/-- The tensor family has the displayed output and monomial coordinates. -/
theorem tensorFn_eq (ℓ n : PolyExpr) (d κ : ℕ) (p : ℕ+) :
    TensorFn ℓ n d κ p = PolyTensor p (ℓ.eval κ) (n.eval κ * n.eval κ) d := rfl

/-- A supplied raw garbling computes the intended coefficient tensor evaluation.
This is semantic agreement with the chosen function class, rather than an efficiency
hypothesis [AGW20, Lemma 2, applied to the polynomial vector of GJLS21, Section 9]. -/
def PGSound {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) : Prop :=
  ∀ κ p f x, PG.eval κ p f x = polyTensorEval f x

/-- Semantic agreement is pointwise equality with the polynomial-vector evaluation. -/
theorem pgSound_iff {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) :
    PGSound PG ↔ ∀ κ p f x, PG.eval κ p f x = polyTensorEval f x := Iff.rfl

/-- The class parameter is the public group's order, packaged by the published class codec.
No external prime schedule is evaluated by an honest algorithm [GJLS21, Definition 4.1]. -/
def classParam (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) (pp : PublicParams G κ) :
    (phfeClass ℓ n G.wG d).Prm κ :=
  (phfeClassParamEquiv ℓ n G.wG d κ).symm pp.orderParam

/-- The parameter adapter packages precisely the modulus read from public parameters. -/
theorem classParam_eq (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) : classParam G ℓ n d κ pp =
      (phfeClassParamEquiv ℓ n G.wG d κ).symm pp.orderParam := rfl

/-- Read a class value at the packaged public modulus as a scalar. This typed codec
exposes the parameter transport without requiring consumers to unfold classParam. -/
def valueEquiv (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) (pp : PublicParams G κ) :
    (phfeClass ℓ n G.wG d).Out κ (classParam G ℓ n d κ pp) ≃ ZMod pp.group.order :=
  phfeClassValueEquiv ℓ n G.wG d κ pp.orderParam

/-- The public-value codec is the class codec at the drawn positive modulus. -/
theorem valueEquiv_eq (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) : valueEquiv G ℓ n d κ pp =
      phfeClassValueEquiv ℓ n G.wG d κ pp.orderParam := rfl

/-- Packaging a supplied scalar and reading it back preserves it. -/
theorem valueEquiv_apply_symm (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) (a : ZMod pp.group.order) :
    valueEquiv G ℓ n d κ pp ((valueEquiv G ℓ n d κ pp).symm a) = a :=
  (valueEquiv G ℓ n d κ pp).apply_symm_apply a

/-- Embed the allowed scalar value in the target group at the public generator
[GJLS21, Definition 4.2 and Section 9]. -/
def embedValue (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) (pp : PublicParams G κ)
    (v : (phfeClass ℓ n G.wG d).Out κ (classParam G ℓ n d κ pp)) : pp.group.GT :=
  pp.group.pair pp.generator pp.generator ^
    (valueEquiv G ℓ n d κ pp v).val

/-- The embedding exponent is the scalar supplied by the published value codec. -/
theorem embedValue_eq (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ)
    (v : (phfeClass ℓ n G.wG d).Out κ (classParam G ℓ n d κ pp)) :
    embedValue G ℓ n d κ pp v = pp.group.pair pp.generator pp.generator ^
      (valueEquiv G ℓ n d κ pp v).val := rfl

/-- The public word contains exactly ℓ residues at the source-group width. -/
theorem publicWidth (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) :
    (phfeClass ℓ n G.wG d).pubLen.eval κ = ℓ.eval κ * G.wG.eval κ :=
  congrArg (fun a : PolyExpr => a.eval κ) (phfeClass_pubLen ℓ n G.wG d)

/-- The private word contains exactly n residues at the source-group width. -/
theorem privateWidth (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) :
    (phfeClass ℓ n G.wG d).privLen.eval κ = n.eval κ * G.wG.eval κ :=
  congrArg (fun a : PolyExpr => a.eval κ) (phfeClass_privLen ℓ n G.wG d)

/-- The function word contains all padded tensor coefficients at the public width. -/
theorem functionWidth (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) :
    (phfeClass ℓ n G.wG d).fnLen.eval κ =
      n.eval κ * n.eval κ * (ℓ.eval κ + 1) ^ d * G.wG.eval κ :=
  (congrArg (fun a : PolyExpr => a.eval κ) (phfeClass_fnLen ℓ n G.wG d)).trans
    (tensorFnLen_eval ℓ (n.mul n) G.wG d κ)

/-- Decode the public input modulo the drawn order, using its published wire-width reader. -/
def decodePublic (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) (pp : PublicParams G κ)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool) :
    Fin (ℓ.eval κ) → ZMod pp.group.order :=
  decodeResidues pp.orderParam (ℓ.eval κ) (G.wG.eval κ)
    (x ∘ (finCongr (publicWidth G ℓ n d κ)).symm)

/-- Public decoding transports the fixed-width word and uses total modular decoding. -/
theorem decodePublic_eq (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool) :
    decodePublic G ℓ n d κ pp x = decodeResidues pp.orderParam (ℓ.eval κ) (G.wG.eval κ)
      (x ∘ (finCongr (publicWidth G ℓ n d κ)).symm) := rfl

/-- Decode the private input once; both quadratic slots receive this same vector. -/
def decodePrivate (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) (pp : PublicParams G κ)
    (y : Fin ((phfeClass ℓ n G.wG d).privLen.eval κ) → Bool) :
    Fin (n.eval κ) → ZMod pp.group.order :=
  decodeResidues pp.orderParam (n.eval κ) (G.wG.eval κ)
    (y ∘ (finCongr (privateWidth G ℓ n d κ)).symm)

/-- Private decoding transports the fixed-width word and uses total modular decoding. -/
theorem decodePrivate_eq (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) (y : Fin ((phfeClass ℓ n G.wG d).privLen.eval κ) → Bool) :
    decodePrivate G ℓ n d κ pp y = decodeResidues pp.orderParam (n.eval κ) (G.wG.eval κ)
      (y ∘ (finCongr (privateWidth G ℓ n d κ)).symm) := rfl

/-- Decode the function word as its ordered coefficient tensor modulo the drawn order. -/
def decodeFunction (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) (pp : PublicParams G κ)
    (f : Fin ((phfeClass ℓ n G.wG d).fnLen.eval κ) → Bool) : TensorFn ℓ n d κ pp.orderParam :=
  decodeTensor pp.orderParam (ℓ.eval κ) (n.eval κ * n.eval κ) d (G.wG.eval κ)
    (f ∘ (finCongr (functionWidth G ℓ n d κ)).symm)

/-- Function decoding transports the word and reads its canonical tensor coordinates. -/
theorem decodeFunction_eq (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) (f : Fin ((phfeClass ℓ n G.wG d).fnLen.eval κ) → Bool) :
    decodeFunction G ℓ n d κ pp f =
      decodeTensor pp.orderParam (ℓ.eval κ) (n.eval κ * n.eval κ) d (G.wG.eval κ)
        (f ∘ (finCongr (functionWidth G ℓ n d κ)).symm) := rfl

/-- A PHFE key retains its original function word and the corresponding typed quadratic key.
Keeping the word makes its fixed-width representation injective even when distinct words
decode to the same residue tensor [GJLS21, Definition 4.1]. -/
structure Key (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d))
    (κ : ℕ) (pp : PublicParams G κ) where
  /-- The original wire function description. -/
  function : Fin ((phfeClass ℓ n G.wG d).fnLen.eval κ) → Bool
  /-- The quadratic key for its decoded coefficient tensor. -/
  quadratic : Quadratic.Key G n n PG κ pp (decodeFunction G ℓ n d κ pp function)

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
