/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The raw semi-adaptive PHFE simulator

The simulator samples the quadratic setup and retains its scalar masks. Ciphertext
simulation receives only the public input. Each key receives its original function word
and the allowed class value, which the public value codec turns into a scalar. Only the
known scalar is exponentiated to supply the source-group leakage expected by the inner
simulator. No exponent is recovered from a group element.

## Main definitions

* `Wee20.wee20SASim_raw`: the concrete raw semi-adaptive simulator.

## Main results

The core equation readers expose the exact stateful setup, encryption and key simulation.
Uniform efficiency for this raw bundle and its committed conversion is stated in Targets.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 2.2 and 3.2.
* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Theorem 9.2 proof, Hybrid 1, printed p. 61.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity Turing TCSlib.Cryptography.Pairing

/-- The raw semi-adaptive PHFE simulator is the stateful quadratic simulator with explicit
wire adapters [Wee20, Section 3.2]. Allowed values are scalar class values, following
[GJLS21, Theorem 9.2 proof, Hybrid 1], rather than literal target-group encodings. -/
noncomputable def wee20SASim_raw (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    FEScheme.Raw.SASimulator.Raw (wee20PHFE_raw G ℓ n d PG) where
  St := fun κ pp =>
    Quadratic.SimState G ℓ n n κ (PHFE.publicParamsEquiv G ℓ n d PG κ pp)
  stLen := PHFE.simStLen G ℓ n
  encSt := fun κ pp =>
    PHFE.encSimState G ℓ n κ (PHFE.publicParamsEquiv G ℓ n d PG κ pp)
  encSt_injective := fun κ pp =>
    PHFE.encSimState_injective G ℓ n κ (PHFE.publicParamsEquiv G ℓ n d PG κ pp)
  SetupDraw := fun κ pp =>
    Quadratic.SimSetupDraw G ℓ n n κ (PHFE.publicParamsEquiv G ℓ n d PG κ pp)
  setupFinite := fun κ pp => inferInstance
  setupNonempty := fun κ pp => inferInstance
  setupCore := fun κ pp ω =>
    let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
    let k := Quadratic.simSetupCore G ℓ n n κ pp' ω
    ((PHFE.mpkEquiv G ℓ n d PG κ pp).symm k.1, k.2)
  EncDraw := fun κ pp _ _ =>
    Quadratic.SimEncDraw G n n κ (PHFE.publicParamsEquiv G ℓ n d PG κ pp)
  encFinite := fun κ pp _ _ => inferInstance
  encNonempty := fun κ pp _ _ => inferInstance
  encCore := fun κ pp st x ω =>
    let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
    let c := Quadratic.simEncCore G ℓ n n κ pp' st (PHFE.decodePublic G ℓ n d κ pp' x) ω
    ((PHFE.ctEquiv G ℓ n d PG κ pp).symm c.1, c.2)
  KeyDraw := fun κ pp _ _ f _ =>
    let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
    Linear.SimKeyDraw G PG κ pp' (PHFE.decodeFunction G ℓ n d κ pp' f)
  keyFinite := fun κ pp _ _ f _ => inferInstance
  keyNonempty := fun κ pp _ _ f _ => inferInstance
  keyCore := fun κ pp st x f mu ω =>
    let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
    let scalar := PHFE.scalarValueEquiv G ℓ n d PG κ pp mu
    let sk := Quadratic.simKeyCore G n n PG κ pp' st (PHFE.decodeFunction G ℓ n d κ pp' f)
      (PHFE.decodePublic G ℓ n d κ pp' x) (pp'.generator ^ scalar.val) ω
    ((PHFE.keyEquiv G ℓ n d PG κ pp).symm ⟨f, sk⟩, st)
  encSetupDraw := fun _ pp =>
    Wire.quadraticSimSetupDraw (PHFE.publicParamsEquiv G ℓ n d PG _ pp)
  encEncDraw := fun _ pp _ _ ω =>
    let pp' := PHFE.publicParamsEquiv G ℓ n d PG _ pp
    [Wire.scalarVector pp' ω.1, Wire.scalarVector pp' ω.2].foldr pairEncode []
  encKeyDraw := fun _ pp _ _ _ _ =>
    Wire.linearSimKeyDraw (PHFE.publicParamsEquiv G ℓ n d PG _ pp) PG

/-- The raw simulator state has the complete concrete polynomial encoding width. -/
theorem wee20SASim_raw_stLen (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20SASim_raw G ℓ n d PG).stLen = PHFE.simStLen G ℓ n := rfl

/-- The raw simulator uses the fixed-width codec for its complete quadratic state. -/
theorem wee20SASim_raw_encSt (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ)
    (st : (wee20SASim_raw G ℓ n d PG).St κ pp) :
    (wee20SASim_raw G ℓ n d PG).encSt κ pp st =
      PHFE.encSimState G ℓ n κ (PHFE.publicParamsEquiv G ℓ n d PG κ pp) st := rfl

/-- Raw simulated setup runs the quadratic simulator and packages its public key. -/
theorem wee20SASim_raw_setupCore (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ)
    (ω : (wee20SASim_raw G ℓ n d PG).SetupDraw κ pp) :
    (wee20SASim_raw G ℓ n d PG).setupCore κ pp ω =
      let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
      let k := Quadratic.simSetupCore G ℓ n n κ pp' ω
      ((PHFE.mpkEquiv G ℓ n d PG κ pp).symm k.1, k.2) := rfl

/-- Raw simulated encryption uses only the decoded public input and fresh scalar masks. -/
theorem wee20SASim_raw_encCore (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ)
    (st : (wee20SASim_raw G ℓ n d PG).St κ pp)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool)
    (ω : (wee20SASim_raw G ℓ n d PG).EncDraw κ pp st x) :
    (wee20SASim_raw G ℓ n d PG).encCore κ pp st x ω =
      let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
      let c := Quadratic.simEncCore G ℓ n n κ pp' st (PHFE.decodePublic G ℓ n d κ pp' x) ω
      ((PHFE.ctEquiv G ℓ n d PG κ pp).symm c.1, c.2) := rfl

/-- Raw simulated keys exponentiate the supplied scalar value and retain the state. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem wee20SASim_raw_keyCore (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ)
    (st : (wee20SASim_raw G ℓ n d PG).St κ pp)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool)
    (f : Fin ((phfeClass ℓ n G.wG d).fnLen.eval κ) → Bool)
    (mu : (phfeClass ℓ n G.wG d).Out κ ((wee20PHFE_raw G ℓ n d PG).cprm κ pp))
    (ω : (wee20SASim_raw G ℓ n d PG).KeyDraw κ pp st x f mu) :
    (wee20SASim_raw G ℓ n d PG).keyCore κ pp st x f mu ω =
      let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
      let scalar := PHFE.scalarValueEquiv G ℓ n d PG κ pp mu
      let sk := Quadratic.simKeyCore G n n PG κ pp' st
        (PHFE.decodeFunction G ℓ n d κ pp' f) (PHFE.decodePublic G ℓ n d κ pp' x)
        (pp'.generator ^ scalar.val) ω
      ((PHFE.keyEquiv G ℓ n d PG κ pp).symm ⟨f, sk⟩, st) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
