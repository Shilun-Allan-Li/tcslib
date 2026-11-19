/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The raw committed PHFE simulator

The same stateful semi-adaptive simulator consumes the committed public input and the
indexed function/value pairs. This raw conversion constructs no sampler. Its efficient
interface has its own three explicit fields in the concrete simulator targets.

## Main definitions

* `Wee20.wee20Sim_raw`: the committed raw simulator obtained by the generic conversion.

## Main results

The conversion reader identifies the complete raw simulator without foreign unfolding.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.3 and Remark 4.6.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 2.2 and 3.2.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity TCSlib.Cryptography.Pairing

/-- The committed raw simulator runs the same stateful algorithms as the semi-adaptive
one, with the allowed information projected from the commitment
[GJLS21, Definition 4.3; Wee20, Section 2.2]. -/
noncomputable def wee20Sim_raw (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    FEScheme.Raw.Simulator.Raw (wee20PHFE_raw G ℓ n d PG) :=
  (wee20SASim_raw G ℓ n d PG).toSim

/-- The committed raw simulator is precisely the generic raw conversion. -/
theorem wee20Sim_raw_eq (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    wee20Sim_raw G ℓ n d PG = (wee20SASim_raw G ℓ n d PG).toSim := rfl

/-- The complete encoded simulator state has one uniform polynomial length bound.

**Proof sketch.** Choose its existing fixed width and use List.length_ofFn. -/
theorem wee20Sim_raw_state_bounded (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    ∃ b : PolyExpr, ∀ κ (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ)
      (st : (wee20Sim_raw G ℓ n d PG).St κ pp),
      (List.ofFn ((wee20Sim_raw G ℓ n d PG).encSt κ pp st)).length ≤ b.eval κ :=
  ⟨(wee20Sim_raw G ℓ n d PG).stLen, fun _ _ _ => le_of_eq List.length_ofFn⟩

/-- Every allowed scalar value has a uniform polynomial encoding-length bound.

**Proof sketch.** Reuse the scheme's value-word bound with the same public parameters. -/
theorem wee20Sim_raw_value_bounded (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    ∃ b : PolyExpr, ∀ κ (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ)
      (v : (phfeClass ℓ n G.wG d).Out κ ((wee20PHFE_raw G ℓ n d PG).cprm κ pp)),
      ((phfeClass ℓ n G.wG d).encValue κ
        ((wee20PHFE_raw G ℓ n d PG).cprm κ pp) v).length ≤ b.eval κ :=
  wee20PHFE_raw_value_bounded G ℓ n d PG

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
