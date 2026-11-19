/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.CommittedSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficiency targets for both concrete PHFE simulators

The six sampler obligations cover both simulator interfaces, with the exact state, permitted
information, draws, encodings and deterministic cores of the corresponding raw bundles.
Four additional encoding-length bounds have concrete uniform polynomial witnesses.

## Main definitions

* `SimTargets`: three sampler targets and two encoded-length bounds for each simulator.

## Main results

* `simTargets_iff`: the exact ten-field conjunction reader.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1, 4.3 and 4.6.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Sections 2.2 and 3.

-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity Turing TCSlib.Cryptography.Pairing
open TCSlib.Cryptography.CoinSampling

section

variable (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)

local notation "S" => wee20PHFE_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)

local notation "Sim" => wee20Sim_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)
local notation "SASim" => wee20SASim_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)

/-- Both concrete stateful simulators carry their own three shared sampler obligations
[GJLS21, Definition 4.3; Wee20, Section 2.2].
Sampler-efficiency part: Phase B obligation; not proved in this development.
The four encoded-length bounds have concrete witnesses.

The committed targets include the full allowed information and its ordered index. They
are stated separately: no input-preprocessing or product-sampler closure is assumed. -/
structure SimTargets : Prop where
  /-- The concrete committed simulator's setup draw and core satisfy the shared contract. -/
  sim_setup_eff : SamplesEfficiently
    (fun κ (pp : PublicParams (S).G κ) =>
      NUPPT.advInput κ pp.encode) (Sim).encSetupDraw
    (fun κ pp (o : (S).MPK κ pp × (Sim).St κ pp) =>
      pairEncode (List.ofFn ((S).encMPK κ pp o.1))
        (List.ofFn ((Sim).encSt κ pp o.2))) (Sim).setupCore
  /-- The concrete committed simulator's enc draw and core satisfy the shared contract. -/
  sim_enc_eff : SamplesEfficiently (fun κ π => NUPPT.advInput κ ((Sim).encInputWord κ π))
    (fun κ π => (Sim).encEncDraw κ π.pp π.state π.omega)
    (fun κ π (o : (S).CT κ π.pp × (Sim).St κ π.pp) =>
      pairEncode (List.ofFn ((S).encCT κ π.pp o.1)) (List.ofFn ((Sim).encSt κ π.pp o.2)))
    (fun κ π => (Sim).encCore κ π.pp π.state π.omega)
  /-- The concrete committed simulator's key draw and core satisfy the shared contract. -/
  sim_key_eff : SamplesEfficiently (fun κ π => NUPPT.advInput κ ((Sim).keyInputWord κ π))
    (fun κ π => (Sim).encKeyDraw κ π.pp π.state π.omega π.index)
    (fun κ π (o : (S).SK κ π.pp × (Sim).St κ π.pp) =>
      pairEncode (List.ofFn ((S).encSK κ π.pp o.1)) (List.ofFn ((Sim).encSt κ π.pp o.2)))
    (fun κ π => (Sim).keyCore κ π.pp π.state π.omega π.index)
  /-- The concrete semi-adaptive simulator's setup draw and core satisfy the shared contract. -/
  sa_setup_eff : SamplesEfficiently
    (fun κ (pp : PublicParams (S).G κ) =>
      NUPPT.advInput κ pp.encode) (SASim).encSetupDraw
    (fun κ pp (o : (S).MPK κ pp × (SASim).St κ pp) =>
      pairEncode (List.ofFn ((S).encMPK κ pp o.1))
        (List.ofFn ((SASim).encSt κ pp o.2))) (SASim).setupCore
  /-- The concrete semi-adaptive simulator's enc draw and core satisfy the shared contract. -/
  sa_enc_eff : SamplesEfficiently (fun κ π => NUPPT.advInput κ ((SASim).encInputWord κ π))
    (fun κ π => (SASim).encEncDraw κ π.pp π.state π.publicInput)
    (fun κ π (o : (S).CT κ π.pp × (SASim).St κ π.pp) =>
      pairEncode (List.ofFn ((S).encCT κ π.pp o.1)) (List.ofFn ((SASim).encSt κ π.pp o.2)))
    (fun κ π => (SASim).encCore κ π.pp π.state π.publicInput)
  /-- The concrete semi-adaptive simulator's key draw and core satisfy the shared contract. -/
  sa_key_eff : SamplesEfficiently (fun κ π => NUPPT.advInput κ ((SASim).keyInputWord κ π))
    (fun κ π => (SASim).encKeyDraw κ π.pp π.state π.publicInput π.function π.value)
    (fun κ π (o : (S).SK κ π.pp × (SASim).St κ π.pp) =>
      pairEncode (List.ofFn ((S).encSK κ π.pp o.1)) (List.ofFn ((SASim).encSt κ π.pp o.2)))
    (fun κ π => (SASim).keyCore κ π.pp π.state π.publicInput π.function π.value)

  /-- One polynomial bounds all committed-simulator private-state words. -/
  sim_state_bounded : ∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ) (st : (Sim).St κ pp),
    (List.ofFn ((Sim).encSt κ pp st)).length ≤ b.eval κ
  /-- One polynomial bounds every class-value word for committed simulation. -/
  sim_value_bounded : ∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ)
    (v : (phfeClass ℓ n G.wG d).Out κ ((S).cprm κ pp)),
    ((phfeClass ℓ n G.wG d).encValue κ ((S).cprm κ pp) v).length ≤ b.eval κ
  /-- One polynomial bounds all semi-adaptive-simulator private-state words. -/
  sa_state_bounded : ∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ) (st : (SASim).St κ pp),
    (List.ofFn ((SASim).encSt κ pp st)).length ≤ b.eval κ
  /-- One polynomial bounds every class-value word for semi-adaptive simulation. -/
  sa_value_bounded : ∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ)
    (v : (phfeClass ℓ n G.wG d).Out κ ((S).cprm κ pp)),
    ((phfeClass ℓ n G.wG d).encValue κ ((S).cprm κ pp) v).length ≤ b.eval κ

/-- The target is exactly the conjunction of its displayed algorithm obligations. 

**Proof sketch.** Destructure the target record into its fields; in the reverse direction, assemble
the record from the conjuncts. -/
theorem simTargets_iff :
    SimTargets G ℓ n d ↔
      (SamplesEfficiently
        (fun κ (pp : PublicParams (S).G κ) =>
          NUPPT.advInput κ pp.encode) (Sim).encSetupDraw
        (fun κ pp (o : (S).MPK κ pp × (Sim).St κ pp) =>
          pairEncode (List.ofFn ((S).encMPK κ pp o.1))
            (List.ofFn ((Sim).encSt κ pp o.2))) (Sim).setupCore) ∧
      (SamplesEfficiently (fun κ π => NUPPT.advInput κ ((Sim).encInputWord κ π))
        (fun κ π => (Sim).encEncDraw κ π.pp π.state π.omega)
        (fun κ π (o : (S).CT κ π.pp × (Sim).St κ π.pp) =>
          pairEncode (List.ofFn ((S).encCT κ π.pp o.1)) (List.ofFn ((Sim).encSt κ π.pp o.2)))
        (fun κ π => (Sim).encCore κ π.pp π.state π.omega)) ∧
      (SamplesEfficiently (fun κ π => NUPPT.advInput κ ((Sim).keyInputWord κ π))
        (fun κ π => (Sim).encKeyDraw κ π.pp π.state π.omega π.index)
        (fun κ π (o : (S).SK κ π.pp × (Sim).St κ π.pp) =>
          pairEncode (List.ofFn ((S).encSK κ π.pp o.1)) (List.ofFn ((Sim).encSt κ π.pp o.2)))
        (fun κ π => (Sim).keyCore κ π.pp π.state π.omega π.index)) ∧
      (SamplesEfficiently
        (fun κ (pp : PublicParams (S).G κ) =>
          NUPPT.advInput κ pp.encode) (SASim).encSetupDraw
        (fun κ pp (o : (S).MPK κ pp × (SASim).St κ pp) =>
          pairEncode (List.ofFn ((S).encMPK κ pp o.1))
            (List.ofFn ((SASim).encSt κ pp o.2))) (SASim).setupCore)
            ∧
      (SamplesEfficiently (fun κ π => NUPPT.advInput κ ((SASim).encInputWord κ π))
        (fun κ π => (SASim).encEncDraw κ π.pp π.state π.publicInput)
        (fun κ π (o : (S).CT κ π.pp × (SASim).St κ π.pp) =>
          pairEncode (List.ofFn ((S).encCT κ π.pp o.1)) (List.ofFn ((SASim).encSt κ π.pp o.2)))
        (fun κ π => (SASim).encCore κ π.pp π.state π.publicInput)) ∧
      (SamplesEfficiently (fun κ π => NUPPT.advInput κ ((SASim).keyInputWord κ π))
        (fun κ π => (SASim).encKeyDraw κ π.pp π.state π.publicInput π.function π.value)
        (fun κ π (o : (S).SK κ π.pp × (SASim).St κ π.pp) =>
          pairEncode (List.ofFn ((S).encSK κ π.pp o.1)) (List.ofFn ((SASim).encSt κ π.pp o.2)))
        (fun κ π => (SASim).keyCore κ π.pp π.state π.publicInput π.function π.value)) ∧
      (∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ) (st : (Sim).St κ pp),
        (List.ofFn ((Sim).encSt κ pp st)).length ≤ b.eval κ) ∧
      (∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ)
        (v : (phfeClass ℓ n G.wG d).Out κ ((S).cprm κ pp)),
        ((phfeClass ℓ n G.wG d).encValue κ ((S).cprm κ pp) v).length ≤ b.eval κ) ∧
      (∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ) (st : (SASim).St κ pp),
        (List.ofFn ((SASim).encSt κ pp st)).length ≤ b.eval κ) ∧
      (∃ b : PolyExpr, ∀ κ (pp : PublicParams (S).G κ)
        (v : (phfeClass ℓ n G.wG d).Out κ ((S).cprm κ pp)),
        ((phfeClass ℓ n G.wG d).encValue κ ((S).cprm κ pp) v).length ≤ b.eval κ) :=
  ⟨fun h => ⟨h.sim_setup_eff, h.sim_enc_eff, h.sim_key_eff,
      h.sa_setup_eff, h.sa_enc_eff, h.sa_key_eff, h.sim_state_bounded,
      h.sim_value_bounded, h.sa_state_bounded, h.sa_value_bounded⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩⟩

end

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
