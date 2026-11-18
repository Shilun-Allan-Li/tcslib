/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw
import TCSlib.Cryptography.CoinSampling.Contract
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Honest-algorithm efficiency targets

The targets name the shared sampler contract and deterministic decryption specification
for the explicit layered construction. No target is proved and no machine is constructed.

## Main definitions

* `SchemeTargets`: five honest uniform-efficiency obligations.

## Main results

* `schemeTargets_iff`: the explicit conjunction reader.

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

local notation "C" => phfeClass ℓ n G.wG d
local notation "S" => wee20PHFE_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)

/-- The five honest-algorithm fields are the exact efficient-interface obligations for the
concrete layered PHFE construction [GJLS21, Definition 4.1; Wee20, Section 3.1].
Phase B obligation; not proved in this development.

The public-generation target covers the nonidentity-generator draw after the already
uniform description generator. Every sampler target uses one complete draw type. -/
structure SchemeTargets : Prop where
  /-- Uniformly draw the nonidentity public generator after the group description. -/
  pubGen_eff : SamplesEfficiently
    (fun κ (g : GroupDescription (S).G κ) => g.val)
    (fun κ g (r : GeneratorDraw (S).G κ g) => List.ofFn (((S).G.group κ g.val).encG r.val))
    (fun κ _ (pp : PublicParams (S).G κ) => pp.encode) (publicParamsCore (S).G)
  /-- Uniformly sample the complete honest setup draw and encode both keys. -/
  setup_eff : SamplesEfficiently
    (fun κ (pp : PublicParams (S).G κ) => pp.encode) (S).encSetupDraw
    (fun κ pp (o : (S).MPK κ pp × (S).MSK κ pp) =>
      pairEncode (List.ofFn ((S).encMPK κ pp o.1)) (List.ofFn ((S).encMSK κ pp o.2))) (S).setupCore
  /-- Uniformly sample encryption with pp, the public key, and both inputs supplied. -/
  enc_eff : SamplesEfficiently
    (fun κ (π : Σ pp : PublicParams (S).G κ,
        (S).MPK κ pp × (Fin ((C).pubLen.eval κ) → Bool) × (Fin ((C).privLen.eval κ) → Bool)) =>
      pairEncode π.1.encode (pairEncode (List.ofFn ((S).encMPK κ π.1 π.2.1))
        (pairEncode (List.ofFn π.2.2.1) (List.ofFn π.2.2.2))))
    (fun κ π => (S).encEncDraw κ π.1 π.2.1 π.2.2.1 π.2.2.2)
    (fun κ π (o : (S).CT κ π.1) => List.ofFn ((S).encCT κ π.1 o))
    (fun κ π => (S).encCore κ π.1 π.2.1 π.2.2.1 π.2.2.2)
  /-- Uniformly sample a function key with pp, the master key, and function supplied. -/
  keyGen_eff : SamplesEfficiently
    (fun κ (π : Σ pp : PublicParams (S).G κ, (S).MSK κ pp × (Fin ((C).fnLen.eval κ) → Bool)) =>
      pairEncode π.1.encode
        (pairEncode (List.ofFn ((S).encMSK κ π.1 π.2.1)) (List.ofFn π.2.2)))
    (fun κ π => (S).encKeyDraw κ π.1 π.2.1 π.2.2)
    (fun κ π (o : (S).SK κ π.1) => List.ofFn ((S).encSK κ π.1 o))
    (fun κ π => (S).keyCore κ π.1 π.2.1 π.2.2)
  /-- One polynomial-time map computes deterministic decryption at every public group. -/
  dec_eff : ∃ a : List Bool → List Bool, PolyTimeComputable a ∧
    ∀ κ (pp : PublicParams (S).G κ) (sk : (S).SK κ pp)
      (x : Fin ((C).pubLen.eval κ) → Bool) (ct : (S).CT κ pp),
      a (NUPPT.advInput κ (pairEncode pp.encode
        (pairEncode (List.ofFn ((S).encSK κ pp sk))
          (pairEncode (List.ofFn x) (List.ofFn ((S).encCT κ pp ct)))))) =
        match (S).dec κ pp sk x ct with
        | none => [false]
        | some o => true :: List.ofFn ((S).encDecOut κ pp o)

/-- The target is exactly the conjunction of its displayed algorithm obligations. 

**Proof sketch.** Destructure the target record into its fields; in the reverse direction, assemble
the record from the conjuncts. -/
theorem schemeTargets_iff :
    SchemeTargets G ℓ n d ↔
      (SamplesEfficiently
        (fun κ (g : GroupDescription (S).G κ) => g.val)
        (fun κ g (r : GeneratorDraw (S).G κ g) => List.ofFn (((S).G.group κ g.val).encG r.val))
        (fun κ _ (pp : PublicParams (S).G κ) => pp.encode) (publicParamsCore (S).G)) ∧
      (SamplesEfficiently
        (fun κ (pp : PublicParams (S).G κ) => pp.encode) (S).encSetupDraw
        (fun κ pp (o : (S).MPK κ pp × (S).MSK κ pp) =>
          pairEncode (List.ofFn ((S).encMPK κ pp o.1)) (List.ofFn ((S).encMSK κ pp o.2)))
            (S).setupCore) ∧
      (SamplesEfficiently
        (fun κ (π : Σ pp : PublicParams (S).G κ,
            (S).MPK κ pp × (Fin ((C).pubLen.eval κ) → Bool) × (Fin ((C).privLen.eval κ) → Bool)) =>
          pairEncode π.1.encode (pairEncode (List.ofFn ((S).encMPK κ π.1 π.2.1))
            (pairEncode (List.ofFn π.2.2.1) (List.ofFn π.2.2.2))))
        (fun κ π => (S).encEncDraw κ π.1 π.2.1 π.2.2.1 π.2.2.2)
        (fun κ π (o : (S).CT κ π.1) => List.ofFn ((S).encCT κ π.1 o))
        (fun κ π => (S).encCore κ π.1 π.2.1 π.2.2.1 π.2.2.2)) ∧
      (SamplesEfficiently
        (fun κ (π : Σ pp : PublicParams (S).G κ, (S).MSK κ pp × (Fin ((C).fnLen.eval κ) → Bool)) =>
          pairEncode π.1.encode
            (pairEncode (List.ofFn ((S).encMSK κ π.1 π.2.1)) (List.ofFn π.2.2)))
        (fun κ π => (S).encKeyDraw κ π.1 π.2.1 π.2.2)
        (fun κ π (o : (S).SK κ π.1) => List.ofFn ((S).encSK κ π.1 o))
        (fun κ π => (S).keyCore κ π.1 π.2.1 π.2.2)) ∧
      (∃ a : List Bool → List Bool, PolyTimeComputable a ∧
        ∀ κ (pp : PublicParams (S).G κ) (sk : (S).SK κ pp)
          (x : Fin ((C).pubLen.eval κ) → Bool) (ct : (S).CT κ pp),
          a (NUPPT.advInput κ (pairEncode pp.encode
            (pairEncode (List.ofFn ((S).encSK κ pp sk))
              (pairEncode (List.ofFn x) (List.ofFn ((S).encCT κ pp ct)))))) =
            match (S).dec κ pp sk x ct with
            | none => [false]
            | some o => true :: List.ofFn ((S).encDecOut κ pp o)) :=
  ⟨fun h => ⟨h.pubGen_eff, h.setup_eff, h.enc_eff, h.keyGen_eff, h.dec_eff⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

end

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
