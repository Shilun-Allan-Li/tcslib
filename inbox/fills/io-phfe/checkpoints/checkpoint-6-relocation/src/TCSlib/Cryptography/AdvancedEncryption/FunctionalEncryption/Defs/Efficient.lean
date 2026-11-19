/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw
import TCSlib.Cryptography.CoinSampling.Contract

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient functional-encryption interfaces

Each sampler has one exact draw type and the shared uniform sampler-efficiency contract.
Each deterministic core is implemented by one polynomial-time string function, chosen before
the security parameter and the public parameters. No sampler is constructed here.

## Main definitions

* `FEScheme`: raw public-key functional encryption together with honest efficiency fields.

## Main results

The raw projection retains the algorithms; efficiency does not change their exact laws.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing TCSlib.Cryptography.CoinSampling TCSlib.Cryptography.Pairing

/-- An efficient public-key functional-encryption scheme carries uniform efficiency for
public-parameter generation, setup, encryption, key generation, and decryption
[GJLS21, Definition 4.1].

The group-description generator is already uniformly efficient. The `pubGen_eff` field covers
the subsequent nonidentity-generator draw, conditional on the description. This keeps public
generation as sequential dependent draws without constructing a product sampler. -/
structure FEScheme (C : FnClass) extends FEScheme.Raw C where
  /-- Uniformly sample and attach the public generator after the group description. -/
  pubGen_eff : SamplesEfficiently
    (fun κ (d : GroupDescription G κ) =>
      NUPPT.advInput κ d.val)
    (fun κ d (g : GeneratorDraw G κ d) => List.ofFn ((G.group κ d.val).encG g.val))
    (fun κ _ (pp : PublicParams G κ) => pp.encode) (publicParamsCore G)
  /-- Uniformly sample the complete setup draw and compute the encoded key pair. -/
  setup_eff : SamplesEfficiently
    (fun κ (pp : PublicParams G κ) =>
      NUPPT.advInput κ pp.encode) encSetupDraw
    (fun κ pp (k : MPK κ pp × MSK κ pp) =>
      pairEncode (List.ofFn (encMPK κ pp k.1)) (List.ofFn (encMSK κ pp k.2))) setupCore
  /-- Uniformly sample encryption randomness with all other inputs on the parameter word. -/
  enc_eff : SamplesEfficiently
    (fun κ (π : Σ pp : PublicParams G κ,
        MPK κ pp × (Fin (C.pubLen.eval κ) → Bool) × (Fin (C.privLen.eval κ) → Bool)) =>
      NUPPT.advInput κ
        (pairEncode π.1.encode (pairEncode (List.ofFn (encMPK κ π.1 π.2.1))
           (pairEncode (List.ofFn π.2.2.1) (List.ofFn π.2.2.2)))))
    (fun κ π => encEncDraw κ π.1 π.2.1 π.2.2.1 π.2.2.2)
    (fun κ π (c : CT κ π.1) => List.ofFn (encCT κ π.1 c))
    (fun κ π => encCore κ π.1 π.2.1 π.2.2.1 π.2.2.2)
  /-- Uniformly sample key randomness with the master key and function on the input. -/
  keyGen_eff : SamplesEfficiently
    (fun κ (π : Σ pp : PublicParams G κ, MSK κ pp × (Fin (C.fnLen.eval κ) → Bool)) =>
      NUPPT.advInput κ
        (pairEncode π.1.encode
           (pairEncode (List.ofFn (encMSK κ π.1 π.2.1)) (List.ofFn π.2.2))))
    (fun κ π => encKeyDraw κ π.1 π.2.1 π.2.2)
    (fun κ π (k : SK κ π.1) => List.ofFn (encSK κ π.1 k))
    (fun κ π => keyCore κ π.1 π.2.1 π.2.2)
  /-- One polynomial-time decryption function works for every security and public parameter. -/
  dec_eff : ∃ a : List Bool → List Bool, PolyTimeComputable a ∧
    ∀ κ (pp : PublicParams G κ) (sk : SK κ pp)
      (x : Fin (C.pubLen.eval κ) → Bool) (ct : CT κ pp),
      a (NUPPT.advInput κ (pairEncode pp.encode
        (pairEncode (List.ofFn (encSK κ pp sk))
          (pairEncode (List.ofFn x) (List.ofFn (encCT κ pp ct)))))) =
        match dec κ pp sk x ct with
        | none => [false]
        | some o => true :: List.ofFn (encDecOut κ pp o)

namespace FEScheme

variable {C : FnClass} (S : FEScheme C)

/-- The raw projection preserves the public group generator. -/
theorem toRaw_G : S.toRaw.G = S.G := rfl

/-- The raw projection preserves the class-parameter interpretation. -/
theorem toRaw_cprm : S.toRaw.cprm = S.cprm := rfl

/-- The raw projection preserves the master public-key family. -/
theorem toRaw_MPK : S.toRaw.MPK = S.MPK := rfl

/-- The raw projection preserves the master secret-key family. -/
theorem toRaw_MSK : S.toRaw.MSK = S.MSK := rfl

/-- The raw projection preserves the functional-key family. -/
theorem toRaw_SK : S.toRaw.SK = S.SK := rfl

/-- The raw projection preserves the ciphertext family. -/
theorem toRaw_CT : S.toRaw.CT = S.CT := rfl

/-- The raw projection preserves the successful decryption-output family. -/
theorem toRaw_DecOut : S.toRaw.DecOut = S.DecOut := rfl

/-- The raw projection preserves the interpretation of class values in the output group. -/
theorem toRaw_embed : S.toRaw.embed = S.embed := rfl

/-- The raw projection preserves the deterministic setup core. -/
theorem toRaw_setupCore : S.toRaw.setupCore = S.setupCore := rfl

/-- The raw projection preserves the deterministic encryption core. -/
theorem toRaw_encCore : S.toRaw.encCore = S.encCore := rfl

/-- The raw projection preserves the deterministic key-generation core. -/
theorem toRaw_keyCore : S.toRaw.keyCore = S.keyCore := rfl

/-- The raw projection preserves deterministic decryption, including its failure result. -/
theorem toRaw_dec : S.toRaw.dec = S.dec := rfl

/-- The raw projection preserves the master public-key encoding. -/
theorem toRaw_encMPK : S.toRaw.encMPK = S.encMPK := rfl

/-- The raw projection preserves the functional-key encoding. -/
theorem toRaw_encSK : S.toRaw.encSK = S.encSK := rfl

/-- The raw projection preserves the ciphertext encoding. -/
theorem toRaw_encCT : S.toRaw.encCT = S.encCT := rfl

end FEScheme

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
