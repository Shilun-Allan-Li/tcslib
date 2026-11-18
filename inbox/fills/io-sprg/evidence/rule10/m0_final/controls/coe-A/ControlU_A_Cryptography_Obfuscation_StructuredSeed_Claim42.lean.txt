import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option autoImplicit false
set_option relaxedAutoImplicit false

/- io-sprg control-only reflexivity elaborator. No tactics, no new axioms.
It constructs Eq.refl/Iff.refl under the full stored reader telescope, then asks the
normal elaborator to check that term against the reader's actual type. Thus sealed
negative controls fail the normal definitional-equality check rather than bypassing it. -/
open Lean Elab Term Meta in
elab "reader_rfl% " t:term : term => do
  let reader ← Lean.Elab.Term.elabTerm t none
  let ty ← Lean.Meta.inferType reader
  let proof ← Lean.Meta.forallTelescope ty fun xs body => do
    let body ← Lean.Meta.whnf body
    let p ← if body.isAppOfArity ``Eq 3 then
        Lean.Meta.mkEqRefl (body.getArg! 1)
      else if body.isAppOfArity ``Iff 2 then
        Lean.Meta.mkAppM ``Iff.refl #[body.getArg! 0]
      else throwError "reader_rfl% requires an Eq or Iff reader conclusion"
    Lean.Meta.mkLambdaFVars xs p
  Lean.Elab.Term.ensureHasType (some ty) proof

namespace StructuredSeedSensitivity

theorem ctl140Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseValue_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseValue_eq))

theorem ctl140Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseValue_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseValue_eq

theorem ctl141Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errSet_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errSet_eq))

theorem ctl141Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errSet_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errSet_eq

theorem ctl142Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.badSet_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.badSet_eq))

theorem ctl142Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.badSet_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.badSet_eq

theorem ctl143Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneFlag_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneFlag_eq))

theorem ctl143Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneFlag_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneFlag_eq

theorem ctl144Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.corr_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.corr_eq))

theorem ctl144Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.corr_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.corr_eq

theorem ctl145Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnVector_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnVector_eq))

theorem ctl145Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnVector_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnVector_eq

theorem ctl146Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneSd_flag) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneSd_flag))

theorem ctl146Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneSd_flag) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.oneSd_flag

theorem ctl147Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.firstGood_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.firstGood_eq))

theorem ctl147Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.firstGood_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.firstGood_eq

theorem ctl148Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.packSeed_fst) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.packSeed_fst))

theorem ctl148Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.packSeed_fst) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.packSeed_fst

theorem ctl149Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_σ) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_σ))

theorem ctl149Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_σ) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_σ

theorem ctl150Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idCore_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idCore_eq))

theorem ctl150Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idCore_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idCore_eq

theorem ctl151Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idSamp'_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idSamp'_eq))

theorem ctl151Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idSamp'_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idSamp'_eq

theorem ctl152Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSampFull_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSampFull_eq))

theorem ctl152Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSampFull_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSampFull_eq

theorem ctl153Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSamp'_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSamp'_eq))

theorem ctl153Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSamp'_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdSamp'_eq

theorem ctl154Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.eval'_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.eval'_eq))

theorem ctl154Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.eval'_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.eval'_eq

theorem ctl155Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.challengeStr_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.challengeStr_eq))

theorem ctl155Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.challengeStr_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.challengeStr_eq

theorem ctl156Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_raw_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_raw_eq))

theorem ctl156Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_raw_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_raw_eq

end StructuredSeedSensitivity

