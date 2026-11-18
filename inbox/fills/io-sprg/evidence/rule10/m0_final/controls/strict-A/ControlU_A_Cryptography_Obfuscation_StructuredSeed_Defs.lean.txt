import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs

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

theorem ctl026Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdxFintype_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdxFintype_eq))

theorem ctl026Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdxFintype_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdxFintype_eq

theorem ctl027Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdDrawFintype_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdDrawFintype_eq))

theorem ctl027Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdDrawFintype_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.instBoolPRGIdDrawFintype_eq

theorem ctl028Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.idSamp_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.idSamp_eq))

theorem ctl028Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.idSamp_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.idSamp_eq

theorem ctl029Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.evalEfficient_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.evalEfficient_iff))

theorem ctl029Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.evalEfficient_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.evalEfficient_iff

theorem ctl030Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.challengeStr_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.challengeStr_eq))

theorem ctl030Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.challengeStr_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.challengeStr_eq

theorem ctl031Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.game_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.game_eq))

theorem ctl031Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.game_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.game_eq

theorem ctl032Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.adv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.adv_eq))

theorem ctl032Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.adv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.adv_eq

theorem ctl033Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.secure_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.secure_iff))

theorem ctl033Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.secure_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.secure_iff

theorem ctl034Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.subexpSecure_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.subexpSecure_iff))

theorem ctl034Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.subexpSecure_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.subexpSecure_iff

theorem ctl035Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.hasStretch_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.hasStretch_iff))

theorem ctl035Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.hasStretch_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.hasStretch_iff

theorem ctl036Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.hasLocality_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.hasLocality_iff))

theorem ctl036Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.hasLocality_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.hasLocality_iff

theorem ctl037Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.termsEfficient_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.termsEfficient_iff))

theorem ctl037Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.termsEfficient_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.MultilinearRep.termsEfficient_iff

theorem ctl038Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.pubDegree_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.pubDegree_eq))

theorem ctl038Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.pubDegree_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.pubDegree_eq

theorem ctl039Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.privDegree_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.privDegree_eq))

theorem ctl039Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.privDegree_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.privDegree_eq

end StructuredSeedSensitivity

