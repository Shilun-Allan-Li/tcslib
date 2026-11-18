import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Params

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

theorem ctl001Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.lpnNoise_coins) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.lpnNoise_coins))

theorem ctl001Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.lpnNoise_coins) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.lpnNoise_coins

theorem ctl002Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.parameters_dimension) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.parameters_dimension))

theorem ctl002Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.parameters_dimension) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.parameters_dimension

theorem ctl003Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noise_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noise_eq))

theorem ctl003Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noise_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noise_eq

theorem ctl004Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.toLWE_parameters) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.toLWE_parameters))

theorem ctl004Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.toLWE_parameters) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.toLWE_parameters

theorem ctl005Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.adv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.adv_eq))

theorem ctl005Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.adv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.adv_eq

theorem ctl006Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.assumption_toLWE_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.assumption_toLWE_iff))

theorem ctl006Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.assumption_toLWE_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.assumption_toLWE_iff

theorem ctl007Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawCard_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawCard_eq))

theorem ctl007Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawCard_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawCard_eq

theorem ctl008Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.residueEquiv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.residueEquiv_eq))

theorem ctl008Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.residueEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.residueEquiv_eq

theorem ctl009Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.vectorEquiv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.vectorEquiv_eq))

theorem ctl009Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.vectorEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.vectorEquiv_eq

theorem ctl010Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.matrixEquiv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.matrixEquiv_eq))

theorem ctl010Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.matrixEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.matrixEquiv_eq

theorem ctl011Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseSeedEquiv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseSeedEquiv_eq))

theorem ctl011Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseSeedEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseSeedEquiv_eq

theorem ctl012Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseVectorEquiv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseVectorEquiv_eq))

theorem ctl012Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseVectorEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.noiseVectorEquiv_eq

theorem ctl013Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawEquiv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawEquiv_eq))

theorem ctl013Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.drawEquiv_eq

theorem ctl014Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleCore_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleCore_eq))

theorem ctl014Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleCore_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleCore_eq

theorem ctl015Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleLaw_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleLaw_eq))

theorem ctl015Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleLaw_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleLaw_eq

theorem ctl016Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleWord_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleWord_eq))

theorem ctl016Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleWord_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.sampleWord_eq

theorem ctl017Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encDraw_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encDraw_eq))

theorem ctl017Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encDraw_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encDraw_eq

theorem ctl018Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encSample_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encSample_eq))

theorem ctl018Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encSample_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.Raw.encSample_eq

theorem ctl019Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.toLWE_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.toLWE_eq))

theorem ctl019Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.toLWE_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.toLWE_eq

theorem ctl020Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.adv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.adv_eq))

theorem ctl020Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.adv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.adv_eq

theorem ctl021Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.assumption_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.assumption_iff))

theorem ctl021Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.assumption_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.LPNFamily.assumption_iff

theorem ctl040Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.PrimeParam.enc_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.PrimeParam.enc_eq))

theorem ctl040Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.PrimeParam.enc_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.PrimeParam.enc_eq

theorem ctl041Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdxFintype_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdxFintype_eq))

theorem ctl041Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdxFintype_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdxFintype_eq

theorem ctl042Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdDrawFintype_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdDrawFintype_eq))

theorem ctl042Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdDrawFintype_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instIdDrawFintype_eq

theorem ctl043Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instSdDrawFintype_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instSdDrawFintype_eq))

theorem ctl043Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instSdDrawFintype_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.instSdDrawFintype_eq

theorem ctl044Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idSamp_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idSamp_eq))

theorem ctl044Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idSamp_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idSamp_eq

theorem ctl045Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdSamp_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdSamp_eq))

theorem ctl045Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdSamp_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdSamp_eq

theorem ctl046Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encPP_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encPP_eq))

theorem ctl046Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encPP_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encPP_eq

theorem ctl047Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encSeed_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encSeed_eq))

theorem ctl047Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encSeed_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encSeed_eq

theorem ctl048Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.challengeStr_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.challengeStr_eq))

theorem ctl048Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.challengeStr_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.challengeStr_eq

theorem ctl049Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.game_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.game_eq))

theorem ctl049Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.game_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.game_eq

theorem ctl050Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.adv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.adv_eq))

theorem ctl050Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.adv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.adv_eq

theorem ctl051Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.secure_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.secure_iff))

theorem ctl051Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.secure_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.secure_iff

theorem ctl052Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.subexpSecure_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.subexpSecure_iff))

theorem ctl052Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.subexpSecure_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.subexpSecure_iff

theorem ctl053Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.seedBits_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.seedBits_eq))

theorem ctl053Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.seedBits_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.seedBits_eq

theorem ctl054Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasPolyStretch_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasPolyStretch_iff))

theorem ctl054Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasPolyStretch_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasPolyStretch_iff

theorem ctl055Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexity_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexity_iff))

theorem ctl055Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexity_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexity_iff

theorem ctl056Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.evalEfficient_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.evalEfficient_iff))

theorem ctl056Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.evalEfficient_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.evalEfficient_iff

theorem ctl057Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idWord_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idWord_eq))

theorem ctl057Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idWord_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.idWord_eq

theorem ctl058Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdWord_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdWord_eq))

theorem ctl058Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdWord_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.sdWord_eq

theorem ctl059Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexityEff_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexityEff_iff))

theorem ctl059Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexityEff_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.hasComplexityEff_iff

theorem ctl060Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.secure_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.secure_iff))

theorem ctl060Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.secure_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.secure_iff

theorem ctl061Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexity_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexity_iff))

theorem ctl061Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexity_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexity_iff

theorem ctl062Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexityEff_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexityEff_iff))

theorem ctl062Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexityEff_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasComplexityEff_iff

theorem ctl063Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasPolyStretch_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasPolyStretch_iff))

theorem ctl063Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasPolyStretch_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.hasPolyStretch_iff

theorem ctl064Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.adv_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.adv_eq))

theorem ctl064Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.adv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.adv_eq

end StructuredSeedSensitivity

