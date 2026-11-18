import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Security

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

theorem ctl157Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.E0_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.E0_eq)

theorem ctl157Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.E0_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.E0_eq

theorem ctl158Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBitsAt_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBitsAt_eq)

theorem ctl158Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBitsAt_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBitsAt_eq

theorem ctl168Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnEnc_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnEnc_eq)

theorem ctl168Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnEnc_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnEnc_eq

theorem ctl169Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnChalEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnChalEquiv_eq)

theorem ctl169Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnChalEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnChalEquiv_eq

theorem ctl170Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceProductEquiv_apply) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceProductEquiv_apply)

theorem ctl170Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceProductEquiv_apply) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceProductEquiv_apply

theorem ctl171Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceCard_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceCard_eq)

theorem ctl171Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceCard_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceCard_eq

theorem ctl172Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceEquiv_eq)

theorem ctl172Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceEquiv_eq

theorem ctl173Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instLPNAdviceFintype_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instLPNAdviceFintype_eq)

theorem ctl173Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instLPNAdviceFintype_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instLPNAdviceFintype_eq

theorem ctl174Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encLPNAdvice_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encLPNAdvice_eq)

theorem ctl174Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encLPNAdvice_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encLPNAdvice_eq

theorem ctl175Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceBound_eq)

theorem ctl175Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnAdviceBound_eq

theorem ctl176Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnMatrixAt_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnMatrixAt_eq)

theorem ctl176Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnMatrixAt_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnMatrixAt_eq

theorem ctl177Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnValuesAt_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnValuesAt_eq)

theorem ctl177Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnValuesAt_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnValuesAt_eq

theorem ctl178Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPre_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPre_eq)

theorem ctl178Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPre_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPre_eq

theorem ctl179Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnRed_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnRed_eq)

theorem ctl179Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnRed_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnRed_eq

theorem ctl180Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.LPNRealizable_iff) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.LPNRealizable_iff)

theorem ctl180Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.LPNRealizable_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.LPNRealizable_iff

theorem ctl181Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalCard_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalCard_eq)

theorem ctl181Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalCard_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalCard_eq

theorem ctl182Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalEquiv_eq)

theorem ctl182Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgChalEquiv_eq

theorem ctl183Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgEnc_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgEnc_eq)

theorem ctl183Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgEnc_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgEnc_eq

theorem ctl184Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGAdvice.prodEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGAdvice.prodEquiv_eq)

theorem ctl184Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGAdvice.prodEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGAdvice.prodEquiv_eq

theorem ctl185Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceCard_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceCard_eq)

theorem ctl185Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceCard_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceCard_eq

theorem ctl186Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceEquiv_eq)

theorem ctl186Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceEquiv_eq

theorem ctl187Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceFintype_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceFintype_eq)

theorem ctl187Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceFintype_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceFintype_eq

theorem ctl188Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceInhabited_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceInhabited_eq)

theorem ctl188Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceInhabited_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.instPRGAdviceInhabited_eq

theorem ctl189Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encPRGAdvice_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encPRGAdvice_eq)

theorem ctl189Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encPRGAdvice_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encPRGAdvice_eq

theorem ctl190Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceDataBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceDataBound_eq)

theorem ctl190Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceDataBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceDataBound_eq

theorem ctl191Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceBound_eq)

theorem ctl191Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgAdviceBound_eq

theorem ctl192Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPre_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPre_eq)

theorem ctl192Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPre_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPre_eq

theorem ctl193Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgRed_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgRed_eq)

theorem ctl193Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgRed_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgRed_eq

theorem ctl194Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGRealizable_iff) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGRealizable_iff)

theorem ctl194Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGRealizable_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGRealizable_iff

end StructuredSeedSensitivity

