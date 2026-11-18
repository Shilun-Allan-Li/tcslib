import Lean
import TCSlib.Cryptography.Obfuscation

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

theorem ctl196Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idWord_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idWord_eq))

theorem ctl196Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idWord_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idWord_eq

theorem ctl197Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdWord_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdWord_eq))

theorem ctl197Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdWord_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdWord_eq

theorem ctl198Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.evalTarget_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.evalTarget_iff))

theorem ctl198Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.evalTarget_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.evalTarget_iff

theorem ctl199Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.qGenTarget_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.qGenTarget_iff))

theorem ctl199Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.qGenTarget_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.qGenTarget_iff

theorem ctl200Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.coreTarget_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.coreTarget_iff))

theorem ctl200Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.coreTarget_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.coreTarget_iff

theorem ctl201Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPreTarget_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPreTarget_iff))

theorem ctl201Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPreTarget_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnPreTarget_iff

theorem ctl202Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPreTarget_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPreTarget_iff))

theorem ctl202Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPreTarget_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPreTarget_iff

theorem ctl203Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.reductionTargets_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.reductionTargets_iff))

theorem ctl203Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.reductionTargets_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.reductionTargets_iff

theorem ctl204Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawSamplerTarget_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawSamplerTarget_iff))

theorem ctl204Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawSamplerTarget_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawSamplerTarget_iff

theorem ctl205Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnSamplerTarget_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnSamplerTarget_iff))

theorem ctl205Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnSamplerTarget_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnSamplerTarget_iff

theorem ctl206Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.targets_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.targets_iff))

theorem ctl206Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.targets_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.targets_iff

theorem ctl207Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_toRaw) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_toRaw))

theorem ctl207Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_toRaw) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_toRaw

theorem ctl208Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_toRaw) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_toRaw))

theorem ctl208Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_toRaw) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG_toRaw

end StructuredSeedSensitivity

