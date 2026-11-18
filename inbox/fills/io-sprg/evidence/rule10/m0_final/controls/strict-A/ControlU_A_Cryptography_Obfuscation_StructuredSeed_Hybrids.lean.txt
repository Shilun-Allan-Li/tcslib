import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids

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

theorem ctl159Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond1_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond1_iff))

theorem ctl159Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond1_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond1_iff

theorem ctl160Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond2_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond2_iff))

theorem ctl160Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond2_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond2_iff

theorem ctl161Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond3_iff) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond3_iff))

theorem ctl161Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond3_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cond3_iff

theorem ctl162Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.jointLaw_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.jointLaw_eq))

theorem ctl162Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.jointLaw_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.jointLaw_eq

theorem ctl163Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errProb_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errProb_eq))

theorem ctl163Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errProb_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.errProb_eq

end StructuredSeedSensitivity

