import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN

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

theorem ctl164Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.publicSeed_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.publicSeed_eq))

theorem ctl164Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.publicSeed_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.publicSeed_eq

theorem ctl165Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainPublic_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainPublic_eq))

theorem ctl165Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainPublic_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainPublic_eq

theorem ctl166Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainGame_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainGame_eq))

theorem ctl166Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainGame_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainGame_eq

theorem ctl167Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.hyb_eq) :=
  @(reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.hyb_eq))

theorem ctl167Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.hyb_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.hyb_eq

end StructuredSeedSensitivity

