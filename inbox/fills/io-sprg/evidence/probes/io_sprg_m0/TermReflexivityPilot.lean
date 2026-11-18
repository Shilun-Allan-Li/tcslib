import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs

set_option maxHeartbeats 0

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


theorem eqPilot : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encPP_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.encPP_eq)

theorem iffPilot : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.secure_iff) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.SPRG.Raw.secure_iff)
