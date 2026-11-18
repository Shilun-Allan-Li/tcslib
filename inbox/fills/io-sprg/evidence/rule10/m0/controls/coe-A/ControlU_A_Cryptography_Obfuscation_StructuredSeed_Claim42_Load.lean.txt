import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Load

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

theorem ctl115Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucket_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucket_eq)

theorem ctl115Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucket_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucket_eq

theorem ctl116Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.load_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.load_eq)

theorem ctl116Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.load_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.load_eq

theorem ctl117Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.overfull_iff) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.overfull_iff)

theorem ctl117Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.overfull_iff) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.overfull_iff

theorem ctl118Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.rank_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.rank_eq)

theorem ctl118Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.rank_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.rank_eq

theorem ctl119Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.indexMap_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.indexMap_eq)

theorem ctl119Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.indexMap_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.indexMap_eq

theorem ctl120Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucketMatrix_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucketMatrix_eq)

theorem ctl120Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucketMatrix_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets.bucketMatrix_eq

end StructuredSeedSensitivity

