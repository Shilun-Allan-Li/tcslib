import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Encoding

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

theorem ctl065Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.D_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.D_eq)

theorem ctl065Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.D_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.D_eq

theorem ctl066Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ℓ_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ℓ_eq)

theorem ctl066Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ℓ_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ℓ_eq

theorem ctl067Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.n_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.n_eq)

theorem ctl067Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.n_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.n_eq

theorem ctl068Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.m_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.m_eq)

theorem ctl068Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.m_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.m_eq

theorem ctl069Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseWidth_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseWidth_eq)

theorem ctl069Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseWidth_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseWidth_eq

theorem ctl070Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseDenAt_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseDenAt_eq)

theorem ctl070Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseDenAt_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.noiseDenAt_eq

theorem ctl071Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq)

theorem ctl071Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq

theorem ctl072Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq)

theorem ctl072Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.w_eq

theorem ctl073Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.t_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.t_eq)

theorem ctl073Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.t_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.t_eq

theorem ctl074Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rc_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rc_eq)

theorem ctl074Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rc_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rc_eq

theorem ctl075Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cap_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cap_eq)

theorem ctl075Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cap_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.cap_eq

theorem ctl076Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.B_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.B_eq)

theorem ctl076Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.B_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.B_eq

theorem ctl077Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.Γ_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.Γ_eq)

theorem ctl077Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.Γ_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.Γ_eq

theorem ctl078Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOf_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOf_eq)

theorem ctl078Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOf_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOf_eq

theorem ctl079Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOfN_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOfN_eq)

theorem ctl079Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOfN_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOfN_eq

theorem ctl080Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubLen_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubLen_eq)

theorem ctl080Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubLen_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubLen_eq

theorem ctl081Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sLen_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sLen_eq)

theorem ctl081Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sLen_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sLen_eq

theorem ctl082Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privLen_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privLen_eq)

theorem ctl082Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privLen_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privLen_eq

theorem ctl083Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarEquiv_eq)

theorem ctl083Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarEquiv_eq

theorem ctl084Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privEquiv_eq)

theorem ctl084Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.privEquiv_eq

theorem ctl085Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubEquiv_eq)

theorem ctl085Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubEquiv_eq

theorem ctl086Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_raw_samples) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_raw_samples)

theorem ctl086Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_raw_samples) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.lpnFamily_raw_samples

end StructuredSeedSensitivity

