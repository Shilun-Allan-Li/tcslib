import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Samplers

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

theorem ctl087Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.residueEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.residueEquiv_eq)

theorem ctl087Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.residueEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.residueEquiv_eq

theorem ctl088Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.vectorEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.vectorEquiv_eq)

theorem ctl088Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.vectorEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.vectorEquiv_eq

theorem ctl089Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.matrixEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.matrixEquiv_eq)

theorem ctl089Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.matrixEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.matrixEquiv_eq

theorem ctl090Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.boolVectorEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.boolVectorEquiv_eq)

theorem ctl090Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.boolVectorEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.boolVectorEquiv_eq

theorem ctl091Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseSeedEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseSeedEquiv_eq)

theorem ctl091Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseSeedEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseSeedEquiv_eq

theorem ctl092Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseVectorEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseVectorEquiv_eq)

theorem ctl092Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseVectorEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.noiseVectorEquiv_eq

theorem ctl093Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.oneDrawEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.oneDrawEquiv_eq)

theorem ctl093Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.oneDrawEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.ConstructionEncoding.oneDrawEquiv_eq

theorem ctl094Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxCard_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxCard_eq)

theorem ctl094Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxCard_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxCard_eq

theorem ctl095Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawCard_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawCard_eq)

theorem ctl095Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawCard_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawCard_eq

theorem ctl096Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawCard_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawCard_eq)

theorem ctl096Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawCard_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawCard_eq

theorem ctl097Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxEquiv_eq)

theorem ctl097Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxEquiv_eq

theorem ctl098Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawEquiv_eq)

theorem ctl098Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idDrawEquiv_eq

theorem ctl099Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawEquiv_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawEquiv_eq)

theorem ctl099Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawEquiv_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.drawEquiv_eq

theorem ctl100Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encBuckets_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encBuckets_eq)

theorem ctl100Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encBuckets_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encBuckets_eq

theorem ctl101Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdx'_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdx'_eq)

theorem ctl101Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdx'_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdx'_eq

theorem ctl102Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdDraw_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdDraw_eq)

theorem ctl102Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdDraw_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encIdDraw_eq

theorem ctl103Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encOneDraw_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encOneDraw_eq)

theorem ctl103Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encOneDraw_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encOneDraw_eq

theorem ctl104Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encDraw_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encDraw_eq)

theorem ctl104Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encDraw_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encDraw_eq

theorem ctl105Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encSeed'_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encSeed'_eq)

theorem ctl105Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encSeed'_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.encSeed'_eq

theorem ctl106Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ellBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ellBound_eq)

theorem ctl106Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ellBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.ellBound_eq

theorem ctl107Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.nBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.nBound_eq)

theorem ctl107Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.nBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.nBound_eq

theorem ctl108Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.mBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.mBound_eq)

theorem ctl108Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.mBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.mBound_eq

theorem ctl109Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bucketBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bucketBound_eq)

theorem ctl109Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bucketBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bucketBound_eq

theorem ctl110Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rcBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rcBound_eq)

theorem ctl110Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rcBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.rcBound_eq

theorem ctl111Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubBound_eq)

theorem ctl111Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.pubBound_eq

theorem ctl112Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarBound_eq)

theorem ctl112Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVarBound_eq

theorem ctl113Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBound_eq)

theorem ctl113Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.seedBound_eq

theorem ctl114Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxBound_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxBound_eq)

theorem ctl114Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxBound_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idxBound_eq

theorem ctl121Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseEntries_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseEntries_eq)

theorem ctl121Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseEntries_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseEntries_eq

theorem ctl122Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseLeft_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseLeft_eq)

theorem ctl122Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseLeft_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseLeft_eq

theorem ctl123Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseRight_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseRight_eq)

theorem ctl123Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseRight_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseRight_eq

theorem ctl124Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseFactor_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseFactor_eq)

theorem ctl124Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseFactor_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.sparseFactor_eq

theorem ctl125Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal.monomialSlot_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal.monomialSlot_eq)

theorem ctl125Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal.monomialSlot_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal.monomialSlot_eq

theorem ctl126Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.outputIndex_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.outputIndex_eq)

theorem ctl126Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.outputIndex_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.outputIndex_eq

theorem ctl127Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bVar_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bVar_eq)

theorem ctl127Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bVar_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.bVar_eq

theorem ctl128Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVar_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVar_eq)

theorem ctl128Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVar_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sVar_eq

theorem ctl129Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.uCoord_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.uCoord_eq)

theorem ctl129Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.uCoord_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.uCoord_eq

theorem ctl130Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.vCoord_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.vCoord_eq)

theorem ctl130Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.vCoord_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.vCoord_eq

theorem ctl131Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.linearCoeff_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.linearCoeff_eq)

theorem ctl131Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.linearCoeff_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.linearCoeff_eq

theorem ctl132Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.halfForm_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.halfForm_eq)

theorem ctl132Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.halfForm_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.halfForm_eq

theorem ctl133Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPoly_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPoly_eq)

theorem ctl133Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPoly_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPoly_eq

theorem ctl134Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.correctionPoly_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.correctionPoly_eq)

theorem ctl134Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.correctionPoly_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.correctionPoly_eq

theorem ctl135Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G1_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G1_eq)

theorem ctl135Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G1_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G1_eq

theorem ctl136Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G2_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G2_eq)

theorem ctl136Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G2_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G2_eq

theorem ctl137Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G3_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G3_eq)

theorem ctl137Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G3_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G3_eq

theorem ctl138Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4struct_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4struct_eq)

theorem ctl138Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4struct_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4struct_eq

theorem ctl139Negative : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4_eq) :=
  reader_rfl% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4_eq)

theorem ctl139Positive : type_of% (@TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4_eq) :=
  @TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4_eq

end StructuredSeedSensitivity

