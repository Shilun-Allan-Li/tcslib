import TCSlib.Cryptography.Candidates.ElGamal
import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.Encryption
import TCSlib.Cryptography.Candidates.Factoring
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Asymptotic.Universal
import TCSlib.Cryptography.Asymptotic.PublicKey
import TCSlib.Cryptography.Asymptotic.HardCoreClaims
import TCSlib.Cryptography.Asymptotic.HardCorePermutation
import TCSlib.Cryptography.Asymptotic.GGMReductionEval
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol

#print axioms Complexity.pairFstD_eq
#print axioms Complexity.pairFstD_of_pairDecode_eq_none
#print axioms Complexity.pairSndD_eq
#print axioms Complexity.pairSndD_of_pairDecode_eq_none
#print axioms Complexity.NUPPT.Uniform.advice_eq
#print axioms Complexity.NUPPT.uniform_iff
#print axioms TCSlib.Cryptography.Collection.owfCoinsEquiv
#print axioms TCSlib.Cryptography.Collection.owfCoinsEquiv_ofFn
#print axioms TCSlib.Cryptography.Collection.owfCoinsEquiv_symm_ofFn
#print axioms TCSlib.Cryptography.prgScheme_encCoinsEquiv
#print axioms TCSlib.Cryptography.prgScheme_encCoinsEquiv_ofFn
#print axioms TCSlib.Cryptography.prgScheme_genCoinsEquiv
#print axioms TCSlib.Cryptography.prgScheme_genCoinsEquiv_ofFn
#print axioms TCSlib.Cryptography.GGMRed.coinPoly_eq
#print axioms TCSlib.Cryptography.GGMRed.coinPoly_eval
#print axioms TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv
#print axioms TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv_ofFn
#print axioms TCSlib.Cryptography.FunFamily.glBit_equiv
#print axioms TCSlib.Cryptography.FunFamily.glPad_f_equiv
#print axioms TCSlib.Cryptography.FunFamily.glPad_inEquiv
#print axioms TCSlib.Cryptography.FunFamily.glPad_inEquiv_ofFn
#print axioms TCSlib.Cryptography.FunFamily.glPad_inEquiv_symm_ofFn
#print axioms TCSlib.Cryptography.FunFamily.glPad_inLen_eval
#print axioms TCSlib.Cryptography.FunFamily.glPad_outEquiv
#print axioms TCSlib.Cryptography.FunFamily.glPad_outEquiv_ofFn
#print axioms TCSlib.Cryptography.FunFamily.glPad_outEquiv_symm_ofFn
#print axioms TCSlib.Cryptography.FunFamily.glPad_outLen_eval
#print axioms TCSlib.Cryptography.PRG.expand_G_stretch
#print axioms TCSlib.Cryptography.PRG.expand_stretch
#print axioms TCSlib.Cryptography.PRG.oneBit_secure_iff
#print axioms TCSlib.Cryptography.PermFamily.HardCore
#print axioms TCSlib.Cryptography.PermFamily.HardCore.easy
#print axioms TCSlib.Cryptography.PermFamily.HardCore.hard
#print axioms TCSlib.Cryptography.PermFamily.HardCore.of_easy_hard
#print axioms TCSlib.Cryptography.PermFamily.glPad_inEquiv
#print axioms TCSlib.Cryptography.PermFamily.glPad_inEquiv_ofFn
#print axioms TCSlib.Cryptography.PermFamily.glPad_inEquiv_symm_ofFn
#print axioms TCSlib.Cryptography.PermFamily.glPad_inLen_eval
#print axioms TCSlib.Cryptography.PermFamily.glPad_outEquiv
#print axioms TCSlib.Cryptography.PermFamily.glPad_outEquiv_ofFn
#print axioms TCSlib.Cryptography.PermFamily.glPad_outEquiv_symm_ofFn
#print axioms TCSlib.Cryptography.PermFamily.glPad_outLen_eval
#print axioms TCSlib.Cryptography.PermFamily.hardCore_iff
#print axioms TCSlib.Cryptography.PermFamily.predProb_toFunFamily
#print axioms TCSlib.Cryptography.owpGenPRG_G_outEquiv
#print axioms TCSlib.Cryptography.owpGenPRG_outEquiv
#print axioms TCSlib.Cryptography.owpGenPRG_outEquiv_ofFn
#print axioms Complexity.NUPPT.wrapCoinsEquiv
#print axioms Complexity.NUPPT.wrapCoinsEquiv_symm_ofFn
#print axioms Complexity.NUPPT.wrap_coinLen
#print axioms TCSlib.Cryptography.FunFamily.blocks_apply
#print axioms TCSlib.Cryptography.FunFamily.ofString_inLen_eval
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv_ofFn
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv_symm_ofFn
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv_ofFn
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv_symm_ofFn
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_f_domEquiv
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_inLen
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_inLen_eval
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_outLen
#print axioms TCSlib.Cryptography.PermFamily.toFunFamily_outLen_eval
#print axioms TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv
#print axioms TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv_ofFn
#print axioms TCSlib.Cryptography.OneWay.yaoB_apply
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins_ofFn
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_coinLen
#print axioms TCSlib.Cryptography.tdpPredictor_coinLen
#print axioms TCSlib.Cryptography.fUniversal_inLen_eval
#print axioms TCSlib.Cryptography.Candidates.prodInverter_eq
#print axioms TCSlib.Cryptography.GI.giProtocolRep_V_coinLen
#print axioms TCSlib.Cryptography.GI.giProtocol_V_coinLen
#print axioms TCSlib.Cryptography.GI.gniProtocolRep_V_coinLen
#print axioms TCSlib.Cryptography.GI.gniProtocol_V_coinLen
#print axioms TCSlib.Cryptography.edgeIdxOfMsg_eq
#print axioms TCSlib.Cryptography.msgAt_eq
#print axioms TCSlib.Cryptography.owp_hardcore_prg
#print axioms TCSlib.Cryptography.cor_81_7
#print axioms TCSlib.Cryptography.OneWayPermutation.glHalf
#print axioms TCSlib.Cryptography.exists_owp_hardCore
#print axioms TCSlib.Cryptography.HardCore.bitHiding
#print axioms TCSlib.Cryptography.owp_commitment
#print axioms TCSlib.Cryptography.thm_87_3_9
#print axioms TCSlib.Cryptography.PermFamily.glHalf_f_even
#print axioms TCSlib.Cryptography.invProb_glHalf_odd_le
#print axioms TCSlib.Cryptography.glHalf_predProb_odd
#print axioms TCSlib.Cryptography.Candidates.eval_fmultWeakPoly
#print axioms TCSlib.Cryptography.Candidates.fmult_prod_inLen
#print axioms TCSlib.Cryptography.Candidates.samplePairOut_eq_encode
#print axioms TCSlib.Cryptography.Candidates.factoringCollection_index
#print axioms TCSlib.Cryptography.GI.gniTapes_apply
#print axioms TCSlib.Cryptography.ofFn_fUniversal_f
#print axioms TCSlib.Cryptography.PadQuad.quadraticCode_of_linear
#print axioms TCSlib.Cryptography.Candidates.rsaCollection_index

#print axioms TCSlib.Cryptography.R3COL_witnessRelation
#print axioms TCSlib.Cryptography.Candidates.statClose_of_uprob_ne
