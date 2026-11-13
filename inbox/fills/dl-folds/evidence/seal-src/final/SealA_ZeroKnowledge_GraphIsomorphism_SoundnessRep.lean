/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph non-isomorphism protocol: completeness and soundness

[PS10, Proposition 118.4] for the `|x|`-fold protocol `gniProtocolRep` (Prot-118.3, repeated),
proved for the shadow protocol of `GraphIsomorphism/Proofs.lean`; the main file closes
`gni_interactiveProof` by `exact GI.gni_interactiveProof gniVerifierRep_efficient`.

The verifier's graphs `H_i = σ_i(G_{b_i})` depend only on the number of replies received, so the
transcript against any prover is explicit (`exec_vfirst_eq`): the prover's `i`-th reply is its
next-message function on `[H_0, …, H_i]`. **Completeness** is exact: the honest prover's reply
is `b_i` for every tape (`gni_honest_reply`). **Soundness**: against isomorphic graphs, after
fixing the prover's coins and reading the verifier's tape as the `|x|` blocks
`(b_i, sampler coins_i)` (`gniTapes`), the acceptance event is the adaptive guessing event of
`uprob_gni_rep_cheat` (Lem-119.b) once the `|x|` sampled permutations are replaced by uniform
ones, which costs `|x| · permFailBound n` (`statClose_pi` of `statClose_samplePerm_long`); so
`Pr[accept] ≤ 2^{-|x|} + |x| · permFailBound n`, a negligible function of `|x|`
(`negligible_two_pow_neg`, `negligible_mul_permFailBound`).

## Main definitions

* `TCSlib.Cryptography.GI.blocksEquiv`, `GI.gniTapes` — a tape of `m · c` bits as `m` blocks,
  and the verifier's tape as (bits, sampler coins).

## Main results

* `TCSlib.Cryptography.GI.exec_vfirst_eq` — transcripts of verifier-first protocols whose
  verifier's messages depend only on the number of replies.
* `TCSlib.Cryptography.GI.statClose_pi` — `StatClose` for `m` independent copies.
* `TCSlib.Cryptography.GI.gniRep_complete`, `GI.gniRep_accept_le` — completeness and the
  acceptance bound of the `|x|`-fold protocol.
* `TCSlib.Cryptography.GI.gni_interactiveProofErrRep`, `GI.gni_interactiveProof` —
  [PS10, Proposition 118.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! Seal A (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean`, with every seal candidate of its
full TCSlib import closure (529 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.encodeNat _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.simulate _root_.Complexity.NUPPT.timeBound _root_.Complexity.P _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.TCSlib.Cryptography.AbortRetry.attempt _root_.TCSlib.Cryptography.AbortRetry.retry _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.acc _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.out _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.start _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.step _root_.TCSlib.Cryptography.EncodingMachines.bitsToNat_eq_blockVal.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.blockVal _root_.TCSlib.Cryptography.EncodingMachines.blockVal_lt.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.cbound _root_.TCSlib.Cryptography.EncodingMachines.cstep _root_.TCSlib.Cryptography.EncodingMachines.divNum _root_.TCSlib.Cryptography.EncodingMachines.findSome?_range_eq.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.firstIdx _root_.TCSlib.Cryptography.EncodingMachines.firstIdx_congr.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.firstIdx_congr.match_1_3 _root_.TCSlib.Cryptography.EncodingMachines.flatMap_range_ite_eq.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.foldr_swap_val.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.fyApply _root_.TCSlib.Cryptography.EncodingMachines.fyFail _root_.TCSlib.Cryptography.EncodingMachines.fyIter _root_.TCSlib.Cryptography.EncodingMachines.fyIter_le.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.fyTarget _root_.TCSlib.Cryptography.EncodingMachines.isBij _root_.TCSlib.Cryptography.EncodingMachines.loopState _root_.TCSlib.Cryptography.EncodingMachines.loopState.match_1 _root_.TCSlib.Cryptography.EncodingMachines.modNum _root_.TCSlib.Cryptography.EncodingMachines.offsetVal _root_.TCSlib.Cryptography.EncodingMachines.permFromCoinsNum _root_.TCSlib.Cryptography.EncodingMachines.permInvNum _root_.TCSlib.Cryptography.EncodingMachines.permNum _root_.TCSlib.Cryptography.EncodingMachines.rowFirst _root_.TCSlib.Cryptography.EncodingMachines.rowInv _root_.TCSlib.Cryptography.EncodingMachines.rowMap _root_.TCSlib.Cryptography.EncodingMachines.swapNum _root_.TCSlib.Cryptography.EncodingMachines.trialIdx _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.GI.Isomorphic _root_.TCSlib.Cryptography.GI.Liso _root_.TCSlib.Cryptography.GI.Lniso _root_.TCSlib.Cryptography.GI.Riso _root_.TCSlib.Cryptography.GI.decGraphAt _root_.TCSlib.Cryptography.GI.encInstance _root_.TCSlib.Cryptography.GI.giBitEquiv _root_.TCSlib.Cryptography.GI.giCoinEquiv _root_.TCSlib.Cryptography.GI.giProtocol _root_.TCSlib.Cryptography.GI.giProtocolRep _root_.TCSlib.Cryptography.GI.giProver _root_.TCSlib.Cryptography.GI.giProver.match_1 _root_.TCSlib.Cryptography.GI.giProverRep _root_.TCSlib.Cryptography.GI.giVerifier _root_.TCSlib.Cryptography.GI.giVerifier.match_1 _root_.TCSlib.Cryptography.GI.giVerifierRep _root_.TCSlib.Cryptography.GI.gniProtocol _root_.TCSlib.Cryptography.GI.gniProtocolRep _root_.TCSlib.Cryptography.GI.gniProver _root_.TCSlib.Cryptography.GI.gniVerifier _root_.TCSlib.Cryptography.GI.gniVerifier.match_1 _root_.TCSlib.Cryptography.GI.gniVerifierRep _root_.TCSlib.Cryptography.GI.ilayout _root_.TCSlib.Cryptography.GI.instanceG₀ _root_.TCSlib.Cryptography.GI.instanceG₁ _root_.TCSlib.Cryptography.GI.instanceVertexCount _root_.TCSlib.Cryptography.GI.instanceVertices _root_.TCSlib.Cryptography.GI.not_isomorphic_both.match_1_1 _root_.TCSlib.Cryptography.GI.permCoinLen _root_.TCSlib.Cryptography.GI.permFailBound _root_.TCSlib.Cryptography.GI.prefixLE _root_.TCSlib.Cryptography.GI.prefixLT _root_.TCSlib.Cryptography.GI.samplePerm _root_.TCSlib.Cryptography.GI.tapeSplit _root_.TCSlib.Cryptography.GI.vTapeSplit _root_.TCSlib.Cryptography.GI.wellFormedInstance _root_.TCSlib.Cryptography.HVZK _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.IP _root_.TCSlib.Cryptography.InteractiveProof.exists_accept.match_1_1 _root_.TCSlib.Cryptography.InteractiveProof.exists_accept.match_1_3 _root_.TCSlib.Cryptography.InteractiveProofErr.exists_accept.match_1_1 _root_.TCSlib.Cryptography.InteractiveProofErr.exists_accept.match_1_3 _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.PerfectZK _root_.TCSlib.Cryptography.PerfectZKAbort _root_.TCSlib.Cryptography.Protocol.ProverBounded _root_.TCSlib.Cryptography.Protocol.ProverBounded.exists_complete.match_1_1 _root_.TCSlib.Cryptography.Protocol.execution _root_.TCSlib.Cryptography.Protocol.outP _root_.TCSlib.Cryptography.Protocol.outV _root_.TCSlib.Cryptography.Protocol.transcript _root_.TCSlib.Cryptography.Protocol.transcriptWith _root_.TCSlib.Cryptography.Protocol.viewP _root_.TCSlib.Cryptography.Protocol.viewV _root_.TCSlib.Cryptography.Protocol.withV _root_.TCSlib.Cryptography.Protocol.withV_vCoinsEquiv _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.StatZK _root_.TCSlib.Cryptography.Strategy.Efficient _root_.TCSlib.Cryptography.Strategy.ReadsPrefix _root_.TCSlib.Cryptography.Strategy.coinLen _root_.TCSlib.Cryptography.Strategy.encodeMsgs _root_.TCSlib.Cryptography.Strategy.ofNUPPT _root_.TCSlib.Cryptography.Strategy.out _root_.TCSlib.Cryptography.View.encode _root_.TCSlib.Cryptography.ZK _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.coinTable _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decColoring _root_.TCSlib.Cryptography.decGraph _root_.TCSlib.Cryptography.decPerm _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.encColoring _root_.TCSlib.Cryptography.encGraph _root_.TCSlib.Cryptography.encPerm _root_.TCSlib.Cryptography.exec _root_.TCSlib.Cryptography.exec.match_1 _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.fisherYates _root_.TCSlib.Cryptography.fisherYates_injOn.match_1_1 _root_.TCSlib.Cryptography.foldr_swap_succ.match_1_1 _root_.TCSlib.Cryptography.fyOffsets _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.liftSucc _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.moverIsV _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.npProtocol _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.permBits _root_.TCSlib.Cryptography.permFromCoins _root_.TCSlib.Cryptography.permGraph _root_.TCSlib.Cryptography.permTrials _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.prod_sub_eq_factorial.match_1_1 _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.witnessLanguage _root_.TCSlib.Cryptography.witnessSet _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ### Transcripts of verifier-first protocols with history-independent graphs -/

/-- An entry of the list of a tuple below its length (any type). -/
theorem getD_ofFn_lt' {α : Type*} {c : ℕ} (t : Fin c → α) {i : ℕ} (hi : i < c) (d : α) :
    (List.ofFn t).getD i d = t ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- In a verifier-first execution of `2k` moves each party has received exactly `k` messages. -/
theorem exec_vfirst_length (P' V : Strategy) (x zP zV rP rV : List Bool) :
    ∀ k, (exec P' V true x zP zV rP rV (2 * k)).1.length = k ∧
      (exec P' V true x zP zV rP rV (2 * k)).2.length = k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : moverIsV true (2 * k) = true := by simp [moverIsV_def]
    have h2 : moverIsV true (2 * k + 1) = false := by
      simp only [moverIsV_true, decide_eq_false_iff_not]
      omega
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, exec_succ, exec_succ]
    simp only [h1, h2, Bool.false_eq_true, if_true, if_false, List.length_append, List.length_singleton]
    omega

/-- **Transcripts against a verifier whose first `m` messages depend only on the number of
replies received.** If `V.next x zV rV hist = Hf hist.length` whenever `hist.length < m`,
then after `2i ≤ 2m` moves of the verifier-first execution the prover has received
`H_0, …, H_{i-1}` and the verifier the replies `P'.next x zP rP [H_0, …, H_j]` for `j < i`.

**Proof sketch.** Induction on `i`: move `2i` is the verifier's (`moverIsV true (2i)`), who sends
`Hf i` on its `i` replies; move `2i + 1` is the prover's, who replies to `[H_0, …, H_i]`
(`List.range_succ`, `List.ofFn_succ_last`). -/
theorem exec_vfirst_eq (P' V : Strategy) (x zP zV rP rV : List Bool) (m : ℕ) (Hf : ℕ → List Bool)
    (hV : ∀ hist : List (List Bool), hist.length < m → V.next x zV rV hist = Hf hist.length) :
    ∀ i ≤ m, exec P' V true x zP zV rP rV (2 * i) =
      (List.map Hf (List.range i),
        List.ofFn fun j : Fin i => P'.next x zP rP (List.map Hf (List.range (j + 1)))) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hrec := ih (by omega)
    have h1 : moverIsV true (2 * i) = true := by simp [moverIsV_def]
    have h2 : moverIsV true (2 * i + 1) = false := by
      simp only [moverIsV_true, decide_eq_false_iff_not]
      omega
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, exec_succ, exec_succ, hrec]
    simp only [h1, h2, Bool.false_eq_true, if_true, if_false]
    rw [hV _ (by simp; omega)]
    simp only [List.length_ofFn]
    refine Prod.ext ?_ ?_
    · simp [List.range_succ]
    · rw [List.ofFn_succ_last]
      simp only [Fin.coe_castSucc, Fin.val_last, List.range_succ, List.map_append, List.map_singleton]

/-! ### The verdicts of the `|x|`-fold graph non-isomorphism protocol -/

/-- The honest prover's reply on an encoded instance: `decide (¬ G₀ ≅ last graph received)`. -/
theorem gniProver_next_enc {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) (hist : List (List Bool)) :
    gniProver.next (encInstance G₀ G₁) y r hist =
      [decide (¬ Isomorphic G₀ (decGraphAt n (hist.getLastD [])))] := by
  show [decide (¬ Isomorphic
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (hist.getLastD [])))] = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph]

/-- The `|x|`-fold verifier's graph of iteration `|hist|` on an encoded instance, while the
protocol is not over: `σ(G_b)` for the bit `b` and the sampler coins of the coin block.

**Proof sketch.** Read the repeated message as the single verifier's first message on the
current coin block (`gniVerifierRep_next_run`), then apply its public encoded-instance
message equation (`gniVerifier_next_nil`). -/
theorem gniVerifierRep_next_lt {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) (hist : List (List Bool))
    (h : hist.length < (encInstance G₀ G₁).length) :
    gniVerifierRep.next (encInstance G₀ G₁) z r hist =
      encGraph (permGraph
        (cond ((coinBlock (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).headD false) G₁ G₀)
        (samplePerm n ((coinBlock (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).drop 1))) :=
  (gniVerifierRep_next_run (encInstance G₀ G₁) z r hist h).trans
    (gniVerifier_next_nil G₀ G₁ z
      (coinBlock (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r))

/-- The `|x|`-fold verifier's verdict once `|x|` replies are in. -/
theorem gniVerifierRep_next_ge (x z r : List Bool) (hist : List (List Bool)) (h : x.length ≤ hist.length) :
    gniVerifierRep.next x z r hist =
      [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
        (hist.getD j []).headD false = (coinBlock (1 + (x.length + 1) ^ 2) j r).headD false)] :=
  (gniVerifierRep_next x z r hist).trans (if_neg (not_lt.2 h))

/-- The verdict of the `|x|`-fold protocol against a prover `P'`: the verifier's next-message
function on the `2|x|`-move execution. -/
theorem gniProtocolRep_outV (P' : Strategy) (x y z : List Bool) (r : gniProtocolRep.ExecCoins P' x) :
    gniProtocolRep.outV P' x y z r =
      gniVerifierRep.next x z (List.ofFn r.2)
        (exec P' gniVerifierRep true x y z (List.ofFn r.1) (List.ofFn r.2) (2 * x.length)).2 := rfl

/-- The graphs of the `|x|`-fold verifier on an encoded instance, as a function of the
iteration index. -/
noncomputable def gniGraphs {n : ℕ} (G₀ G₁ : Graph n) (rV : List Bool) (j : ℕ) : List Bool :=
  encGraph (permGraph
    (cond ((coinBlock (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j rV).headD false) G₁ G₀)
    (samplePerm n ((coinBlock (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j rV).drop 1)))

/-- The verdict of the `|x|`-fold protocol against `P'` on an encoded instance: every reply's
first bit equals the corresponding bit of the verifier's tape, the `j`-th reply being `P'`'s
next message on the graphs `H_0, …, H_j`. -/
theorem gniRep_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁)) :
    gniProtocolRep.outV P' (encInstance G₀ G₁) y z r =
      [decide (∀ j : Fin (encInstance G₀ G₁).length,
        (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
          (List.map (gniGraphs G₀ G₁ (List.ofFn r.2)) (List.range (j + 1)))).headD false =
        (coinBlock (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j (List.ofFn r.2)).headD false)] := by
  rw [gniProtocolRep_outV, exec_vfirst_eq P' gniVerifierRep (encInstance G₀ G₁) y z (List.ofFn r.1)
    (List.ofFn r.2) (encInstance G₀ G₁).length (gniGraphs G₀ G₁ (List.ofFn r.2))
    (fun hist hh => gniVerifierRep_next_lt G₀ G₁ z (List.ofFn r.2) hist hh) _ le_rfl,
    gniVerifierRep_next_ge _ _ _ _ (by simp), wellFormedInstance_encInstance]
  simp only [true_and]
  congr 1
  refine decide_eq_decide.2 (forall_congr' fun j => ?_)
  rw [getD_ofFn_lt' _ j.isLt]

/-- **Completeness of the `|x|`-fold graph non-isomorphism protocol** [PS10, Proposition 118.4]:
on a non-isomorphic encoded instance the honest prover's every reply is the verifier's bit
(`gni_honest_reply`), for every pair of tapes. -/
theorem gniRep_complete {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (y z : List Bool) :
    uprob (fun r : gniProtocolRep.ExecCoins gniProver (encInstance G₀ G₁) =>
      gniProtocolRep.outV gniProver (encInstance G₀ G₁) y z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gniRep_outV_eq]
  have hj : ∀ j : Fin (encInstance G₀ G₁).length,
      (gniProver.next (encInstance G₀ G₁) y (List.ofFn r.1)
        (List.map (gniGraphs G₀ G₁ (List.ofFn r.2)) (List.range (j + 1)))).headD false =
      (coinBlock (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j (List.ofFn r.2)).headD false := by
    intro j
    rw [gniProver_next_enc, List.headD_cons, List.range_succ, List.map_append, List.map_singleton,
      List.getLastD_concat, gniGraphs, decGraphAt_encGraph, gni_honest_reply h]
  simp only [hj, implies_true, decide_true]

/-! ### Tapes as blocks -/

/-- A tape of `m · c` bits as `m` blocks of `c` bits (`finProdFinEquiv`: block `i` occupies
the positions `i c, …, i c + c - 1`): the inverse of the canonical block bijection
`FunFamily.blocks`, kept as a compatibility alias with its reverse orientation. -/
def blocksEquiv (m c : ℕ) : (Fin m → Fin c → Bool) ≃ (Fin (m * c) → Bool) :=
  (FunFamily.blocks m c).symm

/-- `blocksEquiv` is the inverse of the canonical block bijection `FunFamily.blocks` of
`Asymptotic/Adversary.lean`: `blocksEquiv m c = (FunFamily.blocks m c).symm`. -/
theorem blocksEquiv_eq (m c : ℕ) : blocksEquiv m c = (FunFamily.blocks m c).symm := rfl

/-- Entry `k` of the tape of blocks is entry `k mod c` of block `k / c`. -/
theorem blocksEquiv_apply (m c : ℕ) (F : Fin m → Fin c → Bool) (k : Fin (m * c)) :
    blocksEquiv m c F k = F k.divNat k.modNat :=
  FunFamily.blocks_symm_apply m c F k

/-- Block `j < m` of the tape of blocks is the `j`-th block.

**Proof sketch.** Compare entries (`List.ext_getElem?`): entry `t < c` of the slice is entry
`j c + t` of the tape, which `blocksEquiv_apply` reads as entry `(j c + t) mod c = t` of block
`(j c + t) / c = j`; entries `t ≥ c` are absent on both sides. -/
theorem coinSlice_blocksEquiv (m c : ℕ) (F : Fin m → Fin c → Bool) {j : ℕ} (hj : j < m) :
    coinBlock c j (List.ofFn (blocksEquiv m c F)) = List.ofFn (F ⟨j, hj⟩) := by
  apply List.ext_getElem?
  intro t
  simp only [coinBlock_eq, List.getElem?_take, List.getElem?_drop, List.getElem?_ofFn]
  by_cases ht : t < c
  · have hc : 0 < c := by omega
    have hlt : j * c + t < m * c := by
      calc j * c + t < j * c + c := by omega
        _ = (j + 1) * c := by ring
        _ ≤ m * c := Nat.mul_le_mul_right c hj
    simp only [ht, if_true, hlt, dif_pos, blocksEquiv_apply]
    congr 2
    · apply Fin.ext
      rw [Fin.coe_divNat]
      show (j * c + t) / c = j
      rw [show j * c + t = t + c * j by ring, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt ht, zero_add]
    · apply Fin.ext
      rw [Fin.coe_modNat]
      show (j * c + t) % c = t
      rw [show j * c + t = t + c * j by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  · simp [ht]

/-- The verifier's tape of the `|x|`-fold graph non-isomorphism protocol as the `|x|` bits and
the `|x|` sampler tapes of its coin blocks. -/
noncomputable def gniTapes (N : ℕ) :
    (Fin N → Bool) × (Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) ≃ gniProtocolRep.V.Coins N :=
  (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin (1 * (N + 1) ^ 2) → Bool)).symm.trans
    ((Equiv.piCongrRight fun _ => tapeSplit (1 * (N + 1) ^ 2)).trans
      ((blocksEquiv N (1 + 1 * (N + 1) ^ 2)).trans
        (Equiv.arrowCongr (finCongr (gniProtocolRep_V_coinLen N).symm) (Equiv.refl Bool))))

/-- The tape of `gniTapes` is the tape of blocks of the split blocks. -/
theorem gniTapes_apply (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) :
    List.ofFn (gniTapes N (b, ts)) =
      List.ofFn (blocksEquiv N (1 + 1 * (N + 1) ^ 2) (fun j => tapeSplit _ (b j, ts j))) := by
  unfold gniTapes
  exact (List.ofFn_congr (gniProtocolRep_V_coinLen N).symm
    (blocksEquiv N (1 + 1 * (N + 1) ^ 2) (fun j => tapeSplit _ (b j, ts j)))).symm

/-- Coin block `j < N` of the tape `gniTapes N (b, ts)` is `b_j` followed by the sampler tape
`ts_j`. -/
theorem coinSlice_gniTapes (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool))
    {j : ℕ} (hj : j < N) :
    coinBlock (1 + (N + 1) ^ 2) j (List.ofFn (gniTapes N (b, ts))) = b ⟨j, hj⟩ :: List.ofFn (ts ⟨j, hj⟩) := by
  rw [gniTapes_apply, show 1 + (N + 1) ^ 2 = 1 + 1 * (N + 1) ^ 2 by ring, coinSlice_blocksEquiv _ _ _ hj,
    ofFn_tapeSplit]

/-! ### Products of close samplers -/

/-- `m` independent copies of a sampler `δ`-close to uniform are `m δ`-close to uniform.

**Proof sketch.** Induction on `m` through `Fin.consEquiv`: the `m + 1` copies are one copy
and `m` copies (`StatClose.prod`), reassembled by `Fin.cons` (`StatClose.map`); the case `m = 0`
is the equality of two point masses. -/
theorem statClose_pi {σ γ : Type*} [Fintype σ] [Fintype γ] {X : σ → γ} {δ : ℝ}
    (h : StatClose X (id : γ → γ) δ) :
    ∀ m : ℕ, StatClose (fun ts : Fin m → σ => fun k => X (ts k)) (id : (Fin m → γ) → (Fin m → γ)) (m * δ)
  | 0 => by
    intro T
    have h1 : (fun ts : Fin 0 → σ => T (fun k => X (ts k))) = fun _ => T Fin.elim0 := by
      funext ts
      congr 1
      funext k
      exact k.elim0
    have h2 : (fun s : Fin 0 → γ => T (id s)) = fun _ => T Fin.elim0 := by
      funext s
      congr 1
      funext k
      exact k.elim0
    rw [h1, h2]
    simp only [Nat.cast_zero, zero_mul]
    rcases em (T Fin.elim0) with hT | hT
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | m + 1 => by
    have ih := statClose_pi h m
    have hp := (h.prod ih).map (fun q : γ × (Fin m → γ) => (Fin.cons q.1 q.2 : Fin (m + 1) → γ))
    have h1 := (hp.comp_equiv_left (Fin.consEquiv fun _ => σ).symm).comp_equiv_right
      (Fin.consEquiv fun _ => γ).symm
    intro T
    have := h1 T
    have e1 : ∀ ts : Fin (m + 1) → σ,
        (Fin.cons (X (ts 0)) (fun k => X (Fin.tail ts k)) : Fin (m + 1) → γ) = fun k => X (ts k) := by
      intro ts
      funext k
      cases k using Fin.cases with
      | zero => rfl
      | succ k => rfl
    have e2 : ∀ s : Fin (m + 1) → γ, (Fin.cons (s 0) (Fin.tail s) : Fin (m + 1) → γ) = s :=
      fun s => Fin.cons_self_tail s
    simp only [Fin.consEquiv_symm_apply, id_eq] at this
    simp only [e1, e2] at this
    rw [show ((m + 1 : ℕ) : ℝ) * δ = δ + m * δ by push_cast; ring]
    exact this

/-! ### Soundness of the `|x|`-fold protocol -/

/-- The sampler's coins fit in a block of the `|x|`-fold verifier's tape. -/
theorem permCoinLen_le_block {n : ℕ} (G₀ G₁ : Graph n) :
    permCoinLen n ≤ 1 * ((encInstance G₀ G₁).length + 1) ^ 2 :=
  permCoinLen_le_tape G₀ G₁

/-- The guess of a prover with fixed coins `r₁` in iteration `i`, as a function of the graphs
`H_0, …, H_i` received: the first bit of its reply (the `g_i` of `uprob_gni_rep_cheat`). -/
noncomputable def gGuess {n : ℕ} (P' : Strategy) (x y : List Bool) (r₁ : P'.Coins x.length)
    (i : Fin x.length) (Ks : Fin (i + 1) → Graph n) (_ : Unit) : Bool :=
  (P'.next x y (List.ofFn r₁) (List.ofFn fun k => encGraph (Ks k))).headD false

/-- **The acceptance bound of the `|x|`-fold graph non-isomorphism protocol against isomorphic
graphs** [PS10, proof of Proposition 118.4]: for `σ₀(G₀) = G₁` and every prover `P'`, the
verifier accepts with probability at most `2^{-|x|} + |x| · permFailBound n`.

**Proof sketch.** Fix the prover's coins (`Protocol.exists_proverCoins_le`); its `i`-th reply
is then a function `g_i` of the graphs `H_0, …, H_i` (`gGuess`). Read the verifier's tape as
the `|x|` pairs (bit, sampler coins) (`gniTapes`, `coinSlice_gniTapes`): the acceptance event is
`∀ i, g_i(σ_0(G_{b_0}), …, σ_i(G_{b_i})) = b_i` with `σ_j` sampled from block `j`. Replacing the
`|x|` sampled permutations by uniform ones costs `|x| · permFailBound n`
(`statClose_samplePerm_long`, `statClose_pi`, `StatClose.abs_uprob_sub_le_prod`), and for uniform
permutations the event has probability exactly `2^{-|x|}` (`uprob_gni_rep_cheat`). -/
theorem gniRep_accept_le {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (P' : Strategy) (y z : List Bool) :
    uprob (fun r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁) =>
      gniProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true]) ≤
      (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length + (encInstance G₀ G₁).length * permFailBound n := by
  obtain ⟨r₁, hr₁⟩ := gniProtocolRep.exists_proverCoins_le P' (encInstance G₀ G₁) y z (fun o => o = [true])
  refine hr₁.trans ?_
  -- the event on the verifier's tape, through the blocks
  have hev : ∀ p : (Fin (encInstance G₀ G₁).length → Bool) ×
      (Fin (encInstance G₀ G₁).length → (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool)),
      gniProtocolRep.outV P' (encInstance G₀ G₁) y z (r₁, gniTapes (encInstance G₀ G₁).length p) = [true] ↔
        ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i (prefixLE (fun j => permGraph (cond (p.1 j) G₁ G₀)
          (samplePerm n (List.ofFn (p.2 j)))) i) () = p.1 i := by
    rintro ⟨b, ts⟩
    rw [gniRep_outV_eq]
    simp only [List.cons.injEq, decide_eq_true_eq, and_true]
    refine forall_congr' fun i => ?_
    rw [coinSlice_gniTapes _ b ts i.isLt, List.headD_cons, gGuess,
      ofFn_eq_map_range (fun k : Fin (i + 1) => encGraph (prefixLE (fun j => permGraph (cond (b j) G₁ G₀)
        (samplePerm n (List.ofFn (ts j)))) i k)) (gniGraphs G₀ G₁ (List.ofFn (gniTapes _ (b, ts))))
        (fun t => by
          rw [gniGraphs, coinSlice_gniTapes _ b ts (by omega : (t : ℕ) < (encInstance G₀ G₁).length),
            List.headD_cons, List.drop_one, List.tail_cons]
          rfl)]
  rw [← uprob_comp_equiv (gniTapes (encInstance G₀ G₁).length), OneWay.uprob_congr hev,
    ← uprob_comp_equiv (Equiv.prodComm (Fin (encInstance G₀ G₁).length →
      (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool)) (Fin (encInstance G₀ G₁).length → Bool))]
  have hclose := (statClose_pi (statClose_samplePerm_long (permCoinLen_le_block G₀ G₁))
    (encInstance G₀ G₁).length).abs_uprob_sub_le_prod
    fun (σs : Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n))
      (b : Fin (encInstance G₀ G₁).length → Bool) => ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i
        (prefixLE (fun j => permGraph (cond (b j) G₁ G₀) (σs j)) i) () = b i
  have hideal : uprob (fun q : (Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n)) ×
      (Fin (encInstance G₀ G₁).length → Bool) =>
      ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i
        (prefixLE (fun j => permGraph (cond (q.2 j) G₁ G₀) (id q.1 j)) i) () = q.2 i) =
        (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length := by
    rw [← uprob_comp_equiv ((Equiv.prodPUnit ((Fin (encInstance G₀ G₁).length → Bool) ×
      (Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n)))).trans (Equiv.prodComm _ _))]
    exact uprob_gni_rep_cheat hσ (gGuess P' (encInstance G₀ G₁) y r₁)
  rw [hideal] at hclose
  have h2 := (abs_le.1 hclose).2
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at h2 ⊢
  linarith

/-- **The `|x|`-fold graph non-isomorphism protocol is an interactive proof for `L_niso` with
soundness error `2^{-|x|} + |x| · permFailBound n`** [PS10, Proposition 118.4] (Prop-118.4),
given the verifier's efficiency.

**Proof sketch.** Completeness is `gniRep_complete` with the empty auxiliary input. Soundness:
a well-formed `x ∉ L_niso` is `encInstance G₀ G₁` with `G₀ ≅ G₁` (`eq_encInstance_of_wellFormed`,
`encInstance_mem_Lniso_iff`), and `gniRep_accept_le` bounds the acceptance probability, the
verdict being a single bit (`gniRep_outV_eq`, `uprob_not`); a malformed `x` is rejected on every
tape (`gniVerifierRep_next_ge`, `exec_vfirst_length`). -/
theorem gni_interactiveProofErrRep (hV : gniVerifierRep.Efficient) :
    InteractiveProofErr gniProtocolRep Lniso
      (fun N => (2 : ℝ)⁻¹ ^ N + N * permFailBound (instanceVertices N)) where
  efficientV := hV
  complete := by
    refine ⟨.const 1, ?_⟩
    rintro x ⟨n, G₀, G₁, rfl, hni⟩
    exact ⟨[], gniProver_length_le _ [], fun z => gniRep_complete hni [] z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      obtain ⟨σ₀, hσ⟩ : Isomorphic G₀ G₁ := by
        by_contra hni
        exact hx ((encInstance_mem_Lniso_iff G₀ G₁).2 hni)
      have hacc := gniRep_accept_le hσ P' [] z
      have hnot : ∀ r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁),
          gniProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ gniProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gniRep_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not, instanceVertices_length_encInstance]
      linarith
    · have hall : ∀ r : gniProtocolRep.ExecCoins P' x, gniProtocolRep.outV P' x [] z r = [false] := by
        intro r
        rw [gniProtocolRep_outV, gniVerifierRep_next_ge _ _ _ _
          (exec_vfirst_length P' gniVerifierRep x [] z (List.ofFn r.1) (List.ofFn r.2) x.length).2.ge]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      have h1 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
      have h2 : (0 : ℝ) ≤ x.length * permFailBound (instanceVertices x.length) :=
        mul_nonneg (Nat.cast_nonneg _) (permFailBound_nonneg _)
      linarith

/-- **[PS10, Proposition 118.4]:** the `|x|`-fold graph non-isomorphism protocol is an
interactive proof for `L_niso`, given the verifier's efficiency: the soundness error
`2^{-N} + N · permFailBound (instanceVertices N)` of `gni_interactiveProofErrRep` is
negligible (`negligible_two_pow_neg`, `negligible_mul_permFailBound`). -/
theorem gni_interactiveProof (hV : gniVerifierRep.Efficient) : InteractiveProof gniProtocolRep Lniso :=
  (gni_interactiveProofErrRep hV).interactiveProof (negligible_two_pow_neg.add negligible_mul_permFailBound)

end TCSlib.Cryptography.GI
