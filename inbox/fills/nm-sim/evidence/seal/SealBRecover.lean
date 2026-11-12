/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The NM distinguisher of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message). The NM
experiment hands its distinguisher the decryptions of the NM adversary's ciphertexts (`⊥` on a copy
of the challenge). The distinguisher `recDist S D` reads back the SIM experiment's view
`(a, m, (d_i)_i, σ)` from them and runs `D` on it:
* each of `A`'s ciphertexts comes with the encoding of its copy flag: the entry `d_i` is `COPY` if
  the flag is set, and the decryption otherwise (`entF`);
* each bit `x` of `a`, `m`, `σ` is encoded by `Enc_pk(x^{msgLen})`, `Enc_pk((¬x)^{msgLen})`; by
  correctness at most one of them is the challenge, and `guessBit` reads `x` from the two
  decryptions (`guessBit_encPair`).

## Main definitions

* `NMSim.entF`, `NMSim.bitG`, `NMSim.recView`: the reading of the view.
* `NMSim.recDist`: the distinguisher.

## Main results

* `NMSim.recDist_distinguisherL`, `NMSim.nmOutput_flatten`, `NMSim.guessBit_encPair`,
  `NMSim.recView_nmOutL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal B of the nm-sim fill: a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Recover.lean`, with every seal candidate of
its full TCSlib import closure (1360 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acEnc _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHyb _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acSeedTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acStLen _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl_adaptiveIndImpl.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.expect_tapeImpl.match_1_4 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.extTape _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.simulate_tapeImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.tapeImpl _root_.TCSlib.Cryptography.Composability.Attack.ofNat _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_some_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.length_of_firstQ_eq_some.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.recAdvIn _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDin _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDin.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDout _root_.TCSlib.Cryptography.Composability.ChallengeSim.recHandler _root_.TCSlib.Cryptography.Composability.ChallengeSim.recOut _root_.TCSlib.Cryptography.Composability.ChallengeSim.recRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.simulate_recHandler_init.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.simulate_recHandler_recorded.match_1_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.NMSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmDecrypt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmOutput _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nthCt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.ofPadded _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.NMCCA2.ansRead _root_.TCSlib.Cryptography.Composability.NMCCA2.cntRead _root_.TCSlib.Cryptography.Composability.NMCCA2.decBlock _root_.TCSlib.Cryptography.Composability.NMCCA2.decHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encCt _root_.TCSlib.Cryptography.Composability.NMCCA2.encHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encTape _root_.TCSlib.Cryptography.Composability.NMCCA2.finA _root_.TCSlib.Cryptography.Composability.NMCCA2.finL _root_.TCSlib.Cryptography.Composability.NMCCA2.finU _root_.TCSlib.Cryptography.Composability.NMCCA2.finW _root_.TCSlib.Cryptography.Composability.NMCCA2.finZ _root_.TCSlib.Cryptography.Composability.NMCCA2.fwdHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.guessBit _root_.TCSlib.Cryptography.Composability.NMCCA2.guessDist _root_.TCSlib.Cryptography.Composability.NMCCA2.indImpl_eq_of_msgLen_eq_zero.match_1_1 _root_.TCSlib.Cryptography.Composability.NMCCA2.logEmit _root_.TCSlib.Cryptography.Composability.NMSim.altMsg _root_.TCSlib.Cryptography.Composability.NMSim.bitF _root_.TCSlib.Cryptography.Composability.NMSim.castImpl_indImpl_abs.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.chalHandler _root_.TCSlib.Cryptography.Composability.NMSim.chalHandler_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.chalHandler_costBoundedBy.match_1_3 _root_.TCSlib.Cryptography.Composability.NMSim.chalRun _root_.TCSlib.Cryptography.Composability.NMSim.chalState _root_.TCSlib.Cryptography.Composability.NMSim.chalState.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.chunkAt _root_.TCSlib.Cryptography.Composability.NMSim.chunkEmit _root_.TCSlib.Cryptography.Composability.NMSim.chunkMap _root_.TCSlib.Cryptography.Composability.NMSim.chunkStep _root_.TCSlib.Cryptography.Composability.NMSim.copyHandler _root_.TCSlib.Cryptography.Composability.NMSim.ctxSt _root_.TCSlib.Cryptography.Composability.NMSim.drawWith _root_.TCSlib.Cryptography.Composability.NMSim.encBit _root_.TCSlib.Cryptography.Composability.NMSim.encF _root_.TCSlib.Cryptography.Composability.NMSim.encPair _root_.TCSlib.Cryptography.Composability.NMSim.encWith _root_.TCSlib.Cryptography.Composability.NMSim.entryL _root_.TCSlib.Cryptography.Composability.NMSim.entryTails _root_.TCSlib.Cryptography.Composability.NMSim.expect_simulate_rImpl_eager.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.finMsg _root_.TCSlib.Cryptography.Composability.NMSim.finSt _root_.TCSlib.Cryptography.Composability.NMSim.flagF _root_.TCSlib.Cryptography.Composability.NMSim.halfCoins _root_.TCSlib.Cryptography.Composability.NMSim.halfDist _root_.TCSlib.Cryptography.Composability.NMSim.halfSamp _root_.TCSlib.Cryptography.Composability.NMSim.histImpl _root_.TCSlib.Cryptography.Composability.NMSim.histWith _root_.TCSlib.Cryptography.Composability.NMSim.hybAcc _root_.TCSlib.Cryptography.Composability.NMSim.idealAcc _root_.TCSlib.Cryptography.Composability.NMSim.idealView _root_.TCSlib.Cryptography.Composability.NMSim.nmAbs _root_.TCSlib.Cryptography.Composability.NMSim.nmAbs.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.nmComp_abs.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.nmFin _root_.TCSlib.Cryptography.Composability.NMSim.nmLen _root_.TCSlib.Cryptography.Composability.NMSim.nmOutL _root_.TCSlib.Cryptography.Composability.NMSim.nmPair _root_.TCSlib.Cryptography.Composability.NMSim.nmParams _root_.TCSlib.Cryptography.Composability.NMSim.nmSeed _root_.TCSlib.Cryptography.Composability.NMSim.rImpl _root_.TCSlib.Cryptography.Composability.NMSim.rImpl.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl.match_3 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_allOutputs_isSome.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_eq_of_msgLen_eq_zero.match_1_2 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_false_coins.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.rdAns _root_.TCSlib.Cryptography.Composability.NMSim.rdIdx _root_.TCSlib.Cryptography.Composability.NMSim.rdLog _root_.TCSlib.Cryptography.Composability.NMSim.rdQuery _root_.TCSlib.Cryptography.Composability.NMSim.rdState _root_.TCSlib.Cryptography.Composability.NMSim.rdU _root_.TCSlib.Cryptography.Composability.NMSim.rdW _root_.TCSlib.Cryptography.Composability.NMSim.rdZ _root_.TCSlib.Cryptography.Composability.NMSim.realAcc _root_.TCSlib.Cryptography.Composability.NMSim.realView _root_.TCSlib.Cryptography.Composability.NMSim.seedEquiv _root_.TCSlib.Cryptography.Composability.NMSim.seedEquivPoly _root_.TCSlib.Cryptography.Composability.NMSim.simAbs _root_.TCSlib.Cryptography.Composability.NMSim.simAbs.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.simComp_abs.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.simCt _root_.TCSlib.Cryptography.Composability.NMSim.simFin _root_.TCSlib.Cryptography.Composability.NMSim.simMsg _root_.TCSlib.Cryptography.Composability.NMSim.simOutL _root_.TCSlib.Cryptography.Composability.NMSim.simParams _root_.TCSlib.Cryptography.Composability.NMSim.snmDin _root_.TCSlib.Cryptography.Composability.NMSim.snmDin.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.snmDin_eval_inLens.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.snmDout _root_.TCSlib.Cryptography.Composability.NMSim.snmDout_eval_outLens.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.stParam _root_.TCSlib.Cryptography.Composability.NMSim.tailDist _root_.TCSlib.Cryptography.Composability.isPadded _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Composability.padDecFun _root_.TCSlib.Cryptography.Composability.padEncFun _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GGMRed.IsQ _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.advPoly _root_.TCSlib.Cryptography.GGMRed.adviceOf _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.ansMap _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinPoly _root_.TCSlib.Cryptography.GGMRed.coinStr _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.concrete _root_.TCSlib.Cryptography.GGMRed.concrete_iterate.match_1_1 _root_.TCSlib.Cryptography.GGMRed.encState _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.firstRound _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.nextQ _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.orbit_eq_encState.match_1_1 _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.prefMap _root_.TCSlib.Cryptography.GGMRed.pureAt _root_.TCSlib.Cryptography.GGMRed.pureStep _root_.TCSlib.Cryptography.GGMRed.pureStep.match_1 _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rawInput _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.stream _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.valStr _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.IInv _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom.match_1 _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.gB _root_.TCSlib.Cryptography.Games.EffFill.gC _root_.TCSlib.Cryptography.Games.EffFill.gCur _root_.TCSlib.Cryptography.Games.EffFill.gLc _root_.TCSlib.Cryptography.Games.EffFill.gLin _root_.TCSlib.Cryptography.Games.EffFill.gO _root_.TCSlib.Cryptography.Games.EffFill.gPh _root_.TCSlib.Cryptography.Games.EffFill.gS _root_.TCSlib.Cryptography.Games.EffFill.hAct _root_.TCSlib.Cryptography.Games.EffFill.hBound _root_.TCSlib.Cryptography.Games.EffFill.hCtx _root_.TCSlib.Cryptography.Games.EffFill.hMove _root_.TCSlib.Cryptography.Games.EffFill.hNext _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.hRes _root_.TCSlib.Cryptography.Games.EffFill.hRounds _root_.TCSlib.Cryptography.Games.EffFill.hStart _root_.TCSlib.Cryptography.Games.EffFill.hState _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iAnsLen _root_.TCSlib.Cryptography.Games.EffFill.iAsk _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallAct _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCallNext _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinAct _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinNext _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iFixBound _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iNext _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iTree _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_le_length_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.relabel _root_.TCSlib.Cryptography.Games.EffFill.relabelEmit _root_.TCSlib.Cryptography.Games.EffFill.relabelN _root_.TCSlib.Cryptography.Games.EffFill.relabelN_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.answer.match_1 _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.buildComp_singleCodec.match_1_1 _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.singleCodec _root_.TCSlib.Cryptography.Games.singleCodec.match_1 _root_.TCSlib.Cryptography.Games.toHist _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PublicKeyScheme.Secure _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.PublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_prf_of_exists_prg.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmPRF _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.hybridAdv _root_.TCSlib.Cryptography.hybridCoins _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridPlant _root_.TCSlib.Cryptography.hybridPre _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.length_flatten_ofFn.match_1_1 _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multiDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.singleDist _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs

open NMCCA2 (guessBit guessBit_eq guessBit_valid guessBit_refused)

variable (S : FixedLengthPKScheme)

/-! ### Reading the view -/

/-- `guessBit` is polynomial-time (DL-30–36 overlap: the content of the private
`polyTimeComputable_guessFun` of `Indistinguishability/Encrypt.lean`, on the bare string). -/
theorem polyTimeComputable_guessBit : PolyTimeComputable fun w => [guessBit w] :=
  (polyTimeComputable_ite polyTimeComputable_headD
    (polyTimeComputable_headD.comp polyTimeComputable_tail)
    (polyTimeComputable_not
      (polyTimeComputable_headD.comp BinArith.polyTimeComputable_reverse))).congr fun w => by
    rw [guessBit_eq]
    split <;> rfl

/-- **An entry read back** from the decryptions `v ‖ v₁ ‖ v₂` (`msgLen(n) + 1` bits each) of a
ciphertext and the encoding of its copy flag, on the context `⟨1^n, _⟩`: `COPY` if `guessBit (v₁ ‖ v₂)`,
and `false` followed by `v` otherwise. -/
def entF (ctx ch : List Bool) : List Bool :=
  if guessBit (ch.drop ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)) then
    true :: List.replicate ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) false
  else false :: ch.take ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)

/-- `entF S ctx ch = if guessBit (ch.drop (msgLen + 1)) then COPY else false :: ch.take (msgLen + 1)`. -/
theorem entF_eq (ctx ch : List Bool) :
    entF S ctx ch =
      if guessBit (ch.drop ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)) then
        true :: List.replicate ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) false
      else false :: ch.take ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) := rfl

/-- **A bit read back** from the decryptions of its encoding: `[guessBit ch]`. -/
def bitG (_ctx ch : List Bool) : List Bool := [guessBit ch]

/-- `bitG ctx ch = [guessBit ch]`. -/
theorem bitG_eq (ctx ch : List Bool) : bitG ctx ch = [guessBit ch] := rfl

/-- `entF` is polynomial-time, as a function of `⟨ctx, ch⟩`. -/
theorem polyTimeComputable_entF : PolyTimeComputable fun z => entF S (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : PolyTimeComputable fun z => pairEncode (pairFstD (pairFstD z)) (pairSndD z) :=
    (hF.comp hF).pairEncode hD
  have hdrop : PolyTimeComputable fun z =>
      (pairSndD z).drop ((S.msgLen.add (.const 1)).eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairDropPoly (S.msgLen.add (.const 1))).comp hcut).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have htake : PolyTimeComputable fun z =>
      (pairSndD z).take ((S.msgLen.add (.const 1)).eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly (S.msgLen.add (.const 1))).comp hcut).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact polyTimeComputable_ite (polyTimeComputable_guessBit.comp hdrop)
    (BinArith.polyTimeComputable_cons (polyTimeComputable_const [true])
      (EnsembleLemmas.polyTimeComputable_zeros (S.msgLen.add (.const 1)) (hF.comp hF)))
    (BinArith.polyTimeComputable_cons (polyTimeComputable_const [false]) htake)

/-- `bitG` is polynomial-time, as a function of `⟨ctx, ch⟩`. -/
theorem polyTimeComputable_bitG : PolyTimeComputable fun z => bitG (pairFstD z) (pairSndD z) :=
  polyTimeComputable_guessBit.comp polyTimeComputable_pairSndD

variable (pl : PolyExpr) (r sl : PolyExpr)

/-- **The view read back** on the parameter string `U = 1^n` from the decryptions `u`: the entries
`E` (`chunkMap` of `entF` over the first `r` groups of three decryptions) and the bits `B` (`chunkMap`
of `bitG` over the remaining pairs); the view is `B.take pl ‖ (B.drop pl).take msgLen ‖ E ‖
B.drop (pl + msgLen)`. -/
def recView (U u : List Bool) : List Bool :=
  (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).take
      (pl.eval U.length) ++
    ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).drop
      (pl.eval U.length)).take (S.msgLen.eval U.length) ++
    chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
      (pairEncode (pairEncode U [])
        (u.take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length))) ++
    (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).drop
      ((pl.add S.msgLen).eval U.length)

/-- `recView S pl r U u = B.take pl ++ (B.drop pl).take msgLen ++ E ++ B.drop (pl + msgLen)`. -/
theorem recView_eq (U u : List Bool) :
    recView S pl r U u =
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).take (pl.eval U.length) ++
        ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).drop (pl.eval U.length)).take (S.msgLen.eval U.length) ++
        chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
          (pairEncode (pairEncode U [])
            (u.take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length))) ++
        (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).drop ((pl.add S.msgLen).eval U.length) := rfl

/-- The reading of the view is polynomial-time, as a function of `⟨U, u⟩`. -/
theorem polyTimeComputable_recView :
    PolyTimeComputable fun z => recView S pl r (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : ∀ p : PolyExpr, PolyTimeComputable (fun z => (pairSndD z).take (p.eval (pairFstD z).length)) ∧
      PolyTimeComputable (fun z => (pairSndD z).drop (p.eval (pairFstD z).length)) := fun p =>
    ⟨polyTimeComputable_pairTakePoly p, polyTimeComputable_pairDropPoly p⟩
  have hctx : PolyTimeComputable fun z => pairEncode (pairFstD z) ([] : List Bool) :=
    hF.pairEncode (polyTimeComputable_const [])
  have hB : PolyTimeComputable fun z =>
      chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))) :=
    (polyTimeComputable_chunkMap _ polyTimeComputable_bitG).comp
      (hctx.pairEncode (hcut _).2)
  have hE : PolyTimeComputable fun z =>
      chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))) :=
    (polyTimeComputable_chunkMap _ (polyTimeComputable_entF S)).comp
      (hctx.pairEncode (hcut _).1)
  have hBU : ∀ p : PolyExpr, PolyTimeComputable (fun z => pairEncode (pairFstD z)
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))))) := fun _ => hF.pairEncode hB
  have h1 : PolyTimeComputable fun z => (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).take (pl.eval (pairFstD z).length) :=
    ((hcut pl).1.comp (hBU pl)).congr fun z => by
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h2a : PolyTimeComputable fun z => (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop (pl.eval (pairFstD z).length) :=
    ((hcut pl).2.comp (hBU pl)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h2 : PolyTimeComputable fun z =>
      ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop (pl.eval (pairFstD z).length)).take
        (S.msgLen.eval (pairFstD z).length) :=
    ((hcut S.msgLen).1.comp (hF.pairEncode h2a)).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h3 : PolyTimeComputable fun z => (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop ((pl.add S.msgLen).eval (pairFstD z).length) :=
    ((hcut (pl.add S.msgLen)).2.comp (hBU pl)).congr fun z => by
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact (((h1.append h2).append hE).append h3).congr fun z => by rw [recView_eq]

variable (D : NUPPT)

/-- `recDist`'s raw function on `⟨⟨⟨1^n, u⟩, α⟩, ρ⟩`: `D`'s output (advice `α`, coins `ρ`) on the
view read back from `u`. -/
private def recFun (z : List Bool) : List Bool :=
  D.output (NUPPT.layout (NUPPT.inParam z) (recView S pl r (NUPPT.inParam z) (NUPPT.inArg z))
    (NUPPT.inAdvice z) (NUPPT.inCoins z))

/-- The raw function is polynomial-time. -/
private theorem polyTimeComputable_recFun : PolyTimeComputable (recFun S pl r D) :=
  D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_recView S pl r).comp (NUPPT.polyTimeComputable_inParam.pairEncode
      NUPPT.polyTimeComputable_inArg) |>.congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
    NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)

/-- **The NM distinguisher** built from `D`, with `D`'s coins and advice: it reads the SIM view back
from the decryptions (`recView`) and runs `D` on it. -/
noncomputable def recDist : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_recFun S pl r D) D.coins D.adv D.advice D.advice_length

/-- The NM distinguisher has `D`'s coins. -/
theorem recDist_coins : (recDist S pl r D).coins = D.coins := by
  rw [recDist, NUPPT.coins_ofPolyTime]

/-- **The NM distinguisher's verdict** on the decryptions `u`, with `D`'s coins `rD` carried over,
is `D`'s verdict on the view read back: `recDist.distinguisherL n u rD = D.distinguisherL n
(recView 1^n u) rD`. -/
theorem recDist_distinguisherL (n : ℕ) (u : List Bool) (rD : D.Coins n) :
    (recDist S pl r D).distinguisherL n u (NUPPT.coinsCongr (recDist_coins S pl r D).symm n rD) =
      D.distinguisherL n (recView S pl r (List.replicate n true) u) rD := by
  have hlay : pairEncode (pairEncode (NUPPT.advInput n u) (D.advice n)) (List.ofFn rD) =
      NUPPT.layout (List.replicate n true) u (D.advice n) (List.ofFn rD) := by
    rw [NUPPT.layout_eq, NUPPT.advInput_eq]
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_coinsCongr, recDist, NUPPT.runAtL_ofPolyTime, recFun,
    hlay]
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.inCoins_layout]
  rw [← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]

/-! ### The view is read back -/

/-- **The decryptions of concatenated ciphertexts:** for `ℓ` ciphertexts `cs` of `ctLen(n)` bits,
`nmOutput sk s' (padFin _ cs.flatten)` is the concatenation of the entries' tails
`(entryL … [c is the challenge] c).drop 1` (`nmOutput_eq_entryTails`, `map_chunkAt_flatten`). -/
theorem nmOutput_flatten (n ℓ : ℕ) (sk : List Bool) (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (cs : List (List Bool)) (hℓ : cs.length = ℓ) (hc : ∀ c ∈ cs, c.length = S.ctLen.eval n) :
    S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) cs.flatten) =
      (cs.map fun c => (entryL S n sk (decide (s'.map List.ofFn = some c)) c).drop 1).flatten := by
  have hlen : cs.flatten.length = ℓ * S.ctLen.eval n := by
    rw [List.length_flatten, ← hℓ]
    have : cs.map List.length = cs.map fun _ => S.ctLen.eval n := List.map_congr_left hc
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [nmOutput_eq_entryTails S n ℓ sk s' _ hlen, ← hℓ,
    map_chunkAt_flatten (S.ctLen.eval n) (fun c => (entryL S n sk
      (decide (s'.map List.ofFn = some c)) c).drop 1) cs hc]

variable (samp : NUPPT)

/-- **The ciphertexts are not empty** when the messages are not: with `msgLen(n) > 0`, correctness
gives `ctLen(n) > 0` (two different messages cannot both decrypt from the empty ciphertext). -/
theorem ctLen_pos (n : ℕ) (rg : S.gen.Coins n) (re : S.enc.Coins n) (hL : 0 < S.msgLen.eval n) :
    0 < S.ctLen.eval n := by
  by_contra h
  have h0 : S.ctLen.eval n = 0 := by omega
  have hnil : ∀ m : Fin (S.msgLen.eval n) → Bool,
      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re = [] := fun m =>
    List.eq_nil_of_length_eq_zero ((S.enc_length n rg m re).trans h0)
  have h₁ := S.correct n (fun _ => true) rg re
  have h₂ := S.correct n (fun _ => false) rg re
  rw [hnil] at h₁ h₂
  have := congrFun (Option.some.inj (h₁.symm.trans h₂)) ⟨0, hL⟩
  exact absurd this (by decide)

/-- **The encoding of a bit is read back** from its decryptions: under generated keys, with
`msgLen(n) > 0`, for the context `⟨1^n, ⟨z, ⟨ω, st⟩⟩⟩` with `pk = fst z` and the tape `re` after
`2·coins(n)` bits of `ω`, `guessBit (v(Enc_pk(x^{msgLen})) ‖ v(Enc_pk((¬x)^{msgLen}))) = x`, where
`v c` is the decryption of `c` in the NM output (`⊥` on the challenge `s'`).

**Proof sketch.** The two ciphertexts decrypt to `x^{msgLen}` and `(¬x)^{msgLen}` (correctness), so
they differ and at most one is the challenge: `guessBit_valid` or `guessBit_refused`. -/
theorem guessBit_encPair (n : ℕ) (rg : S.gen.Coins n) (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (hL : 0 < S.msgLen.eval n) (z ω st : List Bool) (hz : pairFstD z = pairFstD (S.gen.runAt n [] rg))
    (re : S.enc.Coins n) (hω : ω.drop ((samp.coins.add samp.coins).eval n) = List.ofFn re)
    (x : Bool) :
    guessBit ((entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (encBit S samp
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) x)))
        (encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) x)).drop 1 ++
      (entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (encBit S samp
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) (!x))))
        (encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
          (!x))).drop 1) = x := by
  have henc : ∀ y, encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
      y = S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => y)) re := by
    intro y
    rw [encBit_eq, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
      pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, hω, hz, List.ofFn_const,
      EnsembleLemmas.padL_eq, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq]
    refine List.take_left' ?_
    have := S.enc_length n rg (fun _ => y) re
    rw [NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq, List.ofFn_const] at this
    exact this
  have hdec : ∀ y, decodeFin (S.msgLen.eval n) (S.dec (pairEncode (pairSndD (S.gen.runAt n [] rg))
      (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => y)) re))) = some fun _ => y :=
    fun y => S.correct n _ rg re
  have hne : S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
      (List.ofFn fun _ : Fin (S.msgLen.eval n) => x)) re ≠
      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => !x)) re := by
    intro heq
    have h₁ := hdec x
    rw [heq, hdec (!x)] at h₁
    have := congrFun (Option.some.inj h₁) ⟨0, hL⟩
    cases x <;> exact absurd this (by decide)
  rw [henc, henc, entryL_drop_one, entryL_drop_one, hdec, hdec]
  by_cases h : s'.map List.ofFn = some (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
    (List.ofFn fun _ : Fin (S.msgLen.eval n) => x)) re)
  · have h' : ¬ s'.map List.ofFn = some (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => !x)) re) := by
      rw [h]
      exact fun h'' => hne (Option.some.inj h'')
    rw [if_pos (decide_eq_true h), if_neg (by simpa using h'), ← ofFn_zeroBits]
    exact guessBit_refused hL x
  · rw [if_neg (by simpa using h)]
    exact guessBit_valid hL x _

/-- **The view is read back from the NM output** (under generated keys, `msgLen(n) > 0`): for the
NM adversary's output on the context `⟨1^n, ⟨z, ⟨ω, st⟩⟩⟩` (`A`'s output `a`, the parameter `aP`,
the message `mP`), whose copy flags agree with the challenge `s'` (`hflag`), `recView` of the
decryptions is `aP ‖ mP ‖ (d_i)_i ‖ σ` with `d_i = entryL … [c_i is the challenge] c_i`.

**Proof sketch.** The output is a concatenation of `ctLen(n)`-bit ciphertexts
(`nmOutput_flatten`): for each `c_i`, its decryption and those of its flag's encoding; for each bit
of `aP ‖ mP ‖ σ`, the decryptions of its encoding. `entF` turns each group of three into `d_i`
(`guessBit_encPair`, `hflag`) and `bitG` each pair into its bit (`chunkMap_flatten`). -/
theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
    (s' : Option (Fin (S.ctLen.eval n) → Bool)) (z ω st a aP mP : List Bool)
    (hz : pairFstD z = pairFstD (S.gen.runAt n [] rg)) (re : S.enc.Coins n)
    (hω : ω.drop ((samp.coins.add samp.coins).eval n) = List.ofFn re)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) (haP : aP.length = pl.eval n)
    (hmP : mP.length = S.msgLen.eval n)
    (hflag : ∀ c : List Bool, (st.headD false && decide (c = (st.drop 1).take (S.ctLen.eval n))) =
      decide (s'.map List.ofFn = some c)) :
    recView S pl r (List.replicate n true) (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) s'
        (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (nmOutL S samp r n
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) a aP mP))) =
      aP ++ mP ++ ((List.range (r.eval n)).map fun i => entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)))
        (chunkAt (S.ctLen.eval n) i a)).flatten ++ a.drop (r.eval n * S.ctLen.eval n) := by
  set sk := pairSndD (S.gen.runAt n [] rg) with hsk
  set ctx := pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)) with hctx
  set v : List Bool → List Bool := fun c =>
    (entryL S n sk (decide (s'.map List.ofFn = some c)) c).drop 1 with hvdef
  set f : ℕ → Bool := fun i => st.headD false &&
    decide (chunkAt (S.ctLen.eval n) i a = (st.drop 1).take (S.ctLen.eval n)) with hfdef
  set bits := aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n) with hbits
  have hct := ctLen_pos S n rg re hL
  have hci : ∀ i < r.eval n, (chunkAt (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
    length_chunkAt _ _ _ (by
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega)
  have hv : ∀ c, (v c).length = S.msgLen.eval n + 1 := fun c => by
    rw [hvdef, List.length_drop, length_entryL]
    omega
  have he : ∀ x, (encBit S samp ctx x).length = S.ctLen.eval n := fun x => length_encBit S samp n _ x
  set cs : List (List Bool) := ((List.range (r.eval n)).map fun i =>
      [chunkAt (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)]).flatten ++
    (bits.map fun x => [encBit S samp ctx x, encBit S samp ctx (!x)]).flatten with hcs
  have hW : nmOutL S samp r n ctx a aP mP = cs.flatten := by
    rw [nmOutL_eq, hcs, List.flatten_append, List.flatten_flatten, List.flatten_flatten,
      List.map_map, List.map_map]
    refine congrArg₂ (· ++ ·) (congrArg List.flatten ?_) (congrArg List.flatten ?_)
    · refine List.map_congr_left fun i _ => ?_
      rw [Function.comp_apply, encF_eq, encPair_eq, ctxSt_eq, hctx]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.flatten_cons,
        List.flatten_nil, List.append_nil, hfdef]
    · refine List.map_congr_left fun x _ => ?_
      rw [Function.comp_apply, encPair_eq]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  have hcs_len : cs.length = (nmLen S pl r sl).eval n := by
    rw [hcs, List.length_append, List.length_flatten, List.length_flatten, List.map_map,
      List.map_map]
    have h3 : (List.map (List.length ∘ fun i =>
        [chunkAt (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)])
        (List.range (r.eval n))) = List.replicate (r.eval n) 3 := by
      rw [List.eq_replicate_iff, List.length_map, List.length_range]
      refine ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      rfl
    have h2 : (List.map (List.length ∘ fun x => [encBit S samp ctx x, encBit S samp ctx (!x)])
        bits) = List.replicate bits.length 2 := by
      rw [List.eq_replicate_iff, List.length_map]
      refine ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      rfl
    rw [h3, h2, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul, nmLen_eval, hbits,
      List.length_append, List.length_append, List.length_drop, haP, hmP, ha]
    omega
  have hcs_ct : ∀ c ∈ cs, c.length = S.ctLen.eval n := by
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      rw [List.mem_range] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · exact hci i hi
      · exact he _
      · exact he _
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 h
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact he _
      · exact he _
  rw [hW, nmOutput_flatten S n _ sk s' cs hcs_len hcs_ct]
  have hP : (cs.map v).flatten =
      ((List.range (r.eval n)).map fun i => v (chunkAt (S.ctLen.eval n) i a) ++
        (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten ++
      (bits.map fun x => v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x))).flatten := by
    rw [hcs, List.map_append, List.flatten_append, List.map_flatten, List.map_flatten,
      List.flatten_flatten, List.flatten_flatten, List.map_map, List.map_map, List.map_map,
      List.map_map]
    refine congrArg₂ (· ++ ·) (congrArg List.flatten ?_) (congrArg List.flatten ?_)
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
    · refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
  have h3 : ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))).eval n =
      3 * (S.msgLen.eval n + 1) := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]
  have h2 : ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))).eval n =
      2 * (S.msgLen.eval n + 1) := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]
  have h1 : (S.msgLen.add (.const 1)).eval n = S.msgLen.eval n + 1 := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  have hg3 : ∀ i < r.eval n, (v (chunkAt (S.ctLen.eval n) i a) ++
      (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).length =
      ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))).eval n := fun i _ => by
    rw [List.length_append, List.length_append, hv, hv, hv, h3]
    ring
  have hP1 : (((List.range (r.eval n)).map fun i => v (chunkAt (S.ctLen.eval n) i a) ++
      (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten).length =
      (r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval n := by
    rw [length_flatten_map_range _ _ _ hg3]
    exact (PolyExpr.eval_mul _ _ _).symm
  rw [hP, recView_eq, List.length_replicate, List.take_left' hP1, List.drop_left' hP1,
    chunkMap_flatten _ _ n [] _ (fun ch hch => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hch
      rw [List.length_append, hv, hv, h2]
      ring) (by rw [h2]; omega),
    chunkMap_flatten _ _ n [] _ (fun ch hch => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
      exact hg3 i (List.mem_range.1 hi)) (by rw [h3]; omega), List.map_map, List.map_map]
  have hB : (bits.map (bitG (pairEncode (List.replicate n true) []) ∘ fun x =>
      v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x)))).flatten = bits := by
    have hx : ∀ x, (bitG (pairEncode (List.replicate n true) []) ∘ fun x =>
        v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x))) x = [x] := by
      intro x
      rw [Function.comp_apply, bitG_eq, hvdef]
      exact congrArg (· :: []) (guessBit_encPair S samp n rg s' hL z ω st hz re hω x)
    have hfl : ∀ l : List Bool, (l.map fun x => [x]).flatten = l := by
      intro l
      induction l with
      | nil => rfl
      | cons x t ih => rw [List.map_cons, List.flatten_cons, ih]; rfl
    rw [List.map_congr_left (fun x _ => hx x), hfl]
  have hE : (List.range (r.eval n)).map (entF S (pairEncode (List.replicate n true) []) ∘ fun i =>
      v (chunkAt (S.ctLen.eval n) i a) ++
        (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))) =
      (List.range (r.eval n)).map fun i => entryL S n sk
        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)))
        (chunkAt (S.ctLen.eval n) i a) := by
    refine List.map_congr_left fun i _ => ?_
    have hg : guessBit (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i))) = f i := by
      rw [hvdef]
      exact guessBit_encPair S samp n rg s' hL z ω st hz re hω (f i)
    have hf : f i = decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)) := hflag _
    rw [Function.comp_apply, entF_eq, pairFstD_pairEncode, List.length_replicate, h1,
      List.drop_left' (hv _), List.take_left' (hv _), hg, hf, entryL_eq]
    by_cases hc : s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)
    · rw [if_pos (decide_eq_true hc), if_pos (decide_eq_true hc)]
    · rw [if_neg (by simpa using hc), if_neg (by simpa using hc), hvdef]
      simp only [hc, decide_false, entryL_eq, Bool.false_eq_true, ↓reduceIte, List.drop_one,
        List.tail_cons]
  rw [hB, hE, hbits, PolyExpr.eval_add]
  have hmP' : (aP ++ mP).length = pl.eval n + S.msgLen.eval n := by
    rw [List.length_append, haP, hmP]
  rw [List.append_assoc aP mP, List.take_left' (by rw [haP]), List.drop_left' (by rw [haP]),
    List.take_left' hmP, ← List.append_assoc, List.drop_left' hmP']

end TCSlib.Cryptography.Composability.NMSim
