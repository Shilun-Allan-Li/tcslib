/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIM-NME′ implies non-malleability: the sampler and the games

Direction SIM ⇒ IND of [PS10, Theorem 174.8] ([PSV07, Corollary 1], at one message). An NM
adversary `A` asks a challenge `⟨m₀, m₁⟩` and outputs ciphertexts. The SIM adversary forwards
`A`'s queries, with the sampler `halfSamp S` whose parameter is `⟨m₀, m₁⟩` and which outputs `m_β`
for its single coin `β` (with the empty history). With the coin `β` fixed, the real experiment's
oracles are those of `Ind_β` (`castImpl_indImpl_abs`), so the experiment `NM_β` is the hybrid
oracle's run with the coin `β` (`accept_nmGame_eq_rImpl`).

## Main definitions

* `NMSim.halfSamp`: the sampler `⟨m₀, m₁⟩ ↦ m_β`; `NMSim.halfCoins`: its coins are one bit.
* `NMSim.copyHandler`: the SIM adversary's handler (forwarding, output `A`'s output).
* `NMSim.halfDist` (`D''`), `NMSim.entryTails`, `NMSim.tailDist` (`D'`): the distinguishers.
* `NMSim.runB`: `A`'s run against the hybrid oracle with coin `β`.

## Main results

* `NMSim.halfSamp_runAt`, `NMSim.ofFn_drawWith_half`, `NMSim.expect_sample_halfCoins`.
* `NMSim.castImpl_indImpl_abs`: the CCA oracles of `Ind_β` are the hybrid oracle with coin `β`.
* `NMSim.accept_nmGame_eq_rImpl`: `NM_β` as a run against the hybrid oracle.
* `NMSim.simulate_copyHandler_machine`: the SIM adversary's run is `A`'s.
* `NMSim.tailDist_blocks`, `NMSim.halfDist_blocks`, `NMSim.nmOutput_eq_entryTails`: the
  distinguishers on the views.
* `NMSim.real_identity`, `NMSim.ideal_identity`: the identities behind the two gaps.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 1 and Corollary 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! Seal A (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean`, with every seal candidate of its
full TCSlib import closure (1310 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acEnc _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHyb _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acSeedTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acStLen _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl_adaptiveIndImpl.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.expect_tapeImpl.match_1_4 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.extTape _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.simulate_tapeImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.tapeImpl _root_.TCSlib.Cryptography.Composability.Attack.ofNat _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_some_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.length_of_firstQ_eq_some.match_1_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.NMSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmDecrypt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmOutput _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nthCt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.ofPadded _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.NMCCA2.ansRead _root_.TCSlib.Cryptography.Composability.NMCCA2.cntRead _root_.TCSlib.Cryptography.Composability.NMCCA2.decBlock _root_.TCSlib.Cryptography.Composability.NMCCA2.decHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encCt _root_.TCSlib.Cryptography.Composability.NMCCA2.encHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encTape _root_.TCSlib.Cryptography.Composability.NMCCA2.finA _root_.TCSlib.Cryptography.Composability.NMCCA2.finL _root_.TCSlib.Cryptography.Composability.NMCCA2.finU _root_.TCSlib.Cryptography.Composability.NMCCA2.finW _root_.TCSlib.Cryptography.Composability.NMCCA2.finZ _root_.TCSlib.Cryptography.Composability.NMCCA2.fwdHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.guessBit _root_.TCSlib.Cryptography.Composability.NMCCA2.guessDist _root_.TCSlib.Cryptography.Composability.NMCCA2.indImpl_eq_of_msgLen_eq_zero.match_1_1 _root_.TCSlib.Cryptography.Composability.NMCCA2.logEmit _root_.TCSlib.Cryptography.Composability.NMSim.chunkAt _root_.TCSlib.Cryptography.Composability.NMSim.chunkEmit _root_.TCSlib.Cryptography.Composability.NMSim.chunkMap _root_.TCSlib.Cryptography.Composability.NMSim.chunkStep _root_.TCSlib.Cryptography.Composability.NMSim.drawWith _root_.TCSlib.Cryptography.Composability.NMSim.encWith _root_.TCSlib.Cryptography.Composability.NMSim.entryL _root_.TCSlib.Cryptography.Composability.NMSim.expect_simulate_rImpl_eager.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.histImpl _root_.TCSlib.Cryptography.Composability.NMSim.histWith _root_.TCSlib.Cryptography.Composability.NMSim.hybAcc _root_.TCSlib.Cryptography.Composability.NMSim.idealAcc _root_.TCSlib.Cryptography.Composability.NMSim.idealView _root_.TCSlib.Cryptography.Composability.NMSim.rImpl _root_.TCSlib.Cryptography.Composability.NMSim.rImpl.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl.match_3 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_allOutputs_isSome.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_eq_of_msgLen_eq_zero.match_1_2 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_false_coins.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.realAcc _root_.TCSlib.Cryptography.Composability.NMSim.realView _root_.TCSlib.Cryptography.Composability.NMSim.snmDin _root_.TCSlib.Cryptography.Composability.NMSim.snmDin.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.snmDin_eval_inLens.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.snmDout _root_.TCSlib.Cryptography.Composability.NMSim.snmDout_eval_outLens.match_1_1 _root_.TCSlib.Cryptography.Composability.isPadded _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Composability.padDecFun _root_.TCSlib.Cryptography.Composability.padEncFun _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GGMRed.IsQ _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.advPoly _root_.TCSlib.Cryptography.GGMRed.adviceOf _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.ansMap _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinPoly _root_.TCSlib.Cryptography.GGMRed.coinStr _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.concrete _root_.TCSlib.Cryptography.GGMRed.concrete_iterate.match_1_1 _root_.TCSlib.Cryptography.GGMRed.encState _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.firstRound _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.nextQ _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.orbit_eq_encState.match_1_1 _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.prefMap _root_.TCSlib.Cryptography.GGMRed.pureAt _root_.TCSlib.Cryptography.GGMRed.pureStep _root_.TCSlib.Cryptography.GGMRed.pureStep.match_1 _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rawInput _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.stream _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.valStr _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.IInv _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom.match_1 _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.gB _root_.TCSlib.Cryptography.Games.EffFill.gC _root_.TCSlib.Cryptography.Games.EffFill.gCur _root_.TCSlib.Cryptography.Games.EffFill.gLc _root_.TCSlib.Cryptography.Games.EffFill.gLin _root_.TCSlib.Cryptography.Games.EffFill.gO _root_.TCSlib.Cryptography.Games.EffFill.gPh _root_.TCSlib.Cryptography.Games.EffFill.gS _root_.TCSlib.Cryptography.Games.EffFill.hAct _root_.TCSlib.Cryptography.Games.EffFill.hBound _root_.TCSlib.Cryptography.Games.EffFill.hCtx _root_.TCSlib.Cryptography.Games.EffFill.hMove _root_.TCSlib.Cryptography.Games.EffFill.hNext _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.hRes _root_.TCSlib.Cryptography.Games.EffFill.hRounds _root_.TCSlib.Cryptography.Games.EffFill.hStart _root_.TCSlib.Cryptography.Games.EffFill.hState _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iAnsLen _root_.TCSlib.Cryptography.Games.EffFill.iAsk _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallAct _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCallNext _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinAct _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinNext _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iFixBound _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iNext _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iTree _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_le_length_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.relabel _root_.TCSlib.Cryptography.Games.EffFill.relabelEmit _root_.TCSlib.Cryptography.Games.EffFill.relabelN _root_.TCSlib.Cryptography.Games.EffFill.relabelN_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.InteractiveHandler.rCnt _root_.TCSlib.Cryptography.Games.InteractiveHandler.rI _root_.TCSlib.Cryptography.Games.InteractiveHandler.rL _root_.TCSlib.Cryptography.Games.InteractiveHandler.rS _root_.TCSlib.Cryptography.Games.InteractiveHandler.rU _root_.TCSlib.Cryptography.Games.InteractiveHandler.rW _root_.TCSlib.Cryptography.Games.InteractiveHandler.rX _root_.TCSlib.Cryptography.Games.InteractiveHandler.rZ _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.answer.match_1 _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.buildComp_singleCodec.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.singleCodec _root_.TCSlib.Cryptography.Games.singleCodec.match_1 _root_.TCSlib.Cryptography.Games.toHist _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PublicKeyScheme.Secure _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.PublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_prf_of_exists_prg.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmPRF _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.hybridAdv _root_.TCSlib.Cryptography.hybridCoins _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridPlant _root_.TCSlib.Cryptography.hybridPre _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.length_flatten_ofFn.match_1_1 _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multiDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.singleDist _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


variable (S : FixedLengthPKScheme)

/-! ### The sampler `⟨m₀, m₁⟩ ↦ m_β` -/

/-- The sampler's raw function on `⟨⟨⟨1^n, a⟩, α⟩, ρ⟩`: the second half of `a` (from position
`msgLen(n)`) if the first coin is `1`, the first `msgLen(n)` bits otherwise. -/
private def halfFun (z : List Bool) : List Bool :=
  if (NUPPT.inCoins z).headD false then
    (NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)
  else (NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length)

/-- The sampler's raw function is polynomial-time. -/
private theorem polyTimeComputable_halfFun : PolyTimeComputable (halfFun S) := by
  have hpa := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp NUPPT.polyTimeComputable_inCoins)
    (((polyTimeComputable_pairDropPoly S.msgLen).comp hpa).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
    (((polyTimeComputable_pairTakePoly S.msgLen).comp hpa).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])

/-- **The sampler `⟨m₀, m₁⟩ ↦ m_β`**: the uniform machine with one coin `β` that outputs, on the
parameter `a = m₀ ‖ m₁`, its first `msgLen(n)` bits for `β = 0` and the rest for `β = 1`. -/
noncomputable def halfSamp : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1)

/-- The sampler on `y` with coins `ρ` outputs `y.drop msgLen(n)` if `ρ`'s first bit is `1` and
`y.take msgLen(n)` otherwise. -/
theorem halfSamp_runAt (n : ℕ) (y : List Bool) (ρ : (halfSamp S).Coins n) :
    (halfSamp S).runAt n y ρ =
      if (List.ofFn ρ).headD false then y.drop (S.msgLen.eval n) else y.take (S.msgLen.eval n) := by
  have hrun : ∀ y r, (halfSamp S).runAtL n y r =
      halfFun S (pairEncode (pairEncode (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n y r
  rw [NUPPT.runAt_eq, hrun, halfFun, NUPPT.inCoins_eq, NUPPT.inArg_eq, NUPPT.inParam_eq,
    NUPPT.advInput_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- A one-bit string is constant: for `k = 1`, `v = fun _ => ⟦v⟧.headD false`. -/
private theorem eq_const_headD {k : ℕ} (hk : k = 1) (v : Fin k → Bool) :
    v = fun _ => (List.ofFn v).headD false := by
  subst hk
  funext j
  rw [List.ofFn_succ, List.headD_cons, Subsingleton.elim j 0]

/-- **The sampler's coins are one bit:** `(halfSamp S).Coins n ≃ Bool`, reading the first bit. -/
noncomputable def halfCoins (n : ℕ) : (halfSamp S).Coins n ≃ Bool where
  toFun ρ := (List.ofFn ρ).headD false
  invFun β := (NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n).symm
    fun _ => β
  left_inv ρ := by
    set e := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n
    have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
    have hρ : (List.ofFn ρ).headD false = (List.ofFn (e ρ)).headD false := by
      rw [NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn]
    show e.symm (fun _ => (List.ofFn ρ).headD false) = ρ
    rw [hρ, ← eq_const_headD h1 (e ρ), Equiv.symm_apply_apply]
  right_inv β := by
    set e := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n
    have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
    show (List.ofFn (e.symm fun _ => β)).headD false = β
    rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn (polyTimeComputable_halfFun S) (.const 1) n,
      Equiv.apply_symm_apply, List.ofFn_const, h1, List.replicate_one, List.headD_cons]

/-- The bijection reads the first coin bit: `halfCoins S n ρ = ⟦ρ⟧.headD false`. -/
theorem halfCoins_apply (n : ℕ) (ρ : (halfSamp S).Coins n) :
    halfCoins S n ρ = (List.ofFn ρ).headD false := rfl

/-- The coin of `β` has first bit `β`: `⟦(halfCoins S n).symm β⟧.headD false = β`. -/
theorem headD_ofFn_halfCoins_symm (n : ℕ) (β : Bool) :
    (List.ofFn ((halfCoins S n).symm β)).headD false = β :=
  (halfCoins S n).apply_symm_apply β

/-- **The sampler's draw with coin `β`:** for a parameter of `2 · msgLen(n)` bits,
`⟦M(a; β)⟧ = if β then ⟦a⟧.drop msgLen(n) else ⟦a⟧.take msgLen(n)`. -/
theorem ofFn_drawWith_half (n : ℕ) {k : ℕ} (a : Fin k → Bool)
    (hk : k = S.msgLen.eval n + S.msgLen.eval n) (β : Bool) :
    List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n a ((halfCoins S n).symm β)) =
      if β then (List.ofFn a).drop (S.msgLen.eval n) else (List.ofFn a).take (S.msgLen.eval n) := by
  rw [drawWith_eq, halfSamp_runAt, headD_ofFn_halfCoins_symm]
  refine ofFn_padFin_of_length ?_
  cases β <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_take, List.length_drop,
    List.length_ofFn] <;> omega

/-- **Averaging over the sampler's coins** is averaging over `β`:
`𝔼_ρ[g ρ] = (g (coin 0) + g (coin 1)) / 2`. -/
theorem expect_sample_halfCoins (n : ℕ) (g : (halfSamp S).Coins n → ℝ) :
    expect (sample ((halfSamp S).Coins n)) g =
      (g ((halfCoins S n).symm false) + g ((halfCoins S n).symm true)) / 2 := by
  rw [← ProbComp.expect_sample_equiv (halfCoins S n).symm, expect_sample, Fintype.sum_bool,
    Fintype.card_bool]
  ring

/-! ### `Ind_β` is the hybrid oracle with coin `β` -/

/-- **The CCA oracles of `Ind_β` are the hybrid oracle with the sampler's coin `β`** (on T2's
lengths
with `pl = 2 · msgLen`, `hl = 0`), once the hybrid's state forgets the recorded parameter:
`castImpl (Ind_β) i x (s.map fst) =
(rImpl … (coin β) … i x s).bind fun p => pure (p.1, p.2.map fst)`.

**Proof sketch.** `Dec`: the same availability, refusal and decryption (`indImpl_dec_onSpec_cast`,
`rImpl_dec`), the casts keeping the strings (`ofFn_cast`). A repeated challenge repeats the record
with the empty history. A first challenge encrypts `m_β`, which is the sampler's draw with coin `β`
(`ofFn_drawWith_half`, `ofFn_splitHalf_fst/_snd`). -/
theorem castImpl_indImpl_abs (atk : Attack) (β : Bool) (n : ℕ) (pk sk : List Bool)
    (hist : List Bool → List Bool) (ρ' : (halfSamp S).Coins n) (i : Fin 2)
    (x : (bitSpecAt (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) ×
      (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) :
    castImpl (ins := fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
        (outs := fun i => (snmDout S (.const 0) i).eval n) (S.indImpl atk β n pk sk) i x
        (s.map Prod.fst) =
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x s).bind fun p => .pure (p.1, p.2.map Prod.fst) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hd0 : (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) 0 = S.ctLen.eval n := by
    show (snmDin S _ 0).eval n = _
    rw [snmDin_zero]
  have hd1 : (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) 1 =
      (S.msgLen.add S.msgLen).eval n := by
    show (snmDin S _ 1).eval n = _
    rw [snmDin_one]
  match i, x with
  | 0, x =>
    have hc : cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)) =
        padFin (S.ctLen.eval n) (List.ofFn x) := by
      apply List.ofFn_injective
      rw [ofFn_cast (S.inLens_zero n),
        ofFn_padFin_of_length (by rw [List.length_ofFn, hd0, S.inLens_zero]),
        ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])]
    have hx : List.ofFn (padFin (S.ctLen.eval n) (List.ofFn x)) = List.ofFn x :=
      ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])
    rw [Games.castImpl_eq, S.indImpl_dec_onSpec_cast, rImpl_dec, hc, Option.isSome_map, hx]
    by_cases hcond : (FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin (S.ctLen.eval n) (List.ofFn x)))) = true
    · rw [if_pos hcond, if_pos hcond, OracleComp.pure_bind, OracleComp.pure_bind]
      dsimp only
      rw [ofFn_cast (S.outLens_zero n).symm]
    · rw [if_neg hcond, if_neg hcond, OracleComp.pure_bind, OracleComp.pure_bind]
      dsimp only
      rw [Games.padFin_ofFn_zeroBits]
  | 1, x =>
    have hh : ∀ {ℓ : ℕ} (m : Fin ℓ → Bool),
        List.ofFn (histWith hist ((PolyExpr.const 0).eval n) m) = [] := fun m =>
      List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
    cases s with
    | some ya =>
      obtain ⟨y, a⟩ := ya
      rw [Option.map_some, Games.castImpl_eq, S.indImpl_challenge_repeat_onSpec,
        OracleComp.pure_bind, rImpl_some, OracleComp.pure_bind]
      dsimp only
      rw [ofFn_cast (S.outLens_one n).symm, hh, List.append_nil, Option.map_some]
    | none =>
      rw [Option.map_none, Games.castImpl_eq, S.indImpl_challenge_none_onSpec, rImpl_none_lazy,
        OracleComp.bind_assoc, OracleComp.bind_assoc]
      refine congrArg _ (funext fun re => ?_)
      rw [OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind]
      dsimp only
      have hdraw : List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) ((halfCoins S n).symm β)) =
          List.ofFn (if β then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n)
            (padFin (S.inLens n 1) (List.ofFn x)))).2 else (FixedLengthScheme.splitHalf
              (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).1) := by
        have hx : List.ofFn (cast (S.indSpec_challengeDom n)
            (padFin (S.inLens n 1) (List.ofFn x))) =
            List.ofFn (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) := by
          rw [ofFn_cast (S.inLens_one n),
            ofFn_padFin_of_length (by rw [List.length_ofFn, hd1, hpl, S.inLens_one]),
            ofFn_padFin_of_length (by rw [List.length_ofFn, hd1])]
        rw [ofFn_drawWith_half S n _ hpl]
        cases β
        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
            FixedLengthScheme.ofFn_splitHalf_fst, hx]
        · rw [if_pos rfl, if_pos rfl, FixedLengthScheme.ofFn_splitHalf_snd, hx]
      have he : encWith S n pk (drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x))
          (if false = true then ρ' else (halfCoins S n).symm β)) re =
          padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
            (if β then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n)
              (padFin (S.inLens n 1) (List.ofFn x)))).2 else (FixedLengthScheme.splitHalf
                (cast (S.indSpec_challengeDom n)
                  (padFin (S.inLens n 1) (List.ofFn x)))).1))) re) := by
        rw [if_neg Bool.false_ne_true, encWith_eq, hdraw]
      rw [he, ofFn_cast (S.outLens_one n).symm, hh, List.append_nil, Option.map_some]

/-- **`NM_β` is the hybrid run with the sampler's coin `β`:** the experiment of Definition 172.6
for `A` (budget `q`, `ℓ` ciphertexts) and `D` accepts with the expectation, over the keys, `A`'s
coins and `D`'s coins, of `D`'s verdict on `nmOutput sk (s.map fst) ⟦a⟧` for the run of `A` (on
T2's lengths) against the hybrid oracle with coin `β`, its output `a` and final state `s`.

**Proof sketch.** Transport `A`'s run to T2's lengths (`nmCodec_eq_bitCodec`,
`expect_simulate_castImpl_toCompOn` with `snmDin_eval_inLens`, `snmDout_eval_outLens`) and pass to
the hybrid oracle through the state abstraction `s ↦ s.map fst` (`simulate_eq_of_abs`,
`castImpl_indImpl_abs`). -/
theorem accept_nmGame_eq_rImpl (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (β : Bool)
    (n : ℕ) (hist : List Bool → List Bool) (ρ' : (halfSamp S).Coins n) :
    accept (S.nmGame atk A q ℓ D β n) =
      expect (sample (S.gen.Coins n)) fun rg =>
      expect (sample (A.Coins n)) fun r =>
      expect (sample (D.Coins n)) fun rD =>
        expect (simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n
            (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
            ((halfCoins S n).symm β) ρ' none)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q
            (pairFstD (S.gen.runAt n [] rg)) r) none)
          fun p => if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
            (p.2.map Prod.fst) (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true
            then 1 else 0 := by
  rw [accept_eq, S.nmGame_eq, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun rD => ?_)
  have h2 : (fun res : (Fin (ℓ * S.ctLen.eval n) → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (D.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) rD)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin (ℓ * S.ctLen.eval n) p.1)) rD = true then (1 : ℝ) else 0)
        (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, S.nmCodec_eq_bitCodec, h2]
  refine (Games.expect_simulate_castImpl_toCompOn (snmDin_eval_inLens S n)
    (snmDout_eval_outLens S n) rfl
    (S.indImpl atk β n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))) A n q
    _ r none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin (ℓ * S.ctLen.eval n) p.1)) rD = true then (1 : ℝ) else 0)).symm.trans ?_
  have habs := Games.simulate_eq_of_abs _ _ (Option.map Prod.fst)
    (fun i x s => castImpl_indImpl_abs S atk β n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) hist ρ' i x s)
    (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
      (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q
      (pairFstD (S.gen.runAt n [] rg)) r) none
  rw [Option.map_none] at habs
  rw [habs, expect_bind]
  simp only [expect_pure]

/-! ### The SIM adversary -/

open NMCCA2 (fwdHandler fwdHandler_finRun fwdHandler_finCall fwdHandler_advIn
  simulate_fwdHandler_impl fields_finInput polyTimeComputable_finFields finA)

/-- The SIM adversary's finalization round: output the adversary's output, `⟨[true], a⟩`. -/
private def copyFin (w : List Bool) : List Bool := pairEncode [true] (finA w)

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_copyFin : PolyTimeComputable copyFin :=
  (polyTimeComputable_const [true]).pairEncode polyTimeComputable_finFields.2.2.2.1

/-- The adversary's input is the reduction input. -/
private theorem polyTimeComputable_copyAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairSndD ctx) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- **The SIM adversary's handler** (on the real experiment's oracles with parameter length `pl`
and history length `hl`): it forwards every query (`NMCCA2.fwdHandler`), runs the adversary on the
reduction input, asks nothing in finalization, and outputs the adversary's `outLen(n)`-bit
output. -/
def copyHandler (pl hl outLen : PolyExpr) :
    InteractiveHandler 2 (snmDin S pl) (snmDout S hl) 2 (snmDin S pl) (snmDout S hl) :=
  fwdHandler (snmDin S pl) (snmDout S hl) (.const 0) (fun ctx => pairFstD (pairSndD ctx))
    polyTimeComputable_copyAdvIn outLen (.const 0) copyFin polyTimeComputable_copyFin

/-- The adversary runs on the reduction input: `(copyHandler S pl hl outLen).advInput n z ω = z`. -/
theorem copyHandler_advInput (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) :
    (copyHandler S pl hl outLen).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [copyHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The SIM adversary outputs `outLen(n)` bits: `(copyHandler S pl hl outLen).outLen = outLen`. -/
theorem copyHandler_outLen (pl hl outLen : PolyExpr) :
    (copyHandler S pl hl outLen).outLen = outLen := by
  rw [copyHandler, NMCCA2.fwdHandler_outLen]

/-- **The handler forwards** (`simulate_fwdHandler_impl`). -/
theorem simulate_copyHandler_impl (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α)
    (s : Fin ((copyHandler S pl hl outLen).stateLen.eval n) → Bool) :
    simulate ((copyHandler S pl hl outLen).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (snmDin S pl) (snmDout S hl) (.const 0) _ polyTimeComputable_copyAdvIn
    outLen (.const 0) copyFin polyTimeComputable_copyFin n z ω c s

/-- **The finalization outputs the adversary's output** (of `outLen(n)` bits), asking nothing:
`H.finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem copyHandler_finish (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
    (s : Fin ((copyHandler S pl hl outLen).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (hd : d = outLen.eval n) :
    (copyHandler S pl hl outLen).finish n z ω s a =
      .pure (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) := by
  have hfin : (copyHandler S pl hl outLen).finRun = copyFin := by
    funext w
    rw [copyHandler, fwdHandler_finRun]
  have hfc : (copyHandler S pl hl outLen).finCall = .const 0 := by
    rw [copyHandler, fwdHandler_finCall]
  have hol := copyHandler_outLen S pl hl outLen
  rw [InteractiveHandler.finish_eq, hfc, PolyExpr.eval_const]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ ((copyHandler S pl hl outLen).finRun _) = _
  rw [hfin, copyFin, (fields_finInput _ _ _ _ _ _).2.2.2.1]
  have hw : List.ofFn (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) =
      List.ofFn a := ofFn_padFin_of_length (by rw [List.length_ofFn, hol, hd])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-- **The SIM adversary's run is the adversary's run.** Let `B` be T2's machine for
`copyHandler S pl hl outLen` (coin bijection `φ`). Against any oracle `O` and from any state `s₀`,
`B`'s run on `pk` with coins `φ (ω, r)` is `A`'s run on `pk` with coins `r`, its output read at
`outLen(n)` bits. -/
theorem simulate_copyHandler_machine (A B : NUPPT) (q dα pl hl outLen : PolyExpr) (n : ℕ)
    (hd : dα.eval n = outLen.eval n)
    (φ : (Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((copyHandler S pl hl outLen).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (dα.eval n)) n (q.eval n) ((copyHandler S pl hl outLen).advInput n z ω) r)
          ((copyHandler S pl hl outLen).init n)).bind
          (fun res => (copyHandler S pl hl outLen).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n) (fun j => (snmDout S hl j).eval n)
          ((copyHandler S pl hl outLen).outLen.eval n)) n
          (q.eval n * (copyHandler S pl hl outLen).perCall.eval n +
            (copyHandler S pl hl outLen).finCall.eval n) z (φ (ω, r)))
    {σ : Type} (O : QueryImpl (bitSpecAt (snmDin S pl) (snmDout S hl) n) σ unifSpec) (s₀ : σ)
    (pk : List Bool) (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
    (r : A.Coins n) :
    simulate O (B.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n)
        (fun j => (snmDout S hl j).eval n) ((copyHandler S pl hl outLen).outLen.eval n)) n
        (q.eval n * (copyHandler S pl hl outLen).perCall.eval n +
          (copyHandler S pl hl outLen).finCall.eval n) pk (φ (ω, r))) s₀ =
      (simulate O (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n)
          (fun i => (snmDout S hl i).eval n) (dα.eval n)) n (q.eval n) pk r) s₀).bind fun p =>
        .pure (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn p.1), p.2) := by
  rw [← hφ, copyHandler_advInput, simulate_copyHandler_impl, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, copyHandler_finish S pl hl outLen n pk ω _ _ hd]
  rw [simulate_bind]
  simp only [simulate_pure]

/-! ### The distinguishers -/

/-- `z ↦ (g z).take msgLen(|1^n|)` for the parameter slot `1^n` of a machine input. -/
private theorem polyTimeComputable_takeMsg {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => (g z).take (S.msgLen.eval (NUPPT.inParam z).length) :=
  ((polyTimeComputable_pairTakePoly S.msgLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `z ↦ (g z).drop msgLen(|1^n|)` for the parameter slot `1^n` of a machine input. -/
private theorem polyTimeComputable_dropMsg {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => (g z).drop (S.msgLen.eval (NUPPT.inParam z).length) :=
  ((polyTimeComputable_pairDropPoly S.msgLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `D''`'s raw function: on the view `y`, whether its first two `msgLen(n)`-bit blocks differ. -/
private def halfFunD (z : List Bool) : List Bool :=
  [!decide ((NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length) =
    ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
      (S.msgLen.eval (NUPPT.inParam z).length))]

/-- `D''`'s raw function is polynomial-time. -/
private theorem polyTimeComputable_halfFunD : PolyTimeComputable (halfFunD S) :=
  polyTimeComputable_not ((polyTimeComputable_pairEq.comp
    ((polyTimeComputable_takeMsg S NUPPT.polyTimeComputable_inArg).pairEncode
      (polyTimeComputable_takeMsg S (polyTimeComputable_dropMsg S
        NUPPT.polyTimeComputable_inArg)))).congr fun z => by
          simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])

/-- **The distinguisher `D''`:** the uniform machine without coins accepting a view whose
parameter `⟨m₀, m₁⟩` (its first `2 · msgLen(n)` bits) has `m₀ ≠ m₁`. -/
noncomputable def halfDist : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_halfFunD S) (.const 0)

/-- `D''` accepts `y` iff its first two `msgLen(n)`-bit blocks differ:
`(halfDist S).distinguisherL n y ρ = !decide (y.take L = (y.drop L).take L)`. -/
theorem halfDist_distinguisherL (n : ℕ) (y : List Bool) (ρ : (halfDist S).Coins n) :
    (halfDist S).distinguisherL n y ρ =
      !decide (y.take (S.msgLen.eval n) = (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) := by
  have hrun : ∀ y r, (halfDist S).runAtL n y r =
      halfFunD S (pairEncode (pairEncode (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform (polyTimeComputable_halfFunD S) (.const 0) n y r
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hrun, halfFunD, NUPPT.inArg_eq, NUPPT.inParam_eq,
    NUPPT.advInput_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  cases decide (y.take (S.msgLen.eval n) = (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) <;>
    decide

/-- The tails of the entries: each `msgLen(n) + 2`-bit chunk without its first bit (the `COPY`
flag), on `⟨⟨1^n, []⟩, entries⟩`. -/
def entryTails : List Bool → List Bool :=
  chunkMap (S.msgLen.add (.const 2)) fun _ ch => ch.drop 1

/-- `entryTails S = chunkMap (msgLen + 2) (fun _ ch => ch.drop 1)`. -/
theorem entryTails_eq : entryTails S = chunkMap (S.msgLen.add (.const 2)) fun _ ch => ch.drop 1 :=
  rfl

/-- The tails of the entries are polynomial-time. -/
theorem polyTimeComputable_entryTails : PolyTimeComputable (entryTails S) :=
  polyTimeComputable_chunkMap _ (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

variable (D : NUPPT)

/-- `D'`'s raw function on `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with the view `y = a₀ ‖ a₁ ‖ m ‖ entries`
(`msgLen(n)` bits each for `a₀`, `a₁`, `m`): `0` if `a₀ = a₁`, and otherwise whether `D`'s verdict
(advice `α`, coins `ρ`) on the entries' tails equals `[m = a₁]`. -/
private def tailFun (z : List Bool) : List Bool :=
  if decide ((NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length) =
      ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
        (S.msgLen.eval (NUPPT.inParam z).length)) then [false]
  else [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (entryTails S (pairEncode (pairEncode (NUPPT.inParam z) [])
        ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
          (S.msgLen.eval (NUPPT.inParam z).length)).drop (S.msgLen.eval (NUPPT.inParam z).length))))
      (NUPPT.inAdvice z) (NUPPT.inCoins z)) = [true]) ==
    decide ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
        (S.msgLen.eval (NUPPT.inParam z).length)).take (S.msgLen.eval (NUPPT.inParam z).length) =
      ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
        (S.msgLen.eval (NUPPT.inParam z).length))]

/-- `D'`'s raw function is polynomial-time.

**Proof sketch.** `a₀`, `a₁`, `m` and the entries are `take`/`drop`s of `msgLen(n)` bits of the
view (`polyTimeComputable_takeMsg`, `polyTimeComputable_dropMsg`), the tails are
`polyTimeComputable_entryTails`, `D`'s verdict is `D.output` on `layout`, and the equality tests
use `polyTimeComputable_pairEq`. The outer test is `polyTimeComputable_ite`, and `[v == w]` is
the `ite` on `v` of `[w]` and `[!w]`. -/
private theorem polyTimeComputable_tailFun : PolyTimeComputable (tailFun S D) := by
  have hy := NUPPT.polyTimeComputable_inArg
  have hu := NUPPT.polyTimeComputable_inParam
  have hd1 := polyTimeComputable_dropMsg S hy
  have hd2 := polyTimeComputable_dropMsg S hd1
  have hd3 := polyTimeComputable_dropMsg S hd2
  have ha0 := polyTimeComputable_takeMsg S hy
  have ha1 := polyTimeComputable_takeMsg S hd1
  have hm := polyTimeComputable_takeMsg S hd2
  have heq : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
      PolyTimeComputable fun z => [decide (f z = g z)] := fun hf hg =>
    (polyTimeComputable_pairEq.comp (hf.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hconv : PolyTimeComputable fun z => entryTails S (pairEncode (pairEncode
      (NUPPT.inParam z) []) ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
        (S.msgLen.eval (NUPPT.inParam z).length)).drop (S.msgLen.eval (NUPPT.inParam z).length))) :=
    (polyTimeComputable_entryTails S).comp ((hu.pairEncode (polyTimeComputable_const [])).pairEncode
      hd3)
  have hv := heq (D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout hu hconv
    NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    (polyTimeComputable_const [true])
  have hw := heq hm ha1
  refine polyTimeComputable_ite (heq ha0 ha1) (polyTimeComputable_const [false]) ?_
  have key : ∀ v w : Bool, (if v = true then [w] else [!w]) = [v == w] := by decide
  exact (polyTimeComputable_ite hv hw (polyTimeComputable_not hw)).congr fun z => by
    rw [Function.comp_apply]
    exact key _ _

/-- **The distinguisher `D'`** built from `D`, with `D`'s coins and advice: on a view
`a₀ ‖ a₁ ‖ m ‖ entries` it outputs `0` if `a₀ = a₁`, and otherwise whether `D`'s verdict on the
entries' tails (the `COPY` flags dropped, so a copy reads as `⊥`) equals `[m = a₁]`. -/
noncomputable def tailDist : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_tailFun S D) D.coins D.adv D.advice D.advice_length

/-- `D'` has `D`'s coins. -/
theorem tailDist_coins : (tailDist S D).coins = D.coins := by
  rw [tailDist, NUPPT.coins_ofPolyTime]

/-- **`D'`'s verdict** on a view `y`, with `D`'s coins `rD` carried over: with `L = msgLen(n)`,
`0` if `y`'s first two `L`-bit blocks are equal, and otherwise `[D(entryTails (y.drop 3L)) =
[true]] == [third block = second block]`. -/
theorem tailDist_distinguisherL (n : ℕ) (y : List Bool) (rD : D.Coins n) :
    (tailDist S D).distinguisherL n y (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) =
      if decide (y.take (S.msgLen.eval n) =
          (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) then false
      else (D.distinguisherL n (entryTails S (pairEncode (pairEncode (List.replicate n true) [])
          (((y.drop (S.msgLen.eval n)).drop (S.msgLen.eval n)).drop (S.msgLen.eval n)))) rD ==
        decide (((y.drop (S.msgLen.eval n)).drop (S.msgLen.eval n)).take (S.msgLen.eval n) =
          (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n))) := by
  have hlay : pairEncode (pairEncode (NUPPT.advInput n y) (D.advice n)) (List.ofFn rD) =
      NUPPT.layout (List.replicate n true) y (D.advice n) (List.ofFn rD) := by
    rw [NUPPT.layout_eq, NUPPT.advInput_eq]
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_coinsCongr, tailDist, NUPPT.runAtL_ofPolyTime, tailFun,
    hlay]
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.inCoins_layout, List.length_replicate]
  rw [← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]
  split
  · rfl
  · generalize D.distinguisherL n _ rD = v
    cases v <;> simp

/-! ### The distinguishers on the views -/

/-- The four blocks of a view `A ‖ M ‖ E` with `|A| = 2L`, `|M| = L`. -/
private theorem blocks_append (L : ℕ) (A M E : List Bool) (hA : A.length = L + L)
    (hM : M.length = L) :
    (A ++ M ++ E).take L = A.take L ∧ ((A ++ M ++ E).drop L).take L = A.drop L ∧
      (((A ++ M ++ E).drop L).drop L).take L = M ∧ (((A ++ M ++ E).drop L).drop L).drop L = E := by
  have hd : (A.drop L).length = L := by rw [List.length_drop]; omega
  rw [List.append_assoc]
  refine ⟨List.take_append_of_le_length (by omega), ?_, ?_, ?_⟩
  · rw [List.drop_append_of_le_length (by omega), List.take_left' hd]
  · rw [List.drop_append_of_le_length (by omega), List.drop_left' hd, List.take_left' hM]
  · rw [List.drop_append_of_le_length (by omega), List.drop_left' hd, List.drop_left' hM]

/-- **`D'` on a view `A ‖ M ‖ E`** (`|A| = 2·msgLen(n)`, `|M| = msgLen(n)`): `0` if the halves of
`A` are equal, and otherwise `[D(entryTails E) = 1] == [M = second half of A]`. -/
theorem tailDist_blocks (n : ℕ) (A M E : List Bool)
    (hA : A.length = S.msgLen.eval n + S.msgLen.eval n) (hM : M.length = S.msgLen.eval n)
    (rD : D.Coins n) :
    (tailDist S D).distinguisherL n (A ++ M ++ E)
        (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) =
      if decide (A.take (S.msgLen.eval n) = A.drop (S.msgLen.eval n)) then false
      else (D.distinguisherL n (entryTails S (pairEncode (pairEncode (List.replicate n true) [])
        E)) rD == decide (M = A.drop (S.msgLen.eval n))) := by
  obtain ⟨h1, h2, h3, h4⟩ := blocks_append _ A M E hA hM
  rw [tailDist_distinguisherL, h1, h2, h3, h4]

/-- **`D''` on a view `A ‖ M ‖ E`:** whether the halves of `A` differ. -/
theorem halfDist_blocks (n : ℕ) (A M E : List Bool)
    (hA : A.length = S.msgLen.eval n + S.msgLen.eval n) (hM : M.length = S.msgLen.eval n)
    (ρ : (halfDist S).Coins n) :
    (halfDist S).distinguisherL n (A ++ M ++ E) ρ =
      !decide (A.take (S.msgLen.eval n) = A.drop (S.msgLen.eval n)) := by
  obtain ⟨h1, h2, -, -⟩ := blocks_append _ A M E hA hM
  rw [halfDist_distinguisherL, h1, h2]

/-- An entry without its `COPY` flag: `⊥ = 0` for a copy, `Dec`'s answer otherwise. -/
theorem entryL_drop_one (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    (entryL S n sk copy c).drop 1 =
      if copy then List.replicate (S.msgLen.eval n + 1) false
      else List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c)))) := by
  rw [entryL_eq]
  cases copy <;> rfl

/-- **The entries' tails are the decrypted entries** (`chunkMap_flatten`; every entry has
`msgLen(n) + 2` bits). -/
theorem entryTails_entries (n : ℕ) (sk : List Bool) (es : List (Bool × List Bool)) :
    entryTails S (pairEncode (pairEncode (List.replicate n true) [])
        (es.map fun e => entryL S n sk e.1 e.2).flatten) =
      (es.map fun e => (entryL S n sk e.1 e.2).drop 1).flatten := by
  have hlen : (S.msgLen.add (.const 2)).eval n = S.msgLen.eval n + 2 := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  rw [entryTails_eq, chunkMap_flatten _ _ n [] _ (fun ch hch => ?_) (by rw [hlen]; omega),
    List.map_map]
  · rfl
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hch
    rw [hlen, entryL_eq]
    cases e.1 <;> simp

/-- **The experiment's output is the entries' tails:** for an output string `w` of `ℓ` ciphertexts,
`nmOutput sk s' w` is the concatenation of the tails of the entries `entryL … [ciphertext i is
the challenge] (ciphertext i)`. -/
theorem nmOutput_eq_entryTails (n ℓ : ℕ) (sk : List Bool)
    (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (w : List Bool) (hw : w.length = ℓ * S.ctLen.eval n) :
    S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) w) =
      ((List.range ℓ).map fun i => (entryL S n sk
        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
        (chunkAt (S.ctLen.eval n) i w)).drop 1).flatten := by
  rw [S.nmOutput_eq]
  congr 1
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range, entryL_drop_one, S.nmDecrypt_eq]
  have hc : List.ofFn (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
      rw [List.length_ofFn] at h₁; exact h₁⟩) = chunkAt (S.ctLen.eval n) i w := by
    rw [S.ofFn_nthCt, ofFn_padFin_of_length hw, chunkAt_eq]
  have hcopy : (s' = some (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
      rw [List.length_ofFn] at h₁; exact h₁⟩)) ↔
      s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w) := by
    rw [← hc]
    cases s' with
    | none => simp
    | some c => simp [List.ofFn_inj]
  by_cases h : s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)
  · rw [if_pos (hcopy.2 h), decide_eq_true h, if_pos rfl, ofFn_zeroBits]
  · rw [if_neg (fun h' => h (hcopy.1 h')), decide_eq_false h, if_neg Bool.false_ne_true, hc]

/-! ### The real experiment against `NM_0`, `NM_1` -/

/-- `D'`'s indicator on a view with parameter `A` and message `m_β`, as a function of `D`'s verdict
`t`: `[m₀ ≠ m₁] · [t = β]`. -/
private theorem tail_indicator (A : List Bool) (L : ℕ) (t β : Bool) :
    (if (if decide (A.take L = A.drop L) then false
      else (t == decide ((if β then A.drop L else A.take L) = A.drop L))) = true then (1 : ℝ)
      else 0) =
      if A.take L ≠ A.drop L then (if β then (if t then 1 else 0) else 1 - (if t then 1 else 0))
      else 0 := by
  by_cases hb : A.take L = A.drop L
  · simp [hb]
  · cases β <;> cases t <;> simp [hb]

/-- `D''`'s indicator on a view with parameter `A`: `[m₀ ≠ m₁]`. -/
private theorem half_indicator (A : List Bool) (L : ℕ) :
    (if (!decide (A.take L = A.drop L)) = true then (1 : ℝ) else 0) =
      if A.take L ≠ A.drop L then 1 else 0 := by
  by_cases hb : A.take L = A.drop L <;> simp [hb]

section RealIdentity

variable (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (n : ℕ) (hist : List Bool → List Bool)
  (pk sk : List Bool) (r : A.Coins n) (ρ' : (halfSamp S).Coins n)

/-- **The run of `A` against the hybrid oracle with the sampler's coin `β`** (the real experiment of
the SIM adversary, and `NM_β`): `simulate (rImpl … false … (coin β) ρ' none) (A's run) none`. -/
noncomputable abbrev runB (β : Bool) :
    ProbComp ((Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) :=
  simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
      ((halfCoins S n).symm β) ρ' none)
    (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
      (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q pk r) none

/-- `runB … β = simulate (rImpl … false … (coin β) ρ' none) (A.toCompOn … n q pk r) none`. -/
theorem runB_eq (β : Bool) :
    runB S atk A q ℓ n hist pk sk r ρ' β =
      simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
          ((halfCoins S n).symm β) ρ' none)
        (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
          (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q pk r) none := rfl

/-- The bad event of the coupling: the recorded parameter `⟨m₀, m₁⟩` has `m₀ ≠ m₁` (never for the
empty state, whose parameter reads `0`). -/
private def badHalves (s : Option ((Fin (S.ctLen.eval n) → Bool) ×
    (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) : Prop :=
  (List.ofFn ((s.map Prod.snd).getD (zeroBits _))).take (S.msgLen.eval n) ≠
    (List.ofFn ((s.map Prod.snd).getD (zeroBits _))).drop (S.msgLen.eval n)

private instance : DecidablePred (badHalves S n) := fun _ => instDecidableNot

/-- **The coupling of the two coins:** `𝔼[G · 1_{m₀ = m₁}]` is the same with the sampler's coin
`0` and `1` (`expect_eq_until_bad`): the oracles agree while the recorded parameter has equal
halves, and a bad parameter stays recorded.

**Proof sketch.** `expect_eq_until_bad` with the bad event `badHalves`. The empty state is good
(its parameter reads `0`, `ofFn_zeroBits`), and a recorded state stays recorded (`rImpl_dec`,
`rImpl_some`), so bad is sticky. From a good state the two oracles agree: `Dec` and repeated
challenges do not read the coin (the history is empty), and on a first challenge, after the same
encryption coins, the new state is bad on both sides or `m₀ = m₁` and the two draws coincide
(`ofFn_drawWith_half`). -/
private theorem expect_runB_good (G : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) → ℝ) :
    expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else G p) =
      expect (runB S atk A q ℓ n hist pk sk r ρ' true)
        (fun p => if badHalves S n p.2 then 0 else G p) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hh : ∀ {ℓ' : ℕ} (m : Fin ℓ' → Bool),
      List.ofFn (histWith hist ((PolyExpr.const 0).eval n) m) = [] := fun m =>
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
  have hnone : ¬ badHalves S n none := by
    unfold badHalves
    intro h
    apply h
    rw [Option.map_none, Option.getD_none, ofFn_zeroBits, hpl, List.take_replicate,
      List.drop_replicate]
    congr 1
    omega
  have hkeep : ∀ (β : Bool) i x y a,
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x (some (y, a))).AllOutputs
        fun ys => ys.2 = some (y, a) := by
    intro β i x y a
    match i with
    | 0 =>
      rw [rImpl_dec]
      split <;> exact OracleComp.allOutputs_pure.2 rfl
    | 1 =>
      rw [rImpl_some]
      exact OracleComp.allOutputs_pure.2 rfl
  have hstick : ∀ (β : Bool) i x s, badHalves S n s →
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x s).AllOutputs fun ys => badHalves S n ys.2 := by
    intro β i x s hs
    cases s with
    | none => exact absurd hs hnone
    | some ya => exact (hkeep β i x ya.1 ya.2).mono fun ys h => h ▸ hs
  refine expect_eq_until_bad (badHalves S n) (fun i x s hs g => ?_) (hstick false) (hstick true) _
    G hnone
  match i, s with
  | 0, s => rw [rImpl_dec, rImpl_dec]
  | 1, some (y, a) => rw [rImpl_some, rImpl_some, hh, hh]
  | 1, none =>
    rw [rImpl_none_lazy, rImpl_none_lazy, expect_bind, expect_bind]
    refine congrArg _ (funext fun re => ?_)
    rw [rImpl_none_eager, rImpl_none_eager, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      expect_pure, expect_pure]
    by_cases hb : badHalves S n (some (default, padFin ((S.msgLen.add S.msgLen).eval n)
      (List.ofFn x)))
    · have hb' : ∀ y, badHalves S n (some (y, padFin ((S.msgLen.add S.msgLen).eval n)
          (List.ofFn x))) := fun y => hb
      dsimp only
      rw [if_pos (hb' _), if_pos (hb' _)]
    · have heq : drawWith (halfSamp S) (S.msgLen.eval n) n (padFin ((S.msgLen.add S.msgLen).eval n)
          (List.ofFn x)) ((halfCoins S n).symm false) = drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) ((halfCoins S n).symm true) := by
        apply List.ofFn_injective
        rw [ofFn_drawWith_half S n _ hpl, ofFn_drawWith_half S n _ hpl, if_neg Bool.false_ne_true,
          if_pos rfl]
        simpa [badHalves] using hb
      rw [heq]

/-- **The real identity** at fixed keys and coins: for the views of the SIM adversary's real
experiment with coin `β`, `2 · avg_β 𝔼[D'] − avg_β 𝔼[D''] = 𝔼_1[D(NM)] − 𝔼_0[D(NM)]`, where the
last two are `NM_1` and `NM_0`.

**Proof sketch.** On the views, `D'` is `[m₀ ≠ m₁] · [D(NM) = β]` and `D''` is `[m₀ ≠ m₁]`
(`tailDist_blocks`, `halfDist_blocks`, `ofFn_drawWith_half`, `entryTails_entries`,
`nmOutput_eq_entryTails`). By the coupling (`expect_runB_good`) the good parts of `D(NM)` and of `1`
have the same expectation under both coins; the identity is then linear algebra. -/
theorem real_identity (D : NUPPT) (rD : D.Coins n) (ρ'' : (halfDist S).Coins n) :
    (expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
        if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
          ((halfCoins S n).symm false) (List.ofFn p.1) p.2)
          (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then 1 else 0) +
      expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
        if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
          ((halfCoins S n).symm true) (List.ofFn p.1) p.2)
          (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then 1 else 0)) -
      (expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
          if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
            ((halfCoins S n).symm false) (List.ofFn p.1) p.2) ρ'' = true then 1 else 0) +
        expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
          if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
            ((halfCoins S n).symm true) (List.ofFn p.1) p.2) ρ'' = true then 1 else 0)) / 2 =
      expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
        if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
          (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0) -
      expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
        if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
          (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  set v : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) →
      ℝ := fun p => if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
        (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0 with hv
  -- The views, block by block.
  have hview : ∀ (β : Bool) (p : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))),
      ((if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm β) (List.ofFn p.1) p.2)
        (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then (1 : ℝ) else 0) =
        if badHalves S n p.2 then (if β then v p else 1 - v p) else 0) ∧
      ((if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm β) (List.ofFn p.1) p.2) ρ'' = true then (1 : ℝ) else 0) =
        if badHalves S n p.2 then 1 else 0) := by
    intro β p
    have hw : (List.ofFn p.1).drop (ℓ * S.ctLen.eval n) = [] := by
      rw [List.drop_eq_nil_iff, List.length_ofFn]
    have hA : (List.ofFn ((p.2.map Prod.snd).getD (zeroBits _))).length =
        S.msgLen.eval n + S.msgLen.eval n := by rw [List.length_ofFn, hpl]
    have hM : (List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n
        ((p.2.map Prod.snd).getD (zeroBits _)) ((halfCoins S n).symm β))).length =
        S.msgLen.eval n := List.length_ofFn
    have hes : ((List.range ℓ).map fun i => entryL S n sk
        (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
        (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))) =
        (((List.range ℓ).map fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))).map
          fun e : Bool × List Bool => entryL S n sk e.1 e.2) := by
      rw [List.map_map]
      rfl
    rw [realView_eq, hw, List.append_nil, tailDist_blocks S D n _ _ _ hA hM,
      halfDist_blocks S n _ _ _ hA hM, ofFn_drawWith_half S n _ hpl, hes, entryTails_entries,
      List.map_map]
    have hnm : ((List.range ℓ).map ((fun e : Bool × List Bool => (entryL S n sk e.1 e.2).drop 1) ∘
        fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1)))).flatten =
        S.nmOutput sk (p.2.map Prod.fst) (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1)) := by
      rw [nmOutput_eq_entryTails S n ℓ sk _ _ List.length_ofFn, Option.map_map]
      rfl
    rw [hnm]
    exact ⟨tail_indicator _ _ _ _, half_indicator _ _⟩
  -- The coupling, for `D(NM)` and for `1`.
  have hgv := expect_runB_good S atk A q ℓ n hist pk sk r ρ' v
  have hg1 := expect_runB_good S atk A q ℓ n hist pk sk r ρ' (fun _ => 1)
  have hsplit : ∀ (β : Bool) (f : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) →
      ℝ), expect (runB S atk A q ℓ n hist pk sk r ρ' β) (fun p => if badHalves S n p.2 then f p
        else 0) = expect (runB S atk A q ℓ n hist pk sk r ρ' β) f -
          expect (runB S atk A q ℓ n hist pk sk r ρ' β) (fun p => if badHalves S n p.2 then 0
            else f p) := by
    intro β f
    rw [← ProbComp.expect_sub]
    refine congrArg _ (funext fun p => ?_)
    split <;> ring
  simp only [fun β p => (hview β p).1, fun β p => (hview β p).2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hsub0 : expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p => 1 - v p) =
      1 - expect (runB S atk A q ℓ n hist pk sk r ρ' false) v := by
    rw [ProbComp.expect_sub, expect_const]
  have hsub0' : expect (runB S atk A q ℓ n hist pk sk r ρ' false)
      (fun p => if badHalves S n p.2 then 0 else 1 - v p) =
      expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else 1) -
      expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else v p) := by
    rw [← ProbComp.expect_sub]
    refine congrArg _ (funext fun p => ?_)
    split <;> ring
  rw [hsplit false (fun p => 1 - v p), hsplit true v, hsplit false (fun _ => 1),
    hsplit true (fun _ => 1), hsub0, hsub0', expect_const, expect_const, hgv, hg1]
  ring

end RealIdentity

/-- The ideal identity on an abstract parameter `A` and verdict `t`. -/
private theorem ideal_key (A : List Bool) (L : ℕ) (t : Bool) :
    ((if (if decide (A.take L = A.drop L) then false
        else (t == decide ((if false = true then A.drop L else A.take L) = A.drop L))) = true
        then (1 : ℝ) else 0) +
      if (if decide (A.take L = A.drop L) then false
        else (t == decide ((if true = true then A.drop L else A.take L) = A.drop L))) = true
        then 1 else 0) =
      if (!decide (A.take L = A.drop L)) = true then 1 else 0 := by
  by_cases hb : A.take L = A.drop L
  · simp [hb]
  · cases t <;> simp [hb]

/-- **The ideal identity, pointwise:** on the ideal experiment's views with the two coins, `D'`
accepts with indicator sum equal to `D''`'s (whatever the simulator's output and state): when
`m₀ ≠ m₁`, exactly one coin makes `[D(…) = 1] == [m = m₁]` hold, since `m = m_β`. -/
theorem ideal_identity (n ℓ : ℕ) (sk : List Bool) (w : List Bool)
    (sa : Option (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) (rD : D.Coins n)
    (ρ'' : (halfDist S).Coins n) (hw : w.length = ℓ * (S.ctLen.eval n + 1)) :
    ((if (tailDist S D).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm false) w sa) (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true
        then 1 else 0 : ℝ) +
      if (tailDist S D).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm true) w sa) (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true
        then 1 else 0) =
      if (halfDist S).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm false) w sa) ρ'' = true then 1 else 0 := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hA : (List.ofFn (sa.getD (zeroBits _))).length = S.msgLen.eval n + S.msgLen.eval n := by
    rw [List.length_ofFn, hpl]
  have hM : ∀ β, (List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n (sa.getD (zeroBits _))
      ((halfCoins S n).symm β))).length = S.msgLen.eval n := fun _ => List.length_ofFn
  have hdrop : w.drop (ℓ * (S.ctLen.eval n + 1)) = [] := by rw [List.drop_eq_nil_iff, hw]
  rw [idealView_eq, idealView_eq, hdrop, List.append_nil, List.append_nil,
    tailDist_blocks S D n _ _ _ hA (hM false), tailDist_blocks S D n _ _ _ hA (hM true),
    halfDist_blocks S n _ _ _ hA (hM false), ofFn_drawWith_half S n _ hpl,
    ofFn_drawWith_half S n _ hpl]
  exact ideal_key _ _ _

end TCSlib.Cryptography.Composability.NMSim
