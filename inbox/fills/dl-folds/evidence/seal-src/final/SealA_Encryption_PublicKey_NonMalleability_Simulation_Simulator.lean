/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The simulator of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message), under CPA.
The simulator runs the SIM adversary `A` on `pk`, answering `Dec` with `⊥`. On `A`'s first
challenge `a` it asks its only query `a`, gets `h(m)`, draws `m̃ = M(a; ρ̃)` with its own coins
(with `M`'s advice, read from its input `⟨pk, α_M⟩`), encrypts `ỹ = Enc_pk(m̃; re)` with its own
coins, answers `⟨ỹ, h(m)⟩` and records it. It outputs `A`'s ciphertexts, each flagged `COPY` iff it
equals `ỹ`, and `σ`.

It is the challenge handler (`chalHandler`) with the parameters `simParams`. Against the history
oracle, its run is `A`'s run against the hybrid oracle `rImpl … true … ρ ρ̃ (some re)`, which
encrypts an independent draw (`simComp_abs`); and the ideal experiment's view of its output is the
hybrid's view of `A`'s (`idealView_simOut`).

## Main definitions

* `NMSim.simMsg`, `NMSim.simCt`: `m̃` and `ỹ` read from a round input.
* `NMSim.flagF`, `NMSim.simOutL`, `NMSim.simFin`: the finalization.
* `NMSim.simParams`: the parameters of the simulator's handler.

## Main results

* `NMSim.simFinish`, `NMSim.simComp_abs`, `NMSim.idealView_simOut`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal A (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean`, with every seal candidate of its
full TCSlib import closure (1319 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acEnc _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHyb _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acSeedTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acStLen _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl_adaptiveIndImpl.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.expect_tapeImpl.match_1_4 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.extTape _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.simulate_tapeImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.tapeImpl _root_.TCSlib.Cryptography.Composability.Attack.ofNat _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_some_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_3 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_5 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_7 _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.length_of_firstQ_eq_some.match_1_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.NMSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero.match_1_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmDecrypt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmOutput _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nthCt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.ofPadded _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.NMCCA2.decBlock _root_.TCSlib.Cryptography.Composability.NMCCA2.decHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encCt _root_.TCSlib.Cryptography.Composability.NMCCA2.encHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encTape _root_.TCSlib.Cryptography.Composability.NMCCA2.guessBit _root_.TCSlib.Cryptography.Composability.NMCCA2.guessDist _root_.TCSlib.Cryptography.Composability.NMCCA2.logEmit _root_.TCSlib.Cryptography.Composability.NMSim.chalHandler _root_.TCSlib.Cryptography.Composability.NMSim.chalHandler_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.chalHandler_costBoundedBy.match_1_3 _root_.TCSlib.Cryptography.Composability.NMSim.chalRun _root_.TCSlib.Cryptography.Composability.NMSim.chalState _root_.TCSlib.Cryptography.Composability.NMSim.chalState.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.chunkEmit _root_.TCSlib.Cryptography.Composability.NMSim.chunkMap _root_.TCSlib.Cryptography.Composability.NMSim.chunkStep _root_.TCSlib.Cryptography.Composability.NMSim.drawWith _root_.TCSlib.Cryptography.Composability.NMSim.encWith _root_.TCSlib.Cryptography.Composability.NMSim.entryL _root_.TCSlib.Cryptography.Composability.NMSim.expect_simulate_rImpl_eager.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.histImpl _root_.TCSlib.Cryptography.Composability.NMSim.histWith _root_.TCSlib.Cryptography.Composability.NMSim.hybAcc _root_.TCSlib.Cryptography.Composability.NMSim.idealAcc _root_.TCSlib.Cryptography.Composability.NMSim.idealView _root_.TCSlib.Cryptography.Composability.NMSim.rImpl _root_.TCSlib.Cryptography.Composability.NMSim.rImpl.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl.match_3 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_allOutputs_isSome.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_eq_of_msgLen_eq_zero.match_1_2 _root_.TCSlib.Cryptography.Composability.NMSim.rImpl_false_coins.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.realAcc _root_.TCSlib.Cryptography.Composability.NMSim.realView _root_.TCSlib.Cryptography.Composability.NMSim.snmDin _root_.TCSlib.Cryptography.Composability.NMSim.snmDin.match_1 _root_.TCSlib.Cryptography.Composability.NMSim.snmDin_eval_inLens.match_1_1 _root_.TCSlib.Cryptography.Composability.NMSim.snmDout _root_.TCSlib.Cryptography.Composability.NMSim.snmDout_eval_outLens.match_1_1 _root_.TCSlib.Cryptography.Composability.isPadded _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Composability.padDecFun _root_.TCSlib.Cryptography.Composability.padEncFun _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquivPoly _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GGMRed.IsQ _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.advPoly _root_.TCSlib.Cryptography.GGMRed.adviceOf _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.ansMap _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinPoly _root_.TCSlib.Cryptography.GGMRed.coinStr _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.concrete _root_.TCSlib.Cryptography.GGMRed.concrete_iterate.match_1_1 _root_.TCSlib.Cryptography.GGMRed.encState _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.firstRound _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.nextQ _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.orbit_eq_encState.match_1_1 _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.prefMap _root_.TCSlib.Cryptography.GGMRed.pureAt _root_.TCSlib.Cryptography.GGMRed.pureStep _root_.TCSlib.Cryptography.GGMRed.pureStep.match_1 _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rawInput _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.stream _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.valStr _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.IInv _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom.match_1 _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.gB _root_.TCSlib.Cryptography.Games.EffFill.gC _root_.TCSlib.Cryptography.Games.EffFill.gCur _root_.TCSlib.Cryptography.Games.EffFill.gLc _root_.TCSlib.Cryptography.Games.EffFill.gLin _root_.TCSlib.Cryptography.Games.EffFill.gO _root_.TCSlib.Cryptography.Games.EffFill.gPh _root_.TCSlib.Cryptography.Games.EffFill.gS _root_.TCSlib.Cryptography.Games.EffFill.hAct _root_.TCSlib.Cryptography.Games.EffFill.hBound _root_.TCSlib.Cryptography.Games.EffFill.hCtx _root_.TCSlib.Cryptography.Games.EffFill.hMove _root_.TCSlib.Cryptography.Games.EffFill.hNext _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.hRes _root_.TCSlib.Cryptography.Games.EffFill.hRounds _root_.TCSlib.Cryptography.Games.EffFill.hStart _root_.TCSlib.Cryptography.Games.EffFill.hState _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iAnsLen _root_.TCSlib.Cryptography.Games.EffFill.iAsk _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallAct _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCallNext _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinAct _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinNext _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iFixBound _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iNext _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iTree _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_le_length_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.relabel _root_.TCSlib.Cryptography.Games.EffFill.relabelEmit _root_.TCSlib.Cryptography.Games.EffFill.relabelN _root_.TCSlib.Cryptography.Games.EffFill.relabelN_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finA _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.InteractiveHandler.rAns _root_.TCSlib.Cryptography.Games.InteractiveHandler.rCnt _root_.TCSlib.Cryptography.Games.InteractiveHandler.rI _root_.TCSlib.Cryptography.Games.InteractiveHandler.rL _root_.TCSlib.Cryptography.Games.InteractiveHandler.rS _root_.TCSlib.Cryptography.Games.InteractiveHandler.rU _root_.TCSlib.Cryptography.Games.InteractiveHandler.rW _root_.TCSlib.Cryptography.Games.InteractiveHandler.rX _root_.TCSlib.Cryptography.Games.InteractiveHandler.rZ _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.answer.match_1 _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.ansRead _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.buildComp_singleCodec.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.cntRead _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.fwdHandler _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.iterEmit _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.singleCodec _root_.TCSlib.Cryptography.Games.singleCodec.match_1 _root_.TCSlib.Cryptography.Games.toHist _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PublicKeyScheme.Secure _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.PublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_prf_of_exists_prg.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmPRF _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.hybridAdv _root_.TCSlib.Cryptography.hybridCoins _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridPlant _root_.TCSlib.Cryptography.hybridPre _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.length_flatten_ofFn.match_1_1 _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multiDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.singleDist _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs

open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquiv_ofFn ofFn_padFin_eq_padL)
open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rZ_input rW_input rX_input rAns_input
  rU_finInput rS_finInput finA_finInput polyTimeComputable_rU polyTimeComputable_rZ
  polyTimeComputable_rW polyTimeComputable_rS polyTimeComputable_rX polyTimeComputable_rAns
  polyTimeComputable_finA)

variable (S : FixedLengthPKScheme) (samp : NUPPT)

/-! ### The dummy challenge -/

/-- The dummy message `m̃ = M(a; ρ̃)` read in a round `w`: with `n = |rU w|`, `a = rX w`, the
advice `α = snd (rZ w)` and `ρ̃` the first `coins(n)` bits of the seed, `padL msgLen(n)` of `M`'s
output on `layout 1^n a α ρ̃`. -/
def simMsg (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
    (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
      ((rW w).take (samp.coins.eval (rU w).length))))

/-- `simMsg S samp w = padL msgLen(n) (M.output (layout 1^n a α ρ̃))`. -/
theorem simMsg_eq (w : List Bool) :
    simMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
      (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
        ((rW w).take (samp.coins.eval (rU w).length)))) := rfl

/-- The dummy challenge `ỹ = Enc_pk(m̃; re)` read in a round `w`: `pk = fst (rZ w)`, `re` the seed
after `ρ̃`, `padL ctLen(n)` of `Enc`'s output on `⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩`. -/
def simCt (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (rU w)
      (pairEncode (pairFstD (rZ w)) (simMsg S samp w))) [])
      ((rW w).drop (samp.coins.eval (rU w).length))))

/-- `simCt S samp w = padL ctLen(n) (Enc.output ⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩)`. -/
theorem simCt_eq (w : List Bool) :
    simCt S samp w = EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
      (S.enc.output (pairEncode (pairEncode (pairEncode (rU w)
        (pairEncode (pairFstD (rZ w)) (simMsg S samp w))) [])
        ((rW w).drop (samp.coins.eval (rU w).length)))) := rfl

/-- The dummy message is polynomial-time. -/
theorem polyTimeComputable_simMsg : PolyTimeComputable (simMsg S samp) := by
  have hU := polyTimeComputable_rU
  have hZ := polyTimeComputable_rZ
  have hW := polyTimeComputable_rW
  have hQ := polyTimeComputable_rX
  have hρ : PolyTimeComputable fun w => (rW w).take (samp.coins.eval (rU w).length) :=
    ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hU hQ (polyTimeComputable_pairSndD.comp hZ) hρ))

/-- The dummy challenge is polynomial-time. -/
theorem polyTimeComputable_simCt : PolyTimeComputable (simCt S samp) := by
  have hU := polyTimeComputable_rU
  have hZ := polyTimeComputable_rZ
  have hW := polyTimeComputable_rW
  have hre : PolyTimeComputable fun w => (rW w).drop (samp.coins.eval (rU w).length) :=
    ((polyTimeComputable_pairDropPoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
    (((hU.pairEncode ((polyTimeComputable_pairFstD.comp hZ).pairEncode
      (polyTimeComputable_simMsg S samp))).pairEncode (polyTimeComputable_const [])).pairEncode
      hre))

/-! ### The finalization -/

/-- **The flagged entry** of a ciphertext `c`, on the context `⟨1^n, s⟩` with the state
`s = [flag] ‖ ỹ ‖ …`: `[flag ∧ c = ỹ]` followed by `c`. -/
def flagF (ctx c : List Bool) : List Bool :=
  ((pairSndD ctx).headD false &&
    decide (c = ((pairSndD ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) :: c

/-- `flagF S ctx c = [snd ctx's flag ∧ c = ỹ] ++ c`. -/
theorem flagF_eq (ctx c : List Bool) :
    flagF S ctx c = ((pairSndD ctx).headD false &&
      decide (c = ((pairSndD ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) :: c := rfl

/-- The flagged entry is polynomial-time, as a function of `⟨ctx, c⟩`. -/
theorem polyTimeComputable_flagF :
    PolyTimeComputable fun z => flagF S (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hy : PolyTimeComputable fun z =>
      ((pairSndD (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly S.ctLen).comp ((hF.comp hF).pairEncode
      (polyTimeComputable_tail.comp (hD.comp hF)))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq : PolyTimeComputable fun z => [decide (pairSndD z =
      ((pairSndD (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length))] :=
    (polyTimeComputable_pairEq.comp (hD.pairEncode hy)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact BinArith.polyTimeComputable_cons
    (polyTimeComputable_and (polyTimeComputable_headD.comp (hD.comp hF)) heq) hD

/-- **The simulator's output** at parameter `n`, for the state string `st` and `A`'s output `a`
(`r(n)` ciphertexts, then `σ`): the flagged entries `flagF ⟨1^n, st⟩ c_i`, then `σ`. -/
def simOutL (r : PolyExpr) (n : ℕ) (st a : List Bool) : List Bool :=
  ((List.range (r.eval n)).map fun i =>
    flagF S (pairEncode (List.replicate n true) st) (coinBlock (S.ctLen.eval n) i a)).flatten ++
  a.drop (r.eval n * S.ctLen.eval n)

/-- `simOutL S r n st a = (flagF ⟨1^n, st⟩ c_0 ++ ⋯ ++ flagF ⟨1^n, st⟩ c_{r-1}) ++ σ`. -/
theorem simOutL_eq (r : PolyExpr) (n : ℕ) (st a : List Bool) :
    simOutL S r n st a =
      ((List.range (r.eval n)).map fun i =>
        flagF S (pairEncode (List.replicate n true) st) (coinBlock (S.ctLen.eval n) i a)).flatten ++
      a.drop (r.eval n * S.ctLen.eval n) := rfl

/-- **The simulator's finalization round**: `⟨[true], F ‖ a.drop (r·ctLen)⟩`, with no outer query,
where `F` is `chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` (the flagged entries) when
`ctLen(n) > 0`, and the `r` flags `[flag]` when `ctLen(n) = 0` (every ciphertext is then empty, and
equal to `ỹ`). -/
def simFin (r : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode [true]
    ((if decide (List.replicate (S.ctLen.eval (rU w).length) true = []) then
        (if (rS w).headD false then List.replicate (r.eval (rU w).length) true
          else List.replicate (r.eval (rU w).length) false)
      else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (rU w) (rS w))
        ((finA w).take ((r.mul S.ctLen).eval (rU w).length)))) ++
    (finA w).drop ((r.mul S.ctLen).eval (rU w).length))

/-- `simFin S r w = ⟨[true], F ‖ a.drop (r·ctLen)⟩`, with `F = flag^r` if `ctLen(n) = 0` and
`F = chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` otherwise. -/
theorem simFin_eq (r : PolyExpr) (w : List Bool) :
    simFin S r w = pairEncode [true]
      ((if decide (List.replicate (S.ctLen.eval (rU w).length) true = []) then
          (if (rS w).headD false then List.replicate (r.eval (rU w).length) true
            else List.replicate (r.eval (rU w).length) false)
        else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (rU w) (rS w))
          ((finA w).take ((r.mul S.ctLen).eval (rU w).length)))) ++
      (finA w).drop ((r.mul S.ctLen).eval (rU w).length)) := rfl

/-- The finalization round is polynomial-time. -/
theorem polyTimeComputable_simFin (r : PolyExpr) : PolyTimeComputable (simFin S r) := by
  have hU := polyTimeComputable_rU
  have hA := polyTimeComputable_finA
  have hS := polyTimeComputable_rS
  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (rU w).length) :=
    ((polyTimeComputable_pairTakePoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (rU w).length) :=
    ((polyTimeComputable_pairDropPoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact (polyTimeComputable_const [true]).pairEncode
    ((polyTimeComputable_ite (polyTimeComputable_isNil.comp
        ((polyTimeComputable_unaryPoly S.ctLen).comp hU))
      (polyTimeComputable_ite (polyTimeComputable_headD.comp hS)
        ((polyTimeComputable_unaryPoly r).comp hU) (EnsembleLemmas.polyTimeComputable_zeros r hU))
      ((polyTimeComputable_chunkMap S.ctLen (polyTimeComputable_flagF S)).comp
        ((hU.pairEncode hS).pairEncode htake))).append hdrop)

/-- Every flagged entry has one bit more than its ciphertext. -/
theorem length_flagF (ctx c : List Bool) : (flagF S ctx c).length = c.length + 1 := by
  rw [flagF_eq, List.length_cons]

/-- **The finalization round on a finalization input** (for `A`'s output of `r·ctLen + sl` bits)
returns `⟨[true], simOutL …⟩`.

**Proof sketch.** Read the fields of the input in `simFin_eq` and split on `ctLen(n)`. If
`ctLen(n) = 0`, every chunk is empty and equals `ỹ`, so every flagged entry is `[flag]` and the
`r` entries flatten to `flag^r`. Otherwise cut `a.take (r·ctLen)` into its `r` chunks of
`ctLen(n)` bits (`take_eq_flatten_chunkAt`, `length_coinBlock`); `chunkMap_flatten` maps
`flagF` over them, which is `simOutL_eq`. -/
theorem simFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    simFin S r (InteractiveHandler.finInput n z ω s a L) =
      pairEncode [true] (simOutL S r n s a) := by
  have hU := rU_finInput n z ω s a L
  have hA := finA_finInput n z ω s a L
  rw [simFin_eq, hU, hA, rS_finInput, List.length_replicate, PolyExpr.eval_mul, simOutL_eq]
  congr 2
  by_cases hct : S.ctLen.eval n = 0
  · rw [if_pos (by rw [hct, List.replicate_zero]; rfl)]
    have hent : ∀ i,
        flagF S (pairEncode (List.replicate n true) s) (coinBlock (S.ctLen.eval n) i a) =
          [s.headD false] := by
      intro i
      rw [flagF_eq, pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, hct,
        coinBlock_eq, List.take_zero, List.take_zero, decide_eq_true rfl, Bool.and_true]
    have hrep : ∀ (b : Bool) (m : ℕ), ((List.range m).map fun _ => [b]).flatten =
        List.replicate m b := by
      intro b m
      induction m with
      | zero => rfl
      | succ m ih => rw [List.range_succ, List.map_append, List.flatten_append, ih,
          List.map_singleton, List.flatten_singleton, List.replicate_succ']
    simp only [hent]
    rw [hrep]
    cases s.headD false <;> rfl
  · rw [if_neg (by rw [decide_eq_true_eq, List.replicate_eq_nil_iff]; exact hct),
      take_eq_flatten_chunkAt,
      chunkMap_flatten _ _ n s _ (fun ch hch => ?_) (Nat.pos_of_ne_zero hct), List.map_map]
    · rfl
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
      rw [List.mem_range] at hi
      refine length_coinBlock ?_
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega

/-! ### The handler -/

variable (pl hl : PolyExpr)

/-- **The parameters of the simulator's handler** (on the real experiment's oracles with parameter
length `pl` and history length `hl`; one outer oracle, the history oracle): the first challenge `a`
asks `a`; it answers `⟨ỹ, h⟩` with `ỹ = simCt` and `h` the outer answer. The seed is `ρ̃ ‖ re`
(the sampler's and `Enc`'s coins), the adversary runs on `pk = fst z`, the output is `r` flagged
entries and `σ` (`r·(ctLen + 1) + sl` bits, `simFin`), and the finalization may ask one query (it
asks none), so that T2's budget is at least `1`. -/
def simParams (r sl : PolyExpr) : ChalParams S pl hl 1 (fun _ => pl) (fun _ => hl) where
  j := 0
  seedLen := samp.coins.add S.enc.coins
  advIn ctx := pairFstD (pairFstD (pairSndD ctx))
  advIn_poly := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  qry w := EnsembleLemmas.padL (pl.eval (rU w).length) (rX w)
  qry_poly := EnsembleLemmas.polyTimeComputable_padL pl polyTimeComputable_rU
    polyTimeComputable_rX
  qry_len _ := EnsembleLemmas.length_padL _ _
  ansY := simCt S samp
  ansY_poly := polyTimeComputable_simCt S samp
  ansY_len _ := EnsembleLemmas.length_padL _ _
  ansH w := EnsembleLemmas.padL (hl.eval (rU w).length) (rAns w)
  ansH_poly := EnsembleLemmas.polyTimeComputable_padL hl polyTimeComputable_rU
    polyTimeComputable_rAns
  ansH_len _ := EnsembleLemmas.length_padL _ _
  outLen := (r.mul (S.ctLen.add (.const 1))).add sl
  finCall := .const 1
  finRun := simFin S r
  finRun_poly := polyTimeComputable_simFin S r

attribute [simps (config := { isSimp := false }) j seedLen advIn qry ansY ansH outLen finCall
  finRun] simParams

section Run

variable (r sl : PolyExpr) (n : ℕ)

/-- The simulator's seed is `ρ̃ ‖ re`: `seedLen = samp.coins + enc.coins`. -/
theorem simParams_seedLen_handler :
    (chalHandler (simParams S samp pl hl r sl)).seedLen = samp.coins.add S.enc.coins := by
  rw [chalHandler_seedLen, simParams_seedLen]

/-- The simulator outputs `r·(ctLen + 1) + sl` bits. -/
theorem simParams_outLen_eval :
    (chalHandler (simParams S samp pl hl r sl)).outLen.eval n =
      r.eval n * (S.ctLen.eval n + 1) + sl.eval n := by
  rw [chalHandler_outLen, simParams_outLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_add,
    PolyExpr.eval_const]

/-- The simulator runs `A` on `pk`: `advInput n ⟨pk, α⟩ ω = pk`. -/
theorem simParams_advInput (pk α : List Bool)
    (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool) :
    (chalHandler (simParams S samp pl hl r sl)).advInput n (pairEncode pk α) ω = pk := by
  rw [InteractiveHandler.advInput_eq, chalHandler_advIn, simParams_advIn, seedIn_eq,
    pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode]

/-- **The simulator's finalization** on `A`'s output `a` (`r·ctLen + sl` bits) returns
`simOutL` of the state and `a`, asking nothing. -/
theorem simFinish (z : List Bool)
    (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool)
    (s : Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) (hd : d = r.eval n * S.ctLen.eval n + sl.eval n) :
    (chalHandler (simParams S samp pl hl r sl)).finish n z ω s a =
      .pure (padFin _ (simOutL S r n (List.ofFn s) (List.ofFn a))) := by
  have ha : (List.ofFn a).length = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [List.length_ofFn, hd]
  refine InteractiveHandler.finish_of_ret_padFin _ n z ω s a _ ?_ ?_
  · rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
      length_flatten_map_range (S.ctLen.eval n + 1) _ _ fun i hi => ?_]
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [length_flagF, length_coinBlock (by
        rw [ha]
        have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
        omega)]
  · rw [chalHandler_finRun, simParams_finRun]
    exact simFin_finInput S r sl n z _ _ _ _ ha

end Run

/-! ### The simulator against the history oracle -/

section Composite

variable (hist : List Bool → List Bool) (r sl : PolyExpr) (n : ℕ)

/-- **The abstraction of the hybrid's state** to the simulator's and the history oracle's: no
challenge is `(empty, none)`; the challenge `y` on `a` is `(⟨y, h(M(a; ρ)), a⟩, some a)`. -/
def simAbs (ρ : samp.Coins n) :
    Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) →
      (Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool) ×
        Option (Fin (pl.eval n) → Bool)
  | none => (chalState (simParams S samp pl hl r sl) n none, none)
  | some (y, a) => (chalState (simParams S samp pl hl r sl) n
      (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)), some a)

/-- `simAbs … none = (chalState none, none)`. -/
theorem simAbs_none (ρ : samp.Coins n) :
    simAbs S samp pl hl hist r sl n ρ none =
      (chalState (simParams S samp pl hl r sl) n none, none) := rfl

/-- `simAbs … (some (y, a)) = (chalState (some (y, h(M(a; ρ)), a)), some a)`. -/
theorem simAbs_some (ρ : samp.Coins n) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    simAbs S samp pl hl hist r sl n ρ (some (y, a)) =
      (chalState (simParams S samp pl hl r sl) n
        (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)),
        some a) := rfl

/-- The history oracle's part of the abstraction is the recorded parameter. -/
theorem simAbs_snd (ρ : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    (simAbs S samp pl hl hist r sl n ρ s).2 = s.map Prod.snd := by
  cases s with
  | none => rfl
  | some ya => rfl

/-- **The dummy challenge in a round of the simulator** (input `⟨pk, M.advice n⟩`, seed
`ρ̃ ‖ re`, on
the parameter `x`): `simCt … = ⟦Enc_pk(M(x; ρ̃); re)⟧`. -/
theorem simCt_input (pk : List Bool) (ρ' : samp.Coins n) (re : S.enc.Coins n) (s : List Bool)
    (x : Fin ((snmDin S pl 1).eval n) → Bool) (L : List Bool) :
    simCt S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
        (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s
        (1 : Fin 2) (List.ofFn x) L) =
      List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ') re) := by
  have hU := rU_input (k := 2) n (pairEncode pk (samp.advice n))
    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
    (List.ofFn x) L
  have hZ := rZ_input (k := 2) n (pairEncode pk (samp.advice n))
    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
    (List.ofFn x) L
  have hW := rW_input (k := 2) n (pairEncode pk (samp.advice n))
    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
    (List.ofFn x) L
  have hQ := rX_input (k := 2) n (pairEncode pk (samp.advice n))
    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
    (List.ofFn x) L
  have hxl : (List.ofFn x).length = pl.eval n := by
    rw [List.length_ofFn]
    show (snmDin S pl 1).eval n = _
    rw [snmDin_one]
  rw [simCt_eq, simMsg_eq, hU, hZ, hW, hQ, List.length_replicate, pairFstD_pairEncode,
    pairSndD_pairEncode, seedEquiv_ofFn,
    List.take_left' (length_ofFn_coins samp n ρ'), List.drop_left' (length_ofFn_coins samp n ρ'),
    encWith_eq, drawWith_eq, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
    ofFn_padFin_of_length hxl, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]

/-- **The simulator against the history oracle is the hybrid with an independent draw:** for the
input `⟨pk, M.advice n⟩` and the seed `ρ̃ ‖ re`, the composition of the history oracle (coins `ρ`)
with the simulator's handler, from the abstracted state, is `rImpl … true … ρ ρ̃ (some re)` (under
CPA) with its state abstracted (`simAbs`).

**Proof sketch.** Query by query: `Dec` is `⊥` on both sides (`chalHandler_impl_dec`,
`rImpl_dec_cpa`); a repeated challenge repeats `⟨y, h(M(a; ρ))⟩` (`chalHandler_impl_some`,
`rImpl_some`); a first challenge asks `a`, receives `h(M(a; ρ))` (`histImpl_eq`) and answers
`⟨Enc_pk(M(a; ρ̃); re), h(M(a; ρ))⟩` (`chalHandler_impl_none`, `simCt_input`,
`rImpl_none_eager`). -/
theorem simComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (i : Fin 2)
    (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    ((histImpl S samp pl hl hist n ρ).comp ((chalHandler (simParams S samp pl hl r sl)).impl n
        (pairEncode pk (samp.advice n))
        (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))))
        i x (simAbs S samp pl hl hist r sl n ρ s) =
      (rImpl S .cpa true samp pl hl hist n pk sk ρ ρ' (some re) i x s).bind
        fun p => .pure (p.1, simAbs S samp pl hl hist r sl n ρ p.2) := by
  rw [QueryImpl.comp_apply]
  match i, x, s with
  | 0, x, none =>
    rw [simAbs_none, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, simAbs_none]
  | 0, x, some (y, a) =>
    rw [simAbs_some, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, simAbs_some]
  | 1, x, some (y, a) =>
    rw [simAbs_some, chalHandler_impl_some, simulate_pure, OracleComp.pure_bind, rImpl_some,
      OracleComp.pure_bind, simAbs_some]
  | 1, x, none =>
    have hxl : (List.ofFn x).length = pl.eval n := by
      rw [List.length_ofFn]
      show (snmDin S pl 1).eval n = _
      rw [snmDin_one]
    have hq : ∀ (s' : List Bool) (L : List Bool),
        (simParams S samp pl hl r sl).qry
          (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s'
          (1 : Fin 2) (List.ofFn x) L) = List.ofFn (padFin (pl.eval n) (List.ofFn x)) := by
      intro s' L
      rw [simParams_qry, rU_input (k := 2) n _ _ s' 1 _ L,
        rX_input (k := 2) n _ _ s' 1 _ L, List.length_replicate,
        ofFn_padFin_eq_padL]
    have hH : ∀ (s' q : List Bool) (y : Fin (hl.eval n) → Bool),
        (simParams S samp pl hl r sl).ansH
          (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s'
          (1 : Fin 2) (List.ofFn x) (pairEncode (pairEncode (List.replicate 0 true)
            (pairEncode q (List.ofFn y))) [])) = List.ofFn y := by
      intro s' q y
      rw [simParams_ansH, rU_input (k := 2) n _ _ s' 1 _ _, List.length_replicate,
        rAns_input, EnsembleLemmas.padL_eq]
      exact List.take_left' List.length_ofFn
    rw [simAbs_none, chalHandler_impl_none, simulate_query, histImpl_eq, OracleComp.pure_bind,
      simulate_pure, OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind, simAbs_some,
      if_pos rfl]
    simp only [simParams_j, simParams_ansY, Fin.val_zero, hq, hH, simCt_input, Option.getD_none,
      padFin_ofFn (padFin (pl.eval n) (List.ofFn x)),
      padFin_ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ') re),
      padFin_ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ))]

/-- **The ideal view of the simulator's output is the hybrid's view of `A`'s output:** for `A`'s
output `a` (`r·ctLen + sl` bits) and the hybrid's final state `s`, `idealView` of the simulator's
output (flags from the abstracted state) with the history oracle's state is `realView` of `a` and
`s`.

**Proof sketch.** Entry `i` of the output is `flagF ⟨1^n, st⟩ c_i` (`coinBlock_flatten_append`),
whose flag is `[c_i = y]` for the recorded `y` and `false` without a challenge
(`headD_ofFn_chalState`, `ofFn_chalState_some`), as `realView`'s copy test; `σ` is the tail
(`drop_flatten_append`). -/
theorem idealView_simOut (sk : List Bool) (ρ : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (a : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    idealView S samp pl n (r.eval n) sk ρ (List.ofFn (padFin
        ((chalHandler (simParams S samp pl hl r sl)).outLen.eval n)
        (simOutL S r n (List.ofFn (simAbs S samp pl hl hist r sl n ρ s).1) a)))
        (simAbs S samp pl hl hist r sl n ρ s).2 =
      realView S samp pl n (r.eval n) sk ρ a s := by
  set st := List.ofFn (simAbs S samp pl hl hist r sl n ρ s).1 with hst
  have hc : ∀ i < r.eval n, (coinBlock (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
    length_coinBlock (by
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega)
  have hg : ∀ i < r.eval n, (flagF S (pairEncode (List.replicate n true) st)
      (coinBlock (S.ctLen.eval n) i a)).length = S.ctLen.eval n + 1 := fun i hi => by
    rw [length_flagF, hc i hi]
  have hlen : (simOutL S r n st a).length =
      (chalHandler (simParams S samp pl hl r sl)).outLen.eval n := by
    rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
      length_flatten_map_range (S.ctLen.eval n + 1) _ _ hg, Nat.mul_add, Nat.mul_one]
    omega
  rw [ofFn_padFin_of_length hlen, simAbs_snd, idealView_eq, realView_eq, simOutL_eq,
    drop_flatten_append _ _ _ hg]
  congr 3
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [coinBlock_flatten_append _ _ _ hg _ _ hi, flagF_eq, List.headD_cons, List.tail_cons,
    pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
  congr 1
  cases s with
  | none =>
    rw [hst, simAbs_none, headD_ofFn_chalState]
    simp
  | some ya =>
    obtain ⟨y, a'⟩ := ya
    rw [hst, simAbs_some, ofFn_chalState_some, List.headD_cons, List.drop_one, List.tail_cons,
      List.append_assoc, List.take_left' List.length_ofFn]
    simp only [Bool.true_and, Option.map_some, Option.some.injEq, decide_eq_decide]
    exact eq_comm

end Composite

/-! ### The ideal experiment is the hybrid `H_true` -/

section Ideal

variable (hist : List Bool → List Bool) (A : NUPPT) (q r sl : PolyExpr)

/-- **One run of the simulator is one run of the hybrid `H_true`:** let `Sim₀` be T2's machine of
the simulator's handler (coin bijection `φ`). For the input `⟨pk, M.advice n⟩`, coins
`φ (ρ̃ ‖ re, rA)` and budget `1`, the law of `F(idealView)` over `Sim₀`'s run against the history
oracle (coins `ρ`) is the law of `F(realView)` over `A`'s run (coins `rA`) against
`rImpl … true … ρ ρ̃ (some re)`.

**Proof sketch.** Transport the output length (`expect_toCompOn_outLen`); the run at budget `1` is
the run at T2's budget (`NUPPT.toCompOn_budget_eq`: the handler asks at most one query,
`chalHandler_costBoundedBy`, and its finalization none, `simFinish`); T2's equation; the
composition of the two simulations (`simulate_bind`, `simulate_comp`) is the hybrid's run through
the abstraction (`simulate_eq_of_abs`, `simComp_abs`); the views agree (`idealView_simOut`). -/
theorem simRun_eq (Sim₀ : NUPPT) (n : ℕ)
    (φ : (Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool) × A.Coins n ≃
      Sim₀.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool)
      (rA : A.Coins n),
      (simulate ((chalHandler (simParams S samp pl hl r sl)).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (((r.mul S.ctLen).add sl).eval n)) n (q.eval n)
            ((chalHandler (simParams S samp pl hl r sl)).advInput n z ω) rA)
          ((chalHandler (simParams S samp pl hl r sl)).init n)).bind
          (fun res => (chalHandler (simParams S samp pl hl r sl)).finish n z ω res.2 res.1) =
        Sim₀.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          ((chalHandler (simParams S samp pl hl r sl)).outLen.eval n)) n
          (q.eval n * (chalHandler (simParams S samp pl hl r sl)).perCall.eval n +
            (chalHandler (simParams S samp pl hl r sl)).finCall.eval n) z (φ (ω, rA)))
    (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (rA : A.Coins n)
    (F : List Bool → ℝ) :
    ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
        (Sim₀.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          (r.eval n * (S.ctLen.eval n + 1) + sl.eval n)) n 1 (pairEncode pk (samp.advice n))
          (φ (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re), rA))) none)
        (fun p => F (idealView S samp pl n (r.eval n) sk ρ (List.ofFn p.1) p.2)) =
      ProbComp.expect (simulate (rImpl S .cpa true samp pl hl hist n pk sk ρ ρ' (some re))
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r.eval n * S.ctLen.eval n + sl.eval n)) n (q.eval n) pk rA) none)
        (fun p => F (realView S samp pl n (r.eval n) sk ρ (List.ofFn p.1) p.2)) := by
  set ω := seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re) with hω
  set z := pairEncode pk (samp.advice n) with hz
  have hdα : ((r.mul S.ctLen).add sl).eval n = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have hfin : ∀ (st : Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool)
      (a : Fin (((r.mul S.ctLen).add sl).eval n) → Bool),
      (chalHandler (simParams S samp pl hl r sl)).finish n z ω st a =
        .pure (padFin _ (simOutL S r n (List.ofFn st) (List.ofFn a))) :=
    fun st a => simFinish S samp pl hl r sl n z ω st a hdα
  -- The output length, the budget and T2.
  refine (expect_toCompOn_outLen _ Sim₀ n 1 z _ none
    (simParams_outLen_eval S samp pl hl r sl n).symm
    (fun p => F (idealView S samp pl n (r.eval n) sk ρ p.1 p.2))).trans ?_
  have hK : 1 ≤ q.eval n * (chalHandler (simParams S samp pl hl r sl)).perCall.eval n +
      (chalHandler (simParams S samp pl hl r sl)).finCall.eval n := by
    rw [chalHandler_finCall, simParams_finCall, PolyExpr.eval_const]
    omega
  rw [NUPPT.toCompOn_budget_eq Sim₀ _ n 1 _ z (φ (ω, rA)) hK (by
    rw [← hφ z ω rA, chalHandler_init]
    refine OracleComp.CostBoundedBy.bind (q₁ := 1) (q₂ := 0) (chalHandler_costBoundedBy _ n z ω _)
      fun res => ?_
    rw [hfin]
    exact OracleComp.costBoundedBy_pure _ _ _), ← hφ z ω rA, simParams_advInput, chalHandler_init,
    simulate_bind,
    simulate_comp, ← simAbs_none S samp pl hl hist r sl n ρ,
    Games.simulate_eq_of_abs _ _ _ (simComp_abs S samp pl hl hist r sl n pk sk ρ ρ' re),
    OracleComp.bind_assoc, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, hfin, simulate_pure]
  rw [ProbComp.expect_bind]
  simp only [ProbComp.expect_pure]
  refine (expect_toCompOn_outLen _ A n (q.eval n) pk rA none hdα fun p =>
    F (idealView S samp pl n (r.eval n) sk ρ (List.ofFn (padFin _ (simOutL S r n
      (List.ofFn (simAbs S samp pl hl hist r sl n ρ p.2).1) p.1)))
      (simAbs S samp pl hl hist r sl n ρ p.2).2)).trans ?_
  refine congrArg _ (funext fun p => ?_)
  rw [idealView_simOut S samp pl hl hist r sl n sk ρ p.2 _ (by
    rw [List.length_ofFn])]

/-- **The simulator exists:** for the sampler `samp` (parameter length `pl`, history `hist` of
length `hl`), the adversary `A` and the polynomials `q`, `r`, `sl`, there is a machine `Sim` whose
ideal acceptance rate (budget `1`) is, for every distinguisher and every `n`, the hybrid `H_true`'s
(under CPA).

**Proof sketch.** `Sim₀` is T2's machine of the simulator's handler and `Sim` hard-wires
`M.advice n` as the second input component (`NUPPT.exists_withAdviceOn`). Reindex `Sim`'s coins as
`(ρ̃ ‖ re, rA)` (`coinsCongr`, `φ`, `seedEquiv`, `expect_sample_prod`), draw the hybrid's encryption
coins in advance (`expect_simulate_rImpl_eager`) and reorder the samples (`expect_sample_comm`);
pointwise this is `simRun_eq`. -/
theorem exists_simulator : ∃ Sim : NUPPT, ∀ (X : NUPPT) (n : ℕ),
    idealAcc S samp pl hl hist Sim (r.eval n) (sl.eval n) X n =
      hybAcc S .cpa true samp pl hl hist A (q.eval n) (r.eval n) (sl.eval n) X n := by
  obtain ⟨Sim₀, hT2⟩ := exists_interactiveHandlerMachine A q (snmDin S pl) (snmDout S hl)
    (fun _ : Fin 1 => pl) (fun _ => hl) ((r.mul S.ctLen).add sl)
    (chalHandler (simParams S samp pl hl r sl))
  obtain ⟨Sim, hc, hSim⟩ := NUPPT.exists_withAdviceOn Sim₀ samp.advice samp.adv
    samp.advice_length
  refine ⟨Sim, fun X n => ?_⟩
  obtain ⟨φ, hφ⟩ := hT2 n
  rw [idealAcc_eq, hybAcc_eq]
  refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr hc n)]
  simp only [hSim]
  rw [← ProbComp.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
    ← ProbComp.expect_sample_equiv (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n),
    ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun ρ' => ?_)
  simp only [expect_simulate_rImpl_eager]
  refine (congrArg _ (funext fun re => congrArg _ (funext fun rA => congrArg _ (funext fun rX =>
    simRun_eq S samp pl hl hist A q r sl Sim₀ n φ hφ _ _ ρ ρ' re rA fun v =>
      if X.distinguisherL n v rX = true then 1 else 0)))).trans ?_
  rw [ProbComp.expect_sample_comm]
  refine congrArg _ (funext fun rA => ?_)
  rw [ProbComp.expect_sample_comm]

end Ideal

end TCSlib.Cryptography.Composability.NMSim
