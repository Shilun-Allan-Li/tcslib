/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hybrid oracle of Theorem 174.8

The real experiment of SIM-NME′ [PSV07, Definition 1] (`Simulation.lean`) runs the adversary
against two oracles: `Dec` (per the attack) and a challenge that, on the sampler's parameter `a`,
draws `m = M(a; ρ)`, encrypts it and answers `⟨Enc_pk(m), h(m)⟩`. Both directions of
[PS10, Theorem 174.8] compare runs against variants of these oracles. This file states them
once, generically in the sampler (a machine `samp`, the parameter length `pl`, the history
function `hist` and its length `hl`), on the lengths that T2 machines use (`snmDin`, `snmDout`):

* `rImpl … b … ρ ρ' ce` encrypts `M(a; ρ)` for `b = false` and `M(a; ρ')` for `b = true`, always
  answering the history of `m = M(a; ρ)`. With `b = false` it is the real experiment's oracle; with
  `b = true` it is the hybrid in which the adversary sees an encryption of an independent draw. The
  encryption coins are sampled (`ce = none`) or given in advance (`ce = some re`).
* `histImpl` is the ideal experiment's history oracle on the same lengths.
* `realView` and `idealView` are the experiments' outputs `(a, m, (d_i)_i, σ)` as strings, read
  from the adversary's (respectively the simulator's) output string and the final state.
* `realAcc`, `idealAcc` and `hybAcc` are the acceptance rates of the real experiment, the ideal
  experiment and the hybrid `H_b`, on these lengths.

## Main definitions

* `NMSim.snmDin`, `NMSim.snmDout`: the oracle lengths as polynomials.
* `NMSim.drawWith`, `NMSim.histWith`, `NMSim.encWith`: `M(a; ρ)`, `h(m)` and `Enc_pk(m; re)`.
* `NMSim.rImpl`: the hybrid oracle; `NMSim.histImpl`: the history oracle.
* `NMSim.chunkAt`, `NMSim.entryL`, `NMSim.realView`, `NMSim.idealView`.
* `NMSim.realAcc`, `NMSim.idealAcc`, `NMSim.hybAcc`.

## Main results

* `NMSim.snmDin_eval_inLens`, `NMSim.snmDout_eval_outLens`: with `pl = 2·msgLen` and `hl = 0` the
  lengths are those of Definition 171.5.
* `NMSim.rImpl_dec`, `_some`, `_none_lazy`, `_none_eager`, `_dec_cpa`: the oracle's answers.
* `NMSim.rImpl_eq_of_msgLen_eq_zero`: with empty messages the two hybrids coincide.
* `NMSim.expect_simulate_rImpl_eager`: the encryption coins may be drawn in advance.
* `NMSim.rImpl_false_coins`, `NMSim.histImpl_coins`: coins that are not read.
* Blocks of strings: `NMSim.ofFn_block`, `ofFn_natAdd_eq_drop`, `take_eq_flatten_chunkAt`,
  `chunkAt_flatten_append`, `map_chunkAt_flatten`, and their lengths.
* `NMSim.realAcc_eq_hybAcc`, `NMSim.hybAcc_true_eq_false`: `H_false` is the real experiment, and
  the hybrids coincide when `msgLen(n) = 0`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.6, Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal B (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean`, with every seal candidate of its
full TCSlib import closure (1288 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acEnc _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHyb _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acSeedTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acStLen _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl_adaptiveIndImpl.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.expect_tapeImpl.match_1_4 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.extTape _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.simulate_tapeImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.tapeImpl _root_.TCSlib.Cryptography.Composability.Attack.ofNat _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_some_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.length_of_firstQ_eq_some.match_1_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.NMSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmDecrypt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmOutput _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nthCt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.ofPadded _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.NMCCA2.ansRead _root_.TCSlib.Cryptography.Composability.NMCCA2.cntRead _root_.TCSlib.Cryptography.Composability.NMCCA2.decBlock _root_.TCSlib.Cryptography.Composability.NMCCA2.decHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encCt _root_.TCSlib.Cryptography.Composability.NMCCA2.encHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encTape _root_.TCSlib.Cryptography.Composability.NMCCA2.finA _root_.TCSlib.Cryptography.Composability.NMCCA2.finL _root_.TCSlib.Cryptography.Composability.NMCCA2.finU _root_.TCSlib.Cryptography.Composability.NMCCA2.finW _root_.TCSlib.Cryptography.Composability.NMCCA2.finZ _root_.TCSlib.Cryptography.Composability.NMCCA2.fwdHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.guessBit _root_.TCSlib.Cryptography.Composability.NMCCA2.guessDist _root_.TCSlib.Cryptography.Composability.NMCCA2.indImpl_eq_of_msgLen_eq_zero.match_1_1 _root_.TCSlib.Cryptography.Composability.NMCCA2.logEmit _root_.TCSlib.Cryptography.Composability.NMSim.chunkEmit _root_.TCSlib.Cryptography.Composability.NMSim.chunkMap _root_.TCSlib.Cryptography.Composability.NMSim.chunkStep _root_.TCSlib.Cryptography.Composability.isPadded _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Composability.padDecFun _root_.TCSlib.Cryptography.Composability.padEncFun _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GGMRed.IsQ _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.advPoly _root_.TCSlib.Cryptography.GGMRed.adviceOf _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.ansMap _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinPoly _root_.TCSlib.Cryptography.GGMRed.coinStr _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.concrete _root_.TCSlib.Cryptography.GGMRed.concrete_iterate.match_1_1 _root_.TCSlib.Cryptography.GGMRed.encState _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.firstRound _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.nextQ _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.orbit_eq_encState.match_1_1 _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.prefMap _root_.TCSlib.Cryptography.GGMRed.pureAt _root_.TCSlib.Cryptography.GGMRed.pureStep _root_.TCSlib.Cryptography.GGMRed.pureStep.match_1 _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rawInput _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.stream _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.valStr _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.IInv _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom.match_1 _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.gB _root_.TCSlib.Cryptography.Games.EffFill.gC _root_.TCSlib.Cryptography.Games.EffFill.gCur _root_.TCSlib.Cryptography.Games.EffFill.gLc _root_.TCSlib.Cryptography.Games.EffFill.gLin _root_.TCSlib.Cryptography.Games.EffFill.gO _root_.TCSlib.Cryptography.Games.EffFill.gPh _root_.TCSlib.Cryptography.Games.EffFill.gS _root_.TCSlib.Cryptography.Games.EffFill.hAct _root_.TCSlib.Cryptography.Games.EffFill.hBound _root_.TCSlib.Cryptography.Games.EffFill.hCtx _root_.TCSlib.Cryptography.Games.EffFill.hMove _root_.TCSlib.Cryptography.Games.EffFill.hNext _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.hRes _root_.TCSlib.Cryptography.Games.EffFill.hRounds _root_.TCSlib.Cryptography.Games.EffFill.hStart _root_.TCSlib.Cryptography.Games.EffFill.hState _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iAnsLen _root_.TCSlib.Cryptography.Games.EffFill.iAsk _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallAct _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCallNext _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinAct _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinNext _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iFixBound _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iNext _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iTree _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_le_length_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.relabel _root_.TCSlib.Cryptography.Games.EffFill.relabelEmit _root_.TCSlib.Cryptography.Games.EffFill.relabelN _root_.TCSlib.Cryptography.Games.EffFill.relabelN_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.InteractiveHandler.rCnt _root_.TCSlib.Cryptography.Games.InteractiveHandler.rI _root_.TCSlib.Cryptography.Games.InteractiveHandler.rL _root_.TCSlib.Cryptography.Games.InteractiveHandler.rS _root_.TCSlib.Cryptography.Games.InteractiveHandler.rU _root_.TCSlib.Cryptography.Games.InteractiveHandler.rW _root_.TCSlib.Cryptography.Games.InteractiveHandler.rX _root_.TCSlib.Cryptography.Games.InteractiveHandler.rZ _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.answer.match_1 _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.buildComp_singleCodec.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.singleCodec _root_.TCSlib.Cryptography.Games.singleCodec.match_1 _root_.TCSlib.Cryptography.Games.toHist _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PublicKeyScheme.Secure _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.PublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_prf_of_exists_prg.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmPRF _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.hybridAdv _root_.TCSlib.Cryptography.hybridCoins _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridPlant _root_.TCSlib.Cryptography.hybridPre _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.length_flatten_ofFn.match_1_1 _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multiDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.singleDist _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


variable (S : FixedLengthPKScheme)

/-! ### Lengths -/

/-- The query lengths of the real experiment's oracles as polynomials: ciphertexts for `Dec`, the
sampler's parameter (`pl(n)` bits) for the challenge. -/
def snmDin (pl : PolyExpr) : Fin 2 → PolyExpr
  | 0 => S.ctLen
  | 1 => pl

/-- `Dec` queries are ciphertexts: `snmDin S pl 0 = S.ctLen`. -/
theorem snmDin_zero (pl : PolyExpr) : snmDin S pl 0 = S.ctLen := rfl

/-- Challenge queries are parameters: `snmDin S pl 1 = pl`. -/
theorem snmDin_one (pl : PolyExpr) : snmDin S pl 1 = pl := rfl

/-- The answer lengths as polynomials: a flag and a message for `Dec`, a ciphertext and the
history (`hl(n)` bits) for the challenge. -/
def snmDout (hl : PolyExpr) : Fin 2 → PolyExpr
  | 0 => S.msgLen.add (.const 1)
  | 1 => S.ctLen.add hl

/-- `Dec` answers a flag and a message: `snmDout S hl 0 = msgLen + 1`. -/
theorem snmDout_zero (hl : PolyExpr) : snmDout S hl 0 = S.msgLen.add (.const 1) := rfl

/-- The challenge answers a ciphertext and the history: `snmDout S hl 1 = ctLen + hl`. -/
theorem snmDout_one (hl : PolyExpr) : snmDout S hl 1 = S.ctLen.add hl := rfl

/-- With the parameter `⟨m₀, m₁⟩` (`pl = msgLen + msgLen`) the query lengths are those of
Definition 171.5: `(snmDin S (msgLen + msgLen) ·).eval n = S.inLens n`. -/
theorem snmDin_eval_inLens (n : ℕ) :
    (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) = S.inLens n := by
  funext i
  match i with
  | 0 => rw [snmDin_zero, S.inLens_zero]
  | 1 => rw [snmDin_one, PolyExpr.eval_add, S.inLens_one]

/-- With an empty history (`hl = 0`) the answer lengths are those of Definition 171.5:
`(snmDout S 0 ·).eval n = S.outLens n`. -/
theorem snmDout_eval_outLens (n : ℕ) :
    (fun i => (snmDout S (.const 0) i).eval n) = S.outLens n := by
  funext i
  match i with
  | 0 => rw [snmDout_zero, PolyExpr.eval_add, PolyExpr.eval_const, S.outLens_zero]
  | 1 => rw [snmDout_one, PolyExpr.eval_add, PolyExpr.eval_const, Nat.add_zero, S.outLens_one]

/-! ### Draws, histories and encryptions -/

/-- The message `M(a; ρ)` drawn by the sampler `samp` on the parameter `a` with coins `ρ`, read at
`ℓ` bits: `drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n ⟦a⟧ ρ)`. -/
def drawWith (samp : NUPPT) (ℓ n : ℕ) {k : ℕ} (a : Fin k → Bool) (ρ : samp.Coins n) :
    Fin ℓ → Bool :=
  padFin ℓ (samp.runAt n (List.ofFn a) ρ)

/-- `drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n ⟦a⟧ ρ)`. -/
theorem drawWith_eq (samp : NUPPT) (ℓ n : ℕ) {k : ℕ} (a : Fin k → Bool) (ρ : samp.Coins n) :
    drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n (List.ofFn a) ρ) := rfl

/-- The history `h(m)` read at `hl` bits: `histWith hist hl m = padFin hl (hist ⟦m⟧)`. -/
def histWith (hist : List Bool → List Bool) (hl : ℕ) {ℓ : ℕ} (m : Fin ℓ → Bool) : Fin hl → Bool :=
  padFin hl (hist (List.ofFn m))

/-- `histWith hist hl m = padFin hl (hist ⟦m⟧)`. -/
theorem histWith_eq (hist : List Bool → List Bool) (hl : ℕ) {ℓ : ℕ} (m : Fin ℓ → Bool) :
    histWith hist hl m = padFin hl (hist (List.ofFn m)) := rfl

/-- The encryption `Enc_pk(m; re)` read at `ctLen(n)` bits:
`encWith S n pk m re = padFin ctLen(n) (Enc.runAt n ⟨pk, ⟦m⟧⟩ re)`. -/
def encWith (n : ℕ) (pk : List Bool) {ℓ : ℕ} (m : Fin ℓ → Bool) (re : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn m)) re)

/-- `encWith S n pk m re = padFin ctLen(n) (Enc.runAt n ⟨pk, ⟦m⟧⟩ re)`. -/
theorem encWith_eq (n : ℕ) (pk : List Bool) {ℓ : ℕ} (m : Fin ℓ → Bool) (re : S.enc.Coins n) :
    encWith S n pk m re = padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn m)) re) := rfl

/-! ### The hybrid oracle -/

/-- **The hybrid oracle** at parameter `n`, for the keys `pk`, `sk`, the sampler `samp` (parameter
length `pl`, history `hist` of length `hl`) and its coins `ρ`, `ρ'`, on T2's lengths
(`snmDin`, `snmDout`); the state is the challenge with its parameter, once asked.
- `Dec` answers as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not
  the challenge, and `⊥` (all `false`) otherwise.
- The challenge on the parameter `a`, the first time: `m = M(a; ρ)`; it encrypts `M(a; ρ)` for
  `b = false` and `M(a; ρ')` for `b = true`, with coins sampled (`ce = none`) or given (`ce = some
  re`), answers `⟨y, h(m)⟩` and records `(y, a)`. Later it repeats `⟨y, h(M(a₀; ρ))⟩` for the
  recorded `(y, a₀)`. -/
noncomputable def rImpl (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) :
    QueryImpl (bitSpecAt (snmDin S pl) (snmDout S hl) n)
      (Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin _ (List.ofFn c))) then
      .pure (padFin _ (List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))))), s)
    else .pure (zeroBits _, s)
  | 1, _, some (y, a) =>
    .pure (padFin _ (List.ofFn y ++ List.ofFn (histWith hist (hl.eval n)
      (drawWith samp (S.msgLen.eval n) n a ρ))), some (y, a))
  | 1, x, none =>
    match ce with
    | some re =>
      .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
          (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
          List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) ρ))),
        some (encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re, padFin (pl.eval n) (List.ofFn x)))
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
            List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
              (padFin (pl.eval n) (List.ofFn x)) ρ))),
          some (encWith S n pk (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re,
            padFin (pl.eval n) (List.ofFn x)))

section Readers

variable (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
  (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
  (ce : Option (S.enc.Coins n))

/-- **Decryption** as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when open and not the recorded
challenge, `⊥` otherwise; the state is kept. -/
theorem rImpl_dec (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome &&
          !decide (s.map Prod.fst = some (padFin _ (List.ofFn c))) then
        .pure (padFin _ (List.ofFn (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))))), s)
      else .pure (zeroBits _, s) := rfl

/-- **Under CPA, `Dec` answers `⊥`** and keeps the state. -/
theorem rImpl_dec_cpa (b : Bool) (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S .cpa b samp pl hl hist n pk sk ρ ρ' ce 0 c s = .pure (zeroBits _, s) := by
  rw [rImpl_dec, FixedLengthScheme.decOpen_cpa, Bool.false_and, if_neg Bool.false_ne_true]

/-- **A repeated challenge** answers `⟨y, h(M(a₀; ρ))⟩` for the recorded `(y, a₀)` and keeps the
state. -/
theorem rImpl_some (x : Fin ((snmDin S pl 1).eval n) → Bool) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 1 x (some (y, a)) =
      .pure (padFin _ (List.ofFn y ++ List.ofFn (histWith hist (hl.eval n)
        (drawWith samp (S.msgLen.eval n) n a ρ))), some (y, a)) := rfl

/-- **A first challenge with coins drawn in advance:** on `x` (read as the parameter `a`) it
answers `⟨Enc_pk(M(a; ρ_b); re), h(M(a; ρ))⟩` and records the ciphertext with `a`. -/
theorem rImpl_none_eager (x : Fin ((snmDin S pl 1).eval n) → Bool) (re : S.enc.Coins n) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re) 1 x none =
      .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
          (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
          List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) ρ))),
        some (encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re, padFin (pl.eval n) (List.ofFn x))) := rfl

/-- **A first challenge with sampled coins** samples `re` and answers as with `re` in advance. -/
theorem rImpl_none_lazy (x : Fin ((snmDin S pl 1).eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' none 1 x none =
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re) 1 x none := rfl

/-- Decryption does not read the encryption coins. -/
theorem rImpl_dec_ce (ce' : Option (S.enc.Coins n)) (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 0 c s =
      rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce' 0 c s := rfl

/-- A repeated challenge does not read the encryption coins. -/
theorem rImpl_some_ce (ce' : Option (S.enc.Coins n)) (x : Fin ((snmDin S pl 1).eval n) → Bool)
    (y : Fin (S.ctLen.eval n) → Bool) (a : Fin (pl.eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 1 x (some (y, a)) =
      rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce' 1 x (some (y, a)) := rfl

end Readers

/-- Every call keeps a recorded state recorded: from `some _`, every successor is `some _`. -/
theorem rImpl_allOutputs_isSome (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) (i : Fin 2) (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (hs : s.isSome) :
    (rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce i x s).AllOutputs fun p => p.2.isSome := by
  obtain ⟨⟨y, a⟩, rfl⟩ := Option.isSome_iff_exists.1 hs
  match i with
  | 0 =>
    rw [rImpl_dec]
    split <;> exact OracleComp.allOutputs_pure.2 rfl
  | 1 => exact OracleComp.allOutputs_pure.2 rfl

/-- **The encryption coins may be drawn in advance:** for every computation `c` and function `G`,
the run against the hybrid oracle with sampled coins has the law of the runs with coins `re`
drawn in advance, averaged over `re` (`expect_simulate_eager`; the coins are spent at the first
challenge). -/
theorem expect_simulate_rImpl_eager (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n) {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α)
    (G : α × Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) → ℝ) :
    ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n pk sk ρ ρ' none) c none) G =
      ProbComp.expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re)) c none)
          G := by
  refine expect_simulate_eager _ _ (fun s => s.isSome = true) (fun re i x s hs => ?_)
    (fun i x s hs => rImpl_allOutputs_isSome S atk b samp pl hl hist n pk sk ρ ρ' none i x s hs)
    (fun i x s hs => ?_) c G (by simp)
  · obtain ⟨⟨y, a⟩, rfl⟩ := Option.isSome_iff_exists.1 hs
    match i with
    | 0 => exact rImpl_dec_ce S atk b samp pl hl hist n pk sk ρ ρ' (some re) none x _
    | 1 => exact rImpl_some_ce S atk b samp pl hl hist n pk sk ρ ρ' (some re) none x y a
  · have hs' : s = none := by simpa using hs
    subst hs'
    match i with
    | 0 =>
      refine Or.inl fun re => ⟨rImpl_dec_ce S atk b samp pl hl hist n pk sk ρ ρ' _ _ x none, ?_⟩
      rw [rImpl_dec]
      split <;> exact OracleComp.allOutputs_pure.2 (by simp)
    | 1 =>
      refine Or.inr ⟨rImpl_none_lazy S atk b samp pl hl hist n pk sk ρ ρ' x, fun re => ?_⟩
      rw [rImpl_none_eager]
      exact OracleComp.allOutputs_pure.2 rfl

/-- **With empty messages the two hybrids coincide:** if `msgLen(n) = 0`, then the oracle encrypting
`M(a; ρ')` is the one encrypting `M(a; ρ)` (both draws are the empty message). -/
theorem rImpl_eq_of_msgLen_eq_zero (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) (h : S.msgLen.eval n = 0) :
    rImpl S atk true samp pl hl hist n pk sk ρ ρ' ce =
      rImpl S atk false samp pl hl hist n pk sk ρ ρ' ce := by
  have hsub : ∀ {k : ℕ} (a : Fin k → Bool),
      drawWith samp (S.msgLen.eval n) n a ρ' = drawWith samp (S.msgLen.eval n) n a ρ := by
    intro k a
    funext j
    have := j.isLt
    omega
  funext i x s
  match i, s with
  | 0, s => rfl
  | 1, some (y, a) => rfl
  | 1, none =>
    cases ce with
    | some re => rw [rImpl_none_eager, rImpl_none_eager, if_pos rfl, if_neg Bool.false_ne_true,
        hsub]
    | none =>
      rw [rImpl_none_lazy, rImpl_none_lazy]
      simp only [rImpl_none_eager, Bool.false_eq_true, ↓reduceIte, hsub]

/-- **With `b = false` the hybrid does not read `ρ'`:** the oracles for `ρ₁` and `ρ₂` coincide. -/
theorem rImpl_false_coins (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ₁ ρ₂ : samp.Coins n)
    (ce : Option (S.enc.Coins n)) :
    rImpl S atk false samp pl hl hist n pk sk ρ ρ₁ ce =
      rImpl S atk false samp pl hl hist n pk sk ρ ρ₂ ce := by
  funext i x s
  match i, s with
  | 0, s => rfl
  | 1, some (y, a) => rfl
  | 1, none => cases ce <;> rfl

/-! ### The history oracle -/

/-- **The ideal experiment's oracle** on T2's lengths (`pl(n)`-bit queries, `hl(n)`-bit answers):
on the parameter `a` (the first one asked, recorded) it answers `h(M(a; ρ))`. -/
noncomputable def histImpl (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (n : ℕ) (ρ : samp.Coins n) :
    QueryImpl (bitSpecAt (fun _ : Fin 1 => pl) (fun _ => hl) n) (Option (Fin (pl.eval n) → Bool))
      unifSpec :=
  fun _ a s => .pure (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ),
    some (s.getD a))

/-- `histImpl … ρ i a s = pure (h(M(s.getD a; ρ)), some (s.getD a))`. -/
theorem histImpl_eq (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool) (n : ℕ)
    (ρ : samp.Coins n) (i : Fin 1) (a : Fin (pl.eval n) → Bool)
    (s : Option (Fin (pl.eval n) → Bool)) :
    histImpl S samp pl hl hist n ρ i a s =
      .pure (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ),
        some (s.getD a)) := rfl

/-- **With an empty history the oracle ignores the sampler's coins:** if `hl(n) = 0`, then
`histImpl … ρ = histImpl … ρ'`. -/
theorem histImpl_coins (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool) (n : ℕ)
    (ρ ρ' : samp.Coins n) (h : hl.eval n = 0) :
    histImpl S samp pl hl hist n ρ = histImpl S samp pl hl hist n ρ' := by
  funext i a s
  rw [histImpl_eq, histImpl_eq]
  have hv : histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ) =
      histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ') := by
    funext j
    have := j.isLt
    omega
  rw [hv]

/-! ### Blocks of fixed-length strings -/

/-- Block `i` of `k` bits of a string: `chunkAt k i w = (w.drop (i·k)).take k`. -/
def chunkAt (k i : ℕ) (w : List Bool) : List Bool := (w.drop (i * k)).take k

/-- `chunkAt k i w = (w.drop (i·k)).take k`. -/
theorem chunkAt_eq (k i : ℕ) (w : List Bool) : chunkAt k i w = (w.drop (i * k)).take k := rfl

/-- A block inside the string has `k` bits: `|chunkAt k i w| = k` when `(i + 1)·k ≤ |w|`. -/
theorem length_chunkAt (k i : ℕ) (w : List Bool) (h : (i + 1) * k ≤ w.length) :
    (chunkAt k i w).length = k := by
  rw [chunkAt_eq, List.length_take, List.length_drop, Nat.succ_mul] at *
  omega

/-- **The first `r` blocks:** `w.take (r·k) = (chunkAt k 0 w ++ ⋯ ++ chunkAt k (r-1) w)`. -/
theorem take_eq_flatten_chunkAt (k r : ℕ) (w : List Bool) :
    w.take (r * k) = ((List.range r).map fun i => chunkAt k i w).flatten := by
  induction r with
  | zero => rw [Nat.zero_mul, List.take_zero, List.range_zero, List.map_nil, List.flatten_nil]
  | succ r ih =>
    rw [Nat.succ_mul, List.take_add, ih, List.range_succ, List.map_append, List.flatten_append,
      List.map_singleton, List.flatten_singleton, chunkAt_eq]

/-- `r` blocks of `k` bits have `r·k` bits. -/
theorem length_flatten_map_range (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k) :
    ((List.range r).map g).flatten.length = r * k := by
  induction r with
  | zero => rw [List.range_zero, List.map_nil, List.flatten_nil, List.length_nil, Nat.zero_mul]
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ih fun i hi => hg i (by omega), List.map_singleton, List.flatten_singleton,
      hg r (by omega), Nat.succ_mul]

/-- Blocks of `k` bits, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
`k` bits. -/
theorem length_flatten_map_const {α β : Type} (l : List α) (g : α → List β) (k : ℕ)
    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
  induction l with
  | nil => rw [List.map_nil, List.flatten_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | cons x t ih => rw [List.map_cons, List.flatten_cons, List.length_append, ih, hg,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- **Reading back the blocks:** if `g 0, …, g (r-1)` have `k` bits each, block `i < r` of
`g 0 ++ ⋯ ++ g (r-1) ++ t` is `g i`. -/
theorem chunkAt_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
    (t : List Bool) (i : ℕ) (hi : i < r) :
    chunkAt k i (((List.range r).map g).flatten ++ t) = g i := by
  induction r generalizing t with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton, List.append_assoc]
    by_cases h : i < r
    · exact ih (fun j hj => hg j (by omega)) _ h
    · have hir : i = r := by omega
      subst hir
      rw [chunkAt_eq, List.drop_append_of_le_length (by
          rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.drop_of_length_le (by rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.nil_append, List.take_left' (hg i (by omega))]

/-- The tail after `r` blocks of `k` bits: `(g 0 ++ ⋯ ++ g (r-1) ++ t).drop (r·k) = t`. -/
theorem drop_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
    (t : List Bool) : (((List.range r).map g).flatten ++ t).drop (r * k) = t :=
  List.drop_left' (length_flatten_map_range k r g hg)

/-- **The blocks of a concatenation of `k`-bit blocks:** if every block of `cs` has `k` bits,
mapping `F` over `chunkAt k i cs.flatten` for `i < |cs|` is mapping `F` over `cs`. -/
theorem map_chunkAt_flatten {α : Type} (k : ℕ) (F : List Bool → α) :
    ∀ cs : List (List Bool), (∀ c ∈ cs, c.length = k) →
      (List.range cs.length).map (fun i => F (chunkAt k i cs.flatten)) = cs.map F := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c t ih =>
    intro hc
    have hck : c.length = k := hc c List.mem_cons_self
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons,
      List.flatten_cons, ← ih fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')]
    congr 1
    · rw [chunkAt_eq, Nat.zero_mul, List.drop_zero, List.take_left' hck]
    · refine List.map_congr_left fun i _ => ?_
      rw [Function.comp_apply, chunkAt_eq, chunkAt_eq, Nat.succ_mul, Nat.add_comm,
        ← List.drop_drop, List.drop_left' hck]

/-- **Block `i` of a string of `r` blocks of `k` bits and a tail:**
`⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = chunkAt k i ⟦w⟧`. -/
theorem ofFn_block {r k sl : ℕ} (w : Fin (r * k + sl) → Bool) (i : Fin r) :
    List.ofFn (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
      chunkAt k i (List.ofFn w) := by
  have hle : (i : ℕ) * k + k ≤ r * k := by
    have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  rw [chunkAt_eq]
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine congrArg w (Fin.ext ?_)
    rw [Fin.coe_castAdd, finProdFinEquiv_apply_val]
    show j + k * i = i * k + j
    rw [Nat.mul_comm]
    omega

/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k`. -/
theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
  rw [List.ofFn_add, List.drop_left' List.length_ofFn]

/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for `i < r`, then
`List.ofFn f = (List.range r).map g`. -/
theorem ofFn_eq_map_range {α : Type} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

/-- Comparing strings is comparing their lists:
`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)`. -/
theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
  cases o with
  | none => simp
  | some c' => simp [List.ofFn_inj]

/-! ### The experiments' outputs as strings -/

/-- **An entry `d_i` as a string:** `COPY` (`true` followed by `msgLen(n) + 1` falses) if `copy`,
and `false` followed by `Dec`'s answer on the ciphertext `c` otherwise. -/
def entryL (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) : List Bool :=
  if copy then true :: List.replicate (S.msgLen.eval n + 1) false
  else false :: List.ofFn (FixedLengthScheme.decAnswer
    (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c))))

/-- `entryL S n sk copy c =
if copy then true :: 0^{msgLen + 1} else false :: ⟦decAnswer (Dec_sk c)⟧`. -/
theorem entryL_eq (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    entryL S n sk copy c = if copy then true :: List.replicate (S.msgLen.eval n + 1) false
      else false :: List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c)))) := rfl

/-- An entry has `msgLen(n) + 2` bits. -/
theorem length_entryL (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    (entryL S n sk copy c).length = S.msgLen.eval n + 2 := by
  rw [entryL_eq]
  cases copy
  · rw [if_neg Bool.false_ne_true, List.length_cons, List.length_ofFn]
  · rw [if_pos rfl, List.length_cons, List.length_replicate]

/-- **The real experiment's output** `(a, m, (d_i)_i, σ)` as a string, from the adversary's output
string `w` (`r` ciphertexts, then `σ`) and the final state `s`: `a` is the recorded parameter
(`0` if none), `m = M(a; ρ)`, and `d_i` is `COPY` exactly when ciphertext `i` is the recorded
challenge. -/
def realView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    List Bool :=
  List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
    ((List.range r).map fun i => entryL S n sk
      (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
      (chunkAt (S.ctLen.eval n) i w)).flatten ++
    w.drop (r * S.ctLen.eval n)

/-- `realView … w s = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
theorem realView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    realView S samp pl n r sk ρ w s =
      List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
        List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
        ((List.range r).map fun i => entryL S n sk
          (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
          (chunkAt (S.ctLen.eval n) i w)).flatten ++
        w.drop (r * S.ctLen.eval n) := rfl

/-- **The ideal experiment's output** `(a, m, (d_i)_i, σ)` as a string, from the simulator's output
string `w` (`r` entries of a flag and a ciphertext, then `σ`) and the history oracle's state `sa`:
`a` is the recorded parameter (`0` if none), `m = M(a; ρ)`, and `d_i` is `COPY` exactly when entry
`i` is flagged. -/
def idealView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (sa : Option (Fin (pl.eval n) → Bool)) : List Bool :=
  List.ofFn (sa.getD (zeroBits _)) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
    ((List.range r).map fun i => entryL S n sk
      ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
      (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
    w.drop (r * (S.ctLen.eval n + 1))

/-- `idealView … w sa = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
theorem idealView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (sa : Option (Fin (pl.eval n) → Bool)) :
    idealView S samp pl n r sk ρ w sa =
      List.ofFn (sa.getD (zeroBits _)) ++
        List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
        ((List.range r).map fun i => entryL S n sk
          ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
          (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
        w.drop (r * (S.ctLen.eval n + 1)) := rfl

/-! ### The acceptance rates of the experiments -/

/-- **The real experiment's acceptance rate** for the sampler `samp` (parameter length `pl`,
history `hist` of length `hl`), the adversary `A` (budget `q`, `r` ciphertexts and an `sl`-bit `σ`)
and the distinguisher `X`, on T2's lengths: over the keys and the coins of the sampler, `A` and
`X`, the probability that `X` accepts `realView` of `A`'s run against `rImpl … false … ρ ρ none`. -/
noncomputable def realAcc (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (rImpl S atk false samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
    (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
      (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
    if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `realAcc … = 𝔼_{rg, ρ, rA, rX} 𝔼[1{X accepts realView}]` over `A`'s run against `rImpl`. -/
theorem realAcc_eq (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) :
    realAcc S atk samp pl hl hist A q r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (rImpl S atk false samp pl hl hist n
          (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
        if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

/-- **The ideal experiment's acceptance rate** for the sampler `samp` (as in `realAcc`), the
simulator `Sim` (budget `1`, `r` entries and an `sl`-bit `σ`) and the distinguisher `X`: over the
keys and the coins of the sampler, `Sim` and `X`, the probability that `X` accepts `idealView` of
`Sim`'s run against `histImpl … ρ`. -/
noncomputable def idealAcc (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (Sim.Coins n)) fun rS =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
    (Sim.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
      (r * (S.ctLen.eval n + 1) + sl)) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
    if X.distinguisherL n (idealView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `idealAcc … = 𝔼_{rg, ρ, rS, rX} 𝔼[1{X accepts idealView}]` over `Sim`'s run against
`histImpl`. -/
theorem idealAcc_eq (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) :
    idealAcc S samp pl hl hist Sim r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (Sim.Coins n)) fun rS =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
        (Sim.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          (r * (S.ctLen.eval n + 1) + sl)) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
        if X.distinguisherL n (idealView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

/-- **The hybrid experiments' acceptance rate** `H_b` for the sampler `samp` (as in `realAcc`), the
adversary `A` (budget `q`, `r` ciphertexts and an `sl`-bit `σ`) and the distinguisher `X`: over the
keys, the sampler's coins `ρ`, `ρ'` and the coins of `A` and `X`, the probability that `X` accepts
`realView` of `A`'s run against `rImpl … b … ρ ρ' none`. `H_false` is the real experiment
(`realAcc_eq_hybAcc`). -/
noncomputable def hybAcc (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ' =>
  ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) ρ ρ' none)
    (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
      (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
    if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `hybAcc … b … = 𝔼_{rg, ρ, ρ', rA, rX} 𝔼[1{X accepts realView}]` over `A`'s run against
`rImpl … b … ρ ρ' none`. -/
theorem hybAcc_eq (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) :
    hybAcc S atk b samp pl hl hist A q r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ' =>
      ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) ρ ρ' none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
        if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

/-- **The real experiment is the hybrid `H_false`:** `realAcc … = hybAcc … false …` (with
`b = false` the oracle does not read `ρ'`, `rImpl_false_coins`). -/
theorem realAcc_eq_hybAcc (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) :
    realAcc S atk samp pl hl hist A q r sl X n =
      hybAcc S atk false samp pl hl hist A q r sl X n := by
  rw [realAcc_eq, hybAcc_eq]
  refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
  refine (ProbComp.expect_const (ProbComp.sample (samp.Coins n)) _).symm.trans
    (congrArg _ (funext fun ρ' => ?_))
  rw [rImpl_false_coins S atk samp pl hl hist n _ _ ρ ρ ρ']

/-- **With empty messages the two hybrids coincide:** if `msgLen(n) = 0`, then
`hybAcc … true … = hybAcc … false …` (`rImpl_eq_of_msgLen_eq_zero`). -/
theorem hybAcc_true_eq_false (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ)
    (h : S.msgLen.eval n = 0) :
    hybAcc S atk true samp pl hl hist A q r sl X n =
      hybAcc S atk false samp pl hl hist A q r sl X n := by
  simp only [hybAcc_eq, rImpl_eq_of_msgLen_eq_zero S atk samp pl hl hist n _ _ _ _ none h]

end TCSlib.Cryptography.Composability.NMSim
