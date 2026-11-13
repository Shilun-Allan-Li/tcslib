/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLemmas
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State loops for the hard-core predicate theorems

The loop machines behind the Goldreich–Levin theorem [PS10, Theorem 87.3], run by the guarded state
iteration `Complexity.StateLoop.polyTimeComputable_stateIterate` of `Randomized/Repetition.lean` (an
instance of `Complexity.polyTimeComputable_iterate` on the length-guarded step
`Complexity.StateLoop.gstep`): the block encoding `blocksStr` of a tuple of equal-length bit
strings, the **selective block XOR** `selXorFun` computing `⊕_{t : β_t = 1} s_t` on `⟨⟨1^m, β⟩, s⟩`
— the subset XOR `S_L` of [PS10, Algorithm 89.6] and, with one-bit blocks, the inner product
`⟨x, r⟩` of [PS10, Fact 88.4] (`ipFun`) — and unary halving `1^n ↦ 1^{⌊n/2⌋}` (`unaryHalf`, for the
balanced permutation of `Asymptotic/HardCorePermutation/GoldreichLevin.lean`).

Each loop is specified by the closed form of its orbit on well-formed inputs
(`SelXor.orbit_eq`), its stabilisation (`SelXor.orbit_stable`) and the length bound that
keeps the guard of `gstep` from firing (`SelXor.orbit_length_le`).

## Main definitions

* `TCSlib.Cryptography.blocksEquiv`, `TCSlib.Cryptography.blocksStr` — tuples of blocks as
  one bit string.
* `TCSlib.Cryptography.selXorFun`, `TCSlib.Cryptography.SelXor.partialSum` — the selective
  block XOR and its partial sums.
* `TCSlib.Cryptography.ipFun`, `TCSlib.Cryptography.unaryHalf` — the inner-product evaluator
  and unary halving.

## Main results

* `TCSlib.Cryptography.selXorFun_poly`, `TCSlib.Cryptography.selXorFun_input` — the selective
  block XOR is polynomial-time and computes the subset XOR.
* `TCSlib.Cryptography.ipFun_poly`, `TCSlib.Cryptography.ipFun_ofFn` — the inner-product
  evaluator is polynomial-time and computes `⟨x, r⟩`.
* `TCSlib.Cryptography.unaryHalf_poly` — unary halving is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset Complexity.StateLoop

/-! Seal A (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Asymptotic/HardCoreLoops.lean`, with every seal candidate of its
full TCSlib import closure (757 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquivPoly _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-- Bitwise XOR of two polynomial-time maps is polynomial-time
(`Complexity.polyTimeComputable_pairXor` on the pair). -/
theorem zipXor_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => List.zipWith xor (a w) (b w) := by
  convert polyTimeComputable_pairXor.comp (ha.pairEncode hb) using 1
  funext w
  simp

/-! ## Blocks of bit strings -/

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits: a compatibility alias of
the canonical Bool block bijection `FunFamily.blocks` of `Asymptotic/Adversary.lean`. -/
def blocksEquiv (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  FunFamily.blocks q ℓ

/-- `blocksEquiv` is the canonical block bijection: `blocksEquiv q ℓ = FunFamily.blocks q ℓ`. -/
theorem blocksEquiv_eq (q ℓ : ℕ) : blocksEquiv q ℓ = FunFamily.blocks q ℓ := rfl

/-- The inverse of `blocksEquiv` reads block `p.divNat`, position `p.modNat`
(`FunFamily.blocks_symm_apply`). -/
theorem blocksEquiv_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (p : Fin (q * ℓ)) :
    (blocksEquiv q ℓ).symm t p = t p.divNat p.modNat :=
  FunFamily.blocks_symm_apply q ℓ t p

/-- The encoding of a tuple of `k` blocks of `m` bits as one string of `k · m` bits. -/
def blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) : List Bool :=
  List.ofFn ((blocksEquiv k m).symm s)

/-- The defining equation of `blocksStr`: `blocksStr s = List.ofFn ((blocksEquiv k m).symm s)`. -/
theorem blocksStr_def {k m : ℕ} (s : Fin k → Fin m → Bool) :
    (blocksStr s : List Bool) =
      (List.ofFn ((blocksEquiv k m).symm s)) := rfl

/-- The length of the block encoding. -/
@[simp] theorem length_blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) :
    (blocksStr s).length = k * m := List.length_ofFn

/-- Block `i` of the block encoding: the `m` bits after the first `i · m`. 

**Proof sketch.** `List.ext_getElem`: the length is `min m (k·m − i·m) = m`; position `j` of the block is position `i·m + j` of the encoding, whose block index is `i` and offset `j` (`Nat.add_mul_div_right`, `Nat.add_mul_mod_self_right`). -/
theorem take_drop_blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) (i : Fin k) :
    ((blocksStr s).drop (i * m)).take m = List.ofFn (s i) := by
  have hm : 0 < m ∨ m = 0 := by omega
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_take, List.length_drop, length_blocksStr, List.length_ofFn]
    have := i.isLt
    rcases hm with hm | hm
    · refine min_eq_left ?_
      rw [← Nat.sub_mul]
      exact Nat.le_mul_of_pos_left m (by omega)
    · simp [hm]
  · simp only [List.length_ofFn] at hj₂
    simp only [List.getElem_take, List.getElem_drop, blocksStr, List.getElem_ofFn,
      blocksEquiv_symm_apply]
    have hmpos : 0 < m := by omega
    congr 1
    · refine Fin.ext ?_
      simp only [Fin.coe_divNat]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hmpos, Nat.div_eq_of_lt hj₂, zero_add]
    · refine Fin.ext ?_
      simp only [Fin.coe_modNat]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj₂]

/-- The block encoding of a tuple of one-bit blocks is the string of the bits. -/
theorem blocksStr_one {k : ℕ} (r : Fin k → Bool) :
    blocksStr (fun t (_ : Fin 1) => r t) = List.ofFn r := by
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [blocksStr, List.getElem_ofFn, blocksEquiv_symm_apply]
  congr 1
  exact Fin.ext (by simp [Fin.coe_divNat])

/-- Bitwise XOR of two encoded strings is the encoding of the pointwise sum (`Bool` as a
Boolean ring, `+` is XOR). -/
theorem zipWith_xor_ofFn_add {m : ℕ} (a b : Fin m → Bool) :
    List.zipWith xor (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_zipWith, List.getElem_ofFn, Pi.add_apply]
  rfl

/-! ## The selective block XOR `⊕_{t : β_t = 1} s_t` -/

namespace SelXor

/-- The partial subset sum `∑_{t < i, β_t = 1} s_t` of the blocks `s_t`, by recursion on `i`. -/
def partialSum {k m : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) : ℕ → (Fin m → Bool)
  | 0 => 0
  | i + 1 => partialSum β s i + if h : i < k then (if β ⟨i, h⟩ then s ⟨i, h⟩ else 0) else 0

/-- The partial sum is the subset sum over the indices `t < i` with `β_t = 1`. 

**Proof sketch.** Induction on `i`; the filter at `i + 1` splits the term `t = i` off the filter at `i` (`Finset.sum_filter`, `Finset.sum_add_distrib`, `Finset.sum_eq_single`). -/
theorem partialSum_eq {k m : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) :
    partialSum β s i = ∑ t ∈ univ.filter (fun t : Fin k => (t : ℕ) < i ∧ β t = true), s t := by
  induction i with
  | zero => simp [partialSum]
  | succ i ih =>
    rw [partialSum, ih, Finset.sum_filter, Finset.sum_filter]
    by_cases hi : i < k
    · rw [dif_pos hi]
      have hsplit : ∀ t : Fin k,
          (if (t : ℕ) < i + 1 ∧ β t = true then s t else 0) =
            (if (t : ℕ) < i ∧ β t = true then s t else 0) +
              (if t = ⟨i, hi⟩ ∧ β t = true then s t else 0) := by
        intro t
        by_cases ht : t = ⟨i, hi⟩
        · subst ht
          simp
        · have ht' : (t : ℕ) ≠ i := fun h => ht (Fin.ext h)
          by_cases hb : β t = true
          · by_cases hlt : (t : ℕ) < i
            · simp [hlt, hb, ht, Nat.lt_succ_of_lt hlt]
            · have : ¬ (t : ℕ) < i + 1 := by omega
              simp [hlt, hb, ht, this]
          · simp [hb]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single ⟨i, hi⟩ (fun t _ ht => by simp [ht]) (fun h => absurd (mem_univ _) h)]
      simp
    · rw [dif_neg hi, add_zero]
      refine Finset.sum_congr rfl fun t _ => ?_
      have : ((t : ℕ) < i + 1 ↔ (t : ℕ) < i) := by have := t.isLt; omega
      simp [this]


/-- The initial state on the input `⟨⟨1^m, β⟩, s⟩`: `⟨β, ⟨s, 1^m ⊕ 1^m⟩⟩` (the accumulator starts
at `0^m`). -/
def start (x : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD x))
    (pairEncode (pairSndD x) (List.zipWith xor (pairFstD (pairFstD x)) (pairFstD (pairFstD x))))

/-- The step on the state word `⟨⟨⟨1^m, β⟩, s⟩, ⟨β', ⟨s', acc⟩⟩⟩`: if `β'` is empty, stay;
otherwise consume its first bit `b`, drop one block of `m` bits from `s'`, and XOR that block
into `acc` when `b = 1`. -/
def step (w : List Bool) : List Bool :=
  if pairFstD (pairSndD w) = [] then pairSndD w else
    pairEncode (pairFstD (pairSndD w)).tail
      (pairEncode ((pairFstD (pairSndD (pairSndD w))).drop (pairFstD (pairFstD (pairFstD w))).length)
        (if (pairFstD (pairSndD w)).headD false then
          List.zipWith xor (pairSndD (pairSndD (pairSndD w)))
            ((pairFstD (pairSndD (pairSndD w))).take (pairFstD (pairFstD (pairFstD w))).length)
        else pairSndD (pairSndD (pairSndD w))))

/-- The output: the accumulator of the final state word. -/
def out (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- The length bound on the states of the loop. -/
def bound : PolyExpr := .mul (.const 2) .var

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_pairSndD.pairEncode
      (zipXor_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- The step is polynomial-time (`polyTimeComputable_ite` on the emptiness test, the FP
toolkit of `Complexity.StateLoop`, `takeLen_poly`/`dropLen_poly` and `zipXor_poly`). 

**Proof sketch.** The branch on `β' = []` is `polyTimeComputable_ite` with
`polyTimeComputable_isNil`; the body pairs `Complexity.polyTimeComputable_tail` with the dropped
block (`dropLen_poly`) and the conditional XOR (`polyTimeComputable_ite` on
`polyTimeComputable_headD`, `zipXor_poly` with `takeLen_poly`). -/
theorem step_poly : PolyTimeComputable step := by
  have hβ : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hu : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hacc : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have htest : PolyTimeComputable fun w => [decide (pairFstD (pairSndD w) = [])] :=
    polyTimeComputable_isNil.comp hβ
  have hhead : PolyTimeComputable fun w => [(pairFstD (pairSndD w)).headD false] :=
    polyTimeComputable_headD.comp hβ
  have hbody : PolyTimeComputable fun w =>
      pairEncode (pairFstD (pairSndD w)).tail
        (pairEncode ((pairFstD (pairSndD (pairSndD w))).drop (pairFstD (pairFstD (pairFstD w))).length)
          (if (pairFstD (pairSndD w)).headD false then
            List.zipWith xor (pairSndD (pairSndD (pairSndD w)))
              ((pairFstD (pairSndD (pairSndD w))).take (pairFstD (pairFstD (pairFstD w))).length)
          else pairSndD (pairSndD (pairSndD w)))) :=
    ((polyTimeComputable_tail.congr fun _ => List.drop_one).comp
        hβ).pairEncode ((dropLen_poly hu hs).pairEncode
      (polyTimeComputable_ite hhead (zipXor_poly hacc (takeLen_poly hu hs)) hacc))
  convert polyTimeComputable_ite htest polyTimeComputable_pairSndD hbody using 1
  funext w
  simp only [step, decide_eq_true_eq]

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The well-formed input `⟨⟨1^m, β⟩, s⟩` for `β ∈ {0,1}^k` and `k` blocks `s_t ∈ {0,1}^m`. -/
def input (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate m true) (List.ofFn β)) (blocksStr s)

/-- The closed form of the orbit on a well-formed input, for `i ≤ k` rounds:
`⟨β.drop i, ⟨s.drop (i·m), partialSum β s i⟩⟩`. 

**Proof sketch.** Induction on `i`: the initial accumulator `1^m ⊕ 1^m` is `0^m` (`List.zipWith_replicate`, `List.ofFn_const`); at round `i < k` the head of `β.drop i` is `β_i` (`List.drop_eq_getElem_cons`), the block is `take_drop_blocksStr`, and the accumulator update is `zipWith_xor_ofFn_add` against the recursion of `partialSum`. -/
theorem orbit_eq (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) (hi : i ≤ k) :
    orbit start step (input m β s) i =
      pairEncode ((List.ofFn β).drop i)
        (pairEncode ((blocksStr s).drop (i * m)) (List.ofFn (partialSum β s i))) := by
  induction i with
  | zero =>
    simp only [orbit_zero, start, input, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_zero,
      Nat.zero_mul, partialSum, List.zipWith_replicate, Nat.min_self]
    congr 2
    rw [Bool.xor_self]
    exact (List.ofFn_const m false).symm
  | succ i ih =>
    have hi' : i < k := hi
    rw [orbit_succ, ih (Nat.le_of_succ_le hi)]
    unfold step
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, input, List.length_replicate]
    have hne : (List.ofFn β).drop i ≠ [] := by
      rw [ne_eq, List.drop_eq_nil_iff, List.length_ofFn]; omega
    rw [if_neg hne, List.tail_drop, List.drop_drop,
      List.drop_eq_getElem_cons (i := i) (l := List.ofFn β) (by rw [List.length_ofFn]; exact hi'),
      List.headD_cons, List.getElem_ofFn, take_drop_blocksStr s ⟨i, hi'⟩]
    congr 2
    · rw [Nat.succ_mul]
    · rw [partialSum, dif_pos hi']
      by_cases hb : β ⟨i, hi'⟩ = true
      · rw [if_pos hb, if_pos hb, zipWith_xor_ofFn_add]
      · rw [if_neg hb, if_neg hb, add_zero]

/-- After `k` rounds the loop is stationary (`β'` is exhausted). -/
theorem orbit_stable (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (j : ℕ) :
    orbit start step (input m β s) (k + j) = orbit start step (input m β s) k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, orbit_succ, ih, orbit_eq m β s k le_rfl]
    unfold step
    simp [List.drop_eq_nil_of_le]

/-- Every state of the loop on a well-formed input has length at most `2|input|`. -/
theorem orbit_length_le (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) :
    (orbit start step (input m β s) i).length ≤ bound.eval (input m β s).length := by
  have key : ∀ i ≤ k, (orbit start step (input m β s) i).length ≤ bound.eval (input m β s).length := by
    intro i hi
    rw [orbit_eq m β s i hi]
    simp only [bound, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, input,
      length_pairEncode, List.length_drop, List.length_ofFn, List.length_replicate, length_blocksStr]
    omega
  rcases le_or_gt i k with hi | hi
  · exact key i hi
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    rw [orbit_stable]
    exact key k le_rfl

end SelXor

/-- **The selective block XOR**: on `⟨⟨1^m, β⟩, s⟩` with `β ∈ {0,1}^k` and `s` a string of `k`
blocks of `m` bits, output `⊕_{t : β_t = 1} s_t` (the subset XOR `S_L` of [PS10, Algorithm 89.6]
for `L = {t | β_t = 1}`, and the inner product `⟨x, r⟩` for `m = 1`). Realised as the guarded
state loop `SelXor.step` run for `|⟨x, start x⟩|` rounds. -/
def selXorFun (x : List Bool) : List Bool :=
  SelXor.out ((gstep SelXor.step SelXor.bound)^[(pairEncode x (SelXor.start x)).length]
    (pairEncode x (SelXor.start x)))

/-- The selective block XOR is polynomial-time. -/
theorem selXorFun_poly : PolyTimeComputable selXorFun :=
  polyTimeComputable_stateIterate SelXor.start_poly SelXor.step_poly SelXor.out_poly SelXor.bound

/-- **The selective block XOR computes the subset XOR**: on the well-formed input
`⟨⟨1^m, β⟩, s⟩` it outputs the encoding of `∑_{t : β_t = 1} s_t` (`Bool` as a Boolean ring).

**Proof sketch.** The genuine orbit is bounded (`SelXor.orbit_length_le`), so the guard never
fires (`StateLoop.gstep_iterate_eq`); the loop runs for `R ≥ k` rounds, is stationary after `k`
(`SelXor.orbit_stable`), and its state after `k` rounds is `SelXor.orbit_eq` with
`SelXor.partialSum_eq`. -/
theorem selXorFun_input (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) :
    selXorFun (SelXor.input m β s) =
      List.ofFn (∑ t ∈ univ.filter (fun t : Fin k => β t = true), s t) := by
  unfold selXorFun
  set R := (pairEncode (SelXor.input m β s) (SelXor.start (SelXor.input m β s))).length with hR
  have hRk : k ≤ R := by
    rw [hR, length_pairEncode, SelXor.input, length_pairEncode, length_pairEncode, List.length_ofFn]
    omega
  rw [gstep_iterate_eq SelXor.start SelXor.step SelXor.bound _ R
    (fun i _ => SelXor.orbit_length_le m β s i) R le_rfl]
  obtain ⟨j, hj⟩ : ∃ j, R = k + j := ⟨R - k, by omega⟩
  rw [hj, SelXor.orbit_stable, SelXor.orbit_eq m β s k le_rfl, SelXor.out, pairSndD_pairEncode,
    pairSndD_pairEncode, pairSndD_pairEncode, SelXor.partialSum_eq]
  congr 2
  refine Finset.filter_congr fun t _ => ?_
  simp [t.isLt]

/-! ## The inner product `⟨x, r⟩` and unary halving -/

/-- The inner-product evaluator on `⟨x, r⟩`: the selective block XOR with one-bit blocks. -/
def ipFun (z : List Bool) : List Bool :=
  selXorFun (pairEncode (pairEncode [true] (pairFstD z)) (pairSndD z))

/-- Composition of polynomial-time functions, in applied form (so that the unifier never
unfolds the outer function; private copy of `ptc_comp` in `Randomized/Closure.lean`). -/
theorem ptcComp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  PolyTimeComputable.comp' hg hf

/-- The inner-product evaluator is polynomial-time. -/
theorem ipFun_poly : PolyTimeComputable ipFun := by
  have h := PolyTimeComputable.comp' (g := selXorFun) selXorFun_poly
    (((polyTimeComputable_const [true]).pairEncode polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  exact h

/-- `⟨x, r⟩ = ∑_{t : x_t = 1} r_t` in the Boolean ring `Bool`. -/
theorem ip_eq_sum_filter {k : ℕ} (x r : Fin k → Bool) :
    HardcoreBit.ip x r = ∑ t ∈ univ.filter (fun t : Fin k => x t = true), r t := by
  rw [HardcoreBit.ip_def, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  cases x t <;> cases r t <;> rfl

/-- **The inner-product evaluator computes `⟨x, r⟩`** on encoded strings of equal length. -/
theorem ipFun_ofFn {k : ℕ} (x r : Fin k → Bool) :
    ipFun (pairEncode (List.ofFn x) (List.ofFn r)) = [HardcoreBit.ip x r] := by
  unfold ipFun
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  have hin : pairEncode (pairEncode [true] (List.ofFn x)) (List.ofFn r) =
      SelXor.input 1 x (fun t (_ : Fin 1) => r t) := by
    rw [SelXor.input, blocksStr_one]
    rfl
  rw [hin, selXorFun_input, ip_eq_sum_filter, List.ofFn_succ, List.ofFn_zero, Finset.sum_apply]

/-- Unary halving `1^n ↦ 1^{⌊n/2⌋}`. -/
def unaryHalf (u : List Bool) : List Bool := List.replicate (u.length / 2) true

/-- The defining equation of `unaryHalf`: `unaryHalf u = List.replicate (u.length / 2) true`. -/
theorem unaryHalf_def (u : List Bool) :
    unaryHalf u =
      (List.replicate (u.length / 2) true) := rfl

/-- Unary halving is polynomial-time: the block map with blocks of two symbols and the constant
emission `[true]` (`Complexity.polyTimeComputable_blockMap`) emits one `true` per full block. -/
theorem unaryHalf_poly : PolyTimeComputable unaryHalf := by
  convert (polyTimeComputable_blockMap (.const 2) (polyTimeComputable_const [true])).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id) using 1
  funext u
  simp only [Function.comp_apply, pairSndD_pairEncode, PolyExpr.eval_const, unaryHalf, id_eq]
  rw [← List.map_eq_flatMap, List.map_const', List.length_range]

end TCSlib.Cryptography
