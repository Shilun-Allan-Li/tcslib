/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Generic tools for Theorem 174.8

Three generic facts used by both directions of [PS10, Theorem 174.8]. None of them is specific
to encryption.

* **Budget reduction** (`buildComp_budget_eq`, `toCompOn_budget_eq`). A machine's computation at
  budget `K ≥ j` that makes at most `j` queries on every path is its computation at budget `j`.
  The simulator of the ideal experiment runs at budget `1`, while T2 builds it at a polynomial
  budget.
* **One-shot coins drawn in advance** (`expect_simulate_eager`). An implementation that samples
  coins `t` at most once, on the call that leaves the "unused" states, has the law of the
  implementations with `t` fixed in advance, averaged over `t`.
* **Chunk maps** (`chunkMap`). A polynomial-time map applied to the consecutive fixed-length
  chunks of a string, concatenated (`polyTimeComputable_chunkMap`, `chunkMap_flatten`). The
  machines of both reductions read and write their tuples of ciphertexts and entries this way.

## Main definitions

* `NMSim.chunkStep`, `NMSim.chunkEmit`, `NMSim.chunkMap`.

## Main results

* `NMSim.buildComp_budget_eq`, `NMSim.toCompOn_budget_eq`.
* `NMSim.expect_toCompOn_outLen`: a machine's output length may be changed along an equality.
* `NMSim.expect_congr_of_allOutputs`, `NMSim.expect_expect_sample`,
  `NMSim.bind_congr_of_allOutputs`.
* `NMSim.expect_simulate_eager`.
* `NMSim.expect_eq_until_bad`: equal until bad, for functions of the final state.
* `NMSim.polyTimeComputable_chunkMap`, `NMSim.chunkMap_flatten`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal B (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Generic.lean`, with every seal candidate of its
full TCSlib import closure (1155 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GGMRed.IsQ _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.advPoly _root_.TCSlib.Cryptography.GGMRed.adviceOf _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.ansMap _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinPoly _root_.TCSlib.Cryptography.GGMRed.coinStr _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.concrete _root_.TCSlib.Cryptography.GGMRed.concrete_iterate.match_1_1 _root_.TCSlib.Cryptography.GGMRed.encState _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.firstRound _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.nextQ _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.orbit_eq_encState.match_1_1 _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.prefMap _root_.TCSlib.Cryptography.GGMRed.pureAt _root_.TCSlib.Cryptography.GGMRed.pureStep _root_.TCSlib.Cryptography.GGMRed.pureStep.match_1 _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rawInput _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.stream _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.valStr _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.IInv _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom.match_1 _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.gB _root_.TCSlib.Cryptography.Games.EffFill.gC _root_.TCSlib.Cryptography.Games.EffFill.gCur _root_.TCSlib.Cryptography.Games.EffFill.gLc _root_.TCSlib.Cryptography.Games.EffFill.gLin _root_.TCSlib.Cryptography.Games.EffFill.gO _root_.TCSlib.Cryptography.Games.EffFill.gPh _root_.TCSlib.Cryptography.Games.EffFill.gS _root_.TCSlib.Cryptography.Games.EffFill.hAct _root_.TCSlib.Cryptography.Games.EffFill.hBound _root_.TCSlib.Cryptography.Games.EffFill.hCtx _root_.TCSlib.Cryptography.Games.EffFill.hMove _root_.TCSlib.Cryptography.Games.EffFill.hNext _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.hRes _root_.TCSlib.Cryptography.Games.EffFill.hRounds _root_.TCSlib.Cryptography.Games.EffFill.hStart _root_.TCSlib.Cryptography.Games.EffFill.hState _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iAnsLen _root_.TCSlib.Cryptography.Games.EffFill.iAsk _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallAct _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCallNext _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinAct _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinNext _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iFixBound _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iNext _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iTree _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_le_length_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.relabel _root_.TCSlib.Cryptography.Games.EffFill.relabelEmit _root_.TCSlib.Cryptography.Games.EffFill.relabelN _root_.TCSlib.Cryptography.Games.EffFill.relabelN_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.InteractiveHandler.rCnt _root_.TCSlib.Cryptography.Games.InteractiveHandler.rI _root_.TCSlib.Cryptography.Games.InteractiveHandler.rL _root_.TCSlib.Cryptography.Games.InteractiveHandler.rS _root_.TCSlib.Cryptography.Games.InteractiveHandler.rU _root_.TCSlib.Cryptography.Games.InteractiveHandler.rW _root_.TCSlib.Cryptography.Games.InteractiveHandler.rX _root_.TCSlib.Cryptography.Games.InteractiveHandler.rZ _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.answer.match_1 _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.buildComp_singleCodec.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.singleCodec _root_.TCSlib.Cryptography.Games.singleCodec.match_1 _root_.TCSlib.Cryptography.Games.toHist _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_prf_of_exists_prg.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmPRF _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ### Budget reduction -/

section Budget

variable {ι α : Type} {spec : OracleSpec ι}

/-- **Budget reduction for `buildComp`.** If the computation of `next` at budget `K` from the log
`hist` makes at most `j ≤ K` queries on every path, it is the computation at budget `j`:
`buildComp next t j hist = buildComp next t K hist`.

**Proof sketch.** Induction on `j`. A final output is the same at every budget. A query at budget
`K` costs `1 ≤ j`, so `j = j' + 1` and `K = K' + 1`; both computations ask the same query and
continue with the same log, at budgets `j'` and `K' ≥ j'`, and the continuation makes at most `j'`
queries. At `j = 0` a query is impossible unless `K = 0`, where both give `timeout`. -/
theorem buildComp_budget_eq (next : QueryLog spec → Move spec α) (t : α) :
    ∀ (j K : ℕ) (hist : QueryLog spec), j ≤ K →
      (buildComp next t K hist).CostBoundedBy (fun _ => 1) j →
      buildComp next t j hist = buildComp next t K hist := by
  intro j
  induction j with
  | zero =>
    intro K hist _ hc
    cases h : next hist with
    | ret a =>
      cases K with
      | zero => rfl
      | succ K => rw [buildComp_zero_of_ret h, buildComp_succ_of_ret h]
    | query i x =>
      cases K with
      | zero => rfl
      | succ K =>
        rw [buildComp_succ_of_query h, OracleComp.costBoundedBy_query] at hc
        exact absurd hc.1 (by omega)
  | succ j ih =>
    intro K hist hK hc
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    cases h : next hist with
    | ret a => rw [buildComp_succ_of_ret h, buildComp_succ_of_ret h]
    | query i x =>
      rw [buildComp_succ_of_query h] at hc ⊢
      rw [buildComp_succ_of_query h]
      rw [OracleComp.costBoundedBy_query] at hc
      congr 1
      funext y
      exact ih K _ (by omega) (by simpa using hc.2 y)

/-- **Budget reduction for a machine:** if `D`'s computation on `x` at budget `K ≥ j` makes at
most `j` queries on every path, it is `D`'s computation at budget `j`. -/
theorem toCompOn_budget_eq (D : NUPPT) {β : Type} (codec : MachineCodec spec β) (n j K : ℕ)
    (x : List Bool) (r : D.Coins n) (hjK : j ≤ K)
    (hc : (D.toCompOn codec n K x r).CostBoundedBy (fun _ => 1) j) :
    D.toCompOn codec n j x r = D.toCompOn codec n K x r := by
  rw [NUPPT.toCompOn_eq] at hc ⊢
  rw [NUPPT.toCompOn_eq]
  exact buildComp_budget_eq _ _ j K [] hjK hc

end Budget

/-! ### Expectations on the possible outputs -/

section Expect

variable {α β : Type}

/-- Two functions that agree on every possible output have the same expectation. -/
theorem expect_congr_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a = g a) : ProbComp.expect c f = ProbComp.expect c g :=
  le_antisymm (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).le)
    (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).ge)

/-- **Fubini for a uniform sample:** `𝔼_c[𝔼_{t ← T}[h a t]] = 𝔼_{t ← T}[𝔼_c[h a t]]`. -/
theorem expect_expect_sample (c : ProbComp α) (T : Type) [Fintype T] [Nonempty T]
    (h : α → T → ℝ) :
    ProbComp.expect c (fun a => ProbComp.expect (ProbComp.sample T) (h a)) =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect c fun a => h a t := by
  simp only [ProbComp.expect_sample]
  rw [ProbComp.expect_const_mul, ProbComp.expect_sum]

/-- Two continuations that agree on every possible output give the same computation:
`c.bind f = c.bind g` when `f a = g a` whenever `P a`, and `c.AllOutputs P`. -/
theorem bind_congr_of_allOutputs {ι : Type} {spec : OracleSpec ι} {c : OracleComp spec α}
    {P : α → Prop} (hc : c.AllOutputs P) {f g : α → OracleComp spec β}
    (h : ∀ a, P a → f a = g a) : c.bind f = c.bind g := by
  induction c with
  | pure a =>
    rw [OracleComp.pure_bind, OracleComp.pure_bind]
    exact h a (OracleComp.allOutputs_pure.1 hc)
  | query i x k ih =>
    rw [OracleComp.query_bind, OracleComp.query_bind]
    congr 1
    funext y
    exact ih y (OracleComp.allOutputs_query.1 hc y)

end Expect

/-- **Changing a machine's output length along `d = d'`** keeps the law of its output read as a
list: `𝔼[G (⟦p.1⟧, p.2)]` over the runs through `bitCodec ins outs d` and `bitCodec ins outs d'`
agree. -/
theorem expect_toCompOn_outLen {k : ℕ} {ins outs : Fin k → ℕ} {σ : Type}
    (O : QueryImpl (bitSpec ins outs) σ unifSpec) (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (s : σ) {d d' : ℕ} (hd : d = d') (G : List Bool × σ → ℝ) :
    ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d) n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) =
      ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  subst hd
  rfl

/-! ### One-shot coins drawn in advance -/

section Eager

variable {ι σ α T : Type} {spec : OracleSpec ι} [Fintype T] [Nonempty T]

/-- From a used state, an implementation that agrees with `O` there simulates like `O`. -/
private theorem simulate_eq_of_used (O O' : QueryImpl spec σ unifSpec) (used : σ → Prop)
    (hused : ∀ i x s, used s → O' i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (c : OracleComp spec α) {s : σ} (hs : used s) : simulate O' c s = simulate O c s := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, hused i x s hs]
    exact bind_congr_of_allOutputs (hstick i x s hs) fun p hp => ih p.1 hp

/-- **One-shot coins drawn in advance.** Let `O` be an implementation and `OE t` its variants with
coins `t ∈ T` fixed in advance, and let `used` mark the states after the coins are spent:
- from a used state, `OE t` is `O`, and `O` keeps the state used;
- from an unused state, a call either does not use the coins (`OE t` is `O` for every `t`, and the
  state stays unused), or it is the one that spends them (`O` samples `t` and runs `OE t`, and
  every successor is used).

Then from an unused state, `O`'s simulation has the law of `OE t`'s, averaged over `t`:
`𝔼[G(simulate O c s)] = 𝔼_{t ← T} 𝔼[G(simulate (OE t) c s)]`.

**Proof sketch.** Induction on `c`. From used states the two simulations coincide
(`simulate_eq_of_used`). At a query from an unused state: in the first case, rewrite the call,
apply the induction hypothesis at the (unused) successors and exchange the expectations
(`expect_expect_sample`); in the second, expand `O`'s sample and conclude from the coincidence at
the (used) successors. -/
theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (hfresh : ∀ i x s, ¬ used s →
      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
    ProbComp.expect (simulate O c s) G =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G := by
  induction c generalizing s with
  | pure a =>
    simp only [simulate_pure, ProbComp.expect_pure]
    exact (ProbComp.expect_const _ _).symm
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    rcases hfresh i x s hs with h | ⟨h, hu⟩
    · have hO : ∀ t, OE t i x s = O i x s := fun t => (h t).1
      have hun : (O i x s).AllOutputs fun p => ¬ used p.2 :=
        (h (Classical.arbitrary T)).2
      simp only [hO]
      rw [expect_congr_of_allOutputs hun fun p hp => ih p.1 hp, expect_expect_sample]
    · rw [h, ProbComp.expect_bind]
      refine congrArg _ (funext fun t => ?_)
      refine expect_congr_of_allOutputs (hu t) fun p hp => ?_
      rw [simulate_eq_of_used O (OE t) used (hused t) hstick _ hp]

end Eager

/-! ### Equal until bad, for functions of the final state -/

section UntilBad

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- **Equal until bad, in expectation, for functions of the output and the final state.** Let two
implementations give, from every good state, the same law to good successors, and let each keep
bad states bad. Then from a good state, for every function `G` of the output and the final state,
`𝔼[G · 1_{good}]` is the same under both simulations. This generalizes `prob_eq_until_bad`
(`Games/Hopping.lean`), whose events read only the output.

**Proof sketch.** Induction on the computation. From a bad successor the continuation's value is
`0` on both sides (`simulate_allOutputs_bad`); from a good one the two values agree by induction;
so both expectations only see the values at good successors, which `hagree` equates. -/
theorem expect_eq_until_bad {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop)
    [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ bad s) :
    ProbComp.expect (simulate impl₀ c s) (fun r => if bad r.2 then 0 else G r) =
      ProbComp.expect (simulate impl₁ c s) (fun r => if bad r.2 then 0 else G r) := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    have hz : ∀ (impl : QueryImpl spec σ unifSpec),
        (∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2) →
        ∀ ys : spec.rng i × σ, bad ys.2 →
          ProbComp.expect (simulate impl (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
            0 := by
      intro impl hst ys hb
      rw [expect_congr_of_allOutputs (simulate_allOutputs_bad bad hst _ hb)
        (g := fun _ => 0) fun r hr => if_pos hr, ProbComp.expect_const]
    have h0 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₀ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
              (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₀ hstick₀ ys hb]
      · rw [if_neg hb, ih ys.1 hb]
    have h1 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
              (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₁ hstick₁ ys hb]
      · rw [if_neg hb]
    rw [funext h0, hagree i x s hs, ← funext h1]

end UntilBad

/-! ### Chunk maps -/

section Chunks

/-- One step of a chunk map on `⟨ctx, w⟩` with `ctx = ⟨1^n, _⟩`: drop the first `c(n)` bits of `w`:
`chunkStep c x = ⟨fst x, (snd x).drop c(|fst (fst x)|)⟩`. -/
def chunkStep (c : PolyExpr) (x : List Bool) : List Bool :=
  pairEncode (pairFstD x) ((pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length))

/-- `chunkStep c x = ⟨fst x, (snd x).drop c(|fst (fst x)|)⟩`. -/
theorem chunkStep_eq (c : PolyExpr) (x : List Bool) :
    chunkStep c x =
      pairEncode (pairFstD x) ((pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length)) :=
  rfl

/-- The emission of a chunk map on `⟨ctx, w⟩`: nothing on `w = []`, and `f ctx` of the first
`c(n)` bits of `w` otherwise. -/
def chunkEmit (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    List Bool :=
  if decide (pairSndD x = []) then []
  else f (pairFstD x) ((pairSndD x).take (c.eval (pairFstD (pairFstD x)).length))

/-- `chunkEmit c f x = if snd x = [] then [] else f (fst x) ((snd x).take c(|fst (fst x)|))`. -/
theorem chunkEmit_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    chunkEmit c f x = if decide (pairSndD x = []) then []
      else f (pairFstD x) ((pairSndD x).take (c.eval (pairFstD (pairFstD x)).length)) :=
  rfl

/-- **The chunk map** of `f` with chunk length `c`, on `x = ⟨ctx, w⟩` with `ctx = ⟨1^n, _⟩`: the
concatenation of `f ctx` over the consecutive `c(n)`-bit chunks of `w`, computed by `|x| + 1`
rounds of `chunkStep`: `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i =>
chunkEmit c f (chunkStep c)^[i] x`. -/
def chunkMap (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x)

/-- `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`. -/
theorem chunkMap_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    chunkMap c f x =
      (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x) :=
  rfl

/-- One step never makes a word longer than `max |x| 2` (a malformed word becomes `⟨[], []⟩`). -/
private theorem length_chunkStep_le (c : PolyExpr) (x : List Bool) :
    (chunkStep c x).length ≤ max x.length 2 := by
  rw [chunkStep_eq, length_pairEncode, List.length_drop]
  by_cases h : pairDecode x = none
  · rw [pairFstD_of_pairDecode_eq_none h, pairSndD_of_pairDecode_eq_none h]
    simp only [List.length_nil]
    omega
  · obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.1 h
    rw [eq_pairEncode_of_pairDecode x a b hab, pairFstD_pairEncode, pairSndD_pairEncode,
      length_pairEncode]
    omega

/-- The iterated step keeps words within `|x| + 2` bits. -/
private theorem length_iterate_chunkStep_le (c : PolyExpr) (x : List Bool) (i : ℕ) :
    ((chunkStep c)^[i] x).length ≤ x.length + 2 := by
  suffices h : ((chunkStep c)^[i] x).length ≤ max x.length 2 by omega
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_chunkStep_le c _).trans (max_le ih (le_max_right _ _))

/-- **Chunk maps are polynomial-time** when `f` is, read as a function of `⟨ctx, chunk⟩`
(`Complexity.polyTimeComputable_iterateEmit` with the step `chunkStep`, which never lengthens a
word, and `|x|` rounds).

**Proof sketch.** The step (keep `ctx`, drop `c(n)` bits) and the emission (`[]` on an empty
rest, else `f ctx` of the next `c(n)` bits) are polynomial-time by the pair readers,
`pairTakePoly`/`pairDropPoly` and `polyTimeComputable_ite`. The iterates stay within `|x| + 2`
bits (`length_iterate_chunkStep_le`), so `polyTimeComputable_iterateEmit` gives `chunkMap_eq`. -/
theorem polyTimeComputable_chunkMap (c : PolyExpr) {f : List Bool → List Bool → List Bool}
    (hf : PolyTimeComputable fun z => f (pairFstD z) (pairSndD z)) :
    PolyTimeComputable (chunkMap c f) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : PolyTimeComputable fun x : List Bool =>
      pairEncode (pairFstD (pairFstD x)) (pairSndD x) := (hF.comp hF).pairEncode hD
  have hdrop : PolyTimeComputable fun x : List Bool =>
      (pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length) :=
    ((polyTimeComputable_pairDropPoly c).comp hcut).congr fun x => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have htake : PolyTimeComputable fun x : List Bool =>
      (pairSndD x).take (c.eval (pairFstD (pairFstD x)).length) :=
    ((polyTimeComputable_pairTakePoly c).comp hcut).congr fun x => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hstep : PolyTimeComputable (chunkStep c) := hF.pairEncode hdrop
  have hemit : PolyTimeComputable (chunkEmit c f) :=
    polyTimeComputable_ite (polyTimeComputable_isNil.comp hD) (polyTimeComputable_const [])
      ((hf.comp (hF.pairEncode htake)).congr fun x => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
  exact (polyTimeComputable_iterateEmit hstep hemit .var (.add .var (.const 2))
    (fun x i _ => by
      rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      exact length_iterate_chunkStep_le c x i)).congr
    fun x => by rw [PolyExpr.eval_var, chunkMap_eq]

/-- Reading the suffixes of a list within at least its length many steps (DL-30–36 overlap: the
general form of `Forward`'s private `flatMap_range_drop`, with the reading of a nonempty suffix
assumed only for the list's members). -/
private theorem flatMap_range_drop {β : Type} (F : List β → List Bool) (g : β → List Bool)
    (hnil : F [] = []) :
    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
  intro l
  induction l with
  | nil =>
    intro _ m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, hnil]
  | cons e t ih =>
    intro hcons m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      hcons e List.mem_cons_self, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
      (by rw [List.length_cons] at hm; omega)

/-- **The chunk map of a concatenation of chunks:** if every chunk has `c(n) > 0` bits, the chunk
map of `⟨⟨1^n, e⟩, chunks.flatten⟩` is the concatenation of `f ⟨1^n, e⟩` over the chunks.

**Proof sketch.** The `i`-th step leaves `(chunks.drop i).flatten` (dropping a first chunk of
`c(n)` bits), whose emission is `f` of the `i`-th chunk while chunks remain and `[]` afterwards;
there are at most `|x| + 1` chunks since each has a bit. -/
theorem chunkMap_flatten (c : PolyExpr) (f : List Bool → List Bool → List Bool) (n : ℕ)
    (e : List Bool) (chunks : List (List Bool)) (hlen : ∀ ch ∈ chunks, ch.length = c.eval n)
    (hpos : 0 < c.eval n) :
    chunkMap c f (pairEncode (pairEncode (List.replicate n true) e) chunks.flatten) =
      (chunks.map (f (pairEncode (List.replicate n true) e))).flatten := by
  set ctx := pairEncode (List.replicate n true) e
  have hit : ∀ i, (chunkStep c)^[i] (pairEncode ctx chunks.flatten) =
      pairEncode ctx (chunks.drop i).flatten := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, chunkStep_eq, pairFstD_pairEncode,
        pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, ← List.tail_drop]
      cases h : chunks.drop i with
      | nil => rw [List.flatten_nil, List.drop_nil, List.tail_nil, List.flatten_nil]
      | cons ch rest =>
        have hch : ch.length = c.eval n :=
          hlen ch (List.mem_of_mem_drop (h ▸ List.mem_cons_self))
        rw [List.flatten_cons, List.tail_cons, ← hch, List.drop_left]
  have hlen' : chunks.length ≤ (pairEncode ctx chunks.flatten).length + 1 := by
    have : chunks.length ≤ chunks.flatten.length := by
      rw [List.length_flatten]
      clear hit
      induction chunks with
      | nil => exact le_rfl
      | cons ch rest ih =>
        rw [List.map_cons, List.sum_cons, List.length_cons]
        have := hlen ch List.mem_cons_self
        have := ih fun ch' h' => hlen ch' (List.mem_cons_of_mem _ h')
        omega
    rw [length_pairEncode]
    omega
  rw [chunkMap_eq]
  simp only [hit]
  rw [flatMap_range_drop (fun l => chunkEmit c f (pairEncode ctx l.flatten)) (f ctx)
    (by
      show chunkEmit c f (pairEncode ctx ([] : List (List Bool)).flatten) = []
      rw [List.flatten_nil, chunkEmit_eq, pairSndD_pairEncode, if_pos (decide_eq_true rfl)])
    chunks (fun ch hch t => ?_) _ hlen', List.flatMap_def]
  have hl := hlen ch hch
  have hne : ch ++ t.flatten ≠ [] := fun h => by
    rw [List.append_eq_nil_iff] at h
    rw [h.1, List.length_nil] at hl
    omega
  show chunkEmit c f (pairEncode ctx (ch :: t).flatten) = f ctx ch
  rw [chunkEmit_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
    List.length_replicate, List.flatten_cons, if_neg (by simpa using hne), ← hl, List.take_left]

end Chunks

end TCSlib.Cryptography.Composability.NMSim
