/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: machines behind the honest parties

Proof infrastructure for the efficiency theorems of `ThreeColoring/Protocol.lean`
(`colProver_efficient`, `colVerifier_efficient`, `colProverRep_efficient`,
`colVerifierRep_efficient`, inventory item Inf-4.2) and for the decider clause of
`R3COL_witnessRelation` [PS10, §4.7, Protocol 127.5]. The honest parties of the protocol
are exhibited as polynomial-time functions of the interactive machine layout
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`ilayout`, `efficient_of_polyTime`), assembled from
the unary FP toolkit of `ZeroKnowledge/EncodingMachines.lean` (numbers travel in unary,
`polyTimeComputable_firstIdx`, `polyTimeComputable_of_getD`, `polyTimeComputable_stateFind`)
and the typed coin cuts of `Complexity/Randomized/Primitives.lean`.

This file holds the generic pieces (the parties themselves as string functions are in
`ThreeColoring/Parties.lean`, the identification with the strategies of `Protocol.lean` in
`ThreeColoring/ProtocolProofs.lean`):

* counted loops bounded along the genuine orbit only (`polyTimeComputable_loopState'`),
  concatenating loops over a data-dependent range (`polyTimeComputable_flatMap_range`), and
  the iterated second projection (`iterSnd_poly`, the message-selection `msgAt`);
* zero padding (`padTo`) with the identities `List.ofFn (padFin L w) = padTo L w` and
  `List.ofFn (fun j => r.getD (b + j) false) = padTo L (r.drop b)` that turn the parties'
  typed values and randomness blocks into string operations;
* the **numeric model of the edge list**: `edgeList G` is, through the index
  `(u, v) ↦ v + n u` of `finProdFinEquiv`, the increasing list of positions `j < n²` whose
  bit of the adjacency matrix is set (`map_edgeList`); hence `edgeCount G` is the bit count
  `countTrue` and `edgeOf G e` is the `e`-th set position `nthTrue` (`edgeCount_eq`,
  `edgeOf_val`), both computed by counted loops and bounded searches;
* the **numeric model of the samplers**: `bitsToNat` of a tape window is the loop value
  `natOfBits`, and the rejection sampler is the first accepted trial (`sampleVal`,
  `map_val_sampleIdx_getD`); the colour permutation reaches the machine as the six-bit table
  `permTable π` of the images of the three colours (`permTable_samplePerm3`), a table lookup
  on the sampled index;
* colours as numbers: `decColoring`, `decColor` and `encColor` numerically (`colorVal`,
  `encColorOfVal`, `colorFromTable`).

## Main definitions

* `ColMachines.ilayout`, `argX`, `argZ`, `argM`, `padTo`, `countTrue`, `nthTrue`, `natOfBits`,
  `firstTrial`, `sampleVal`, `permTable`, `tableOfIdx`, `colorFromTable`, `colorVal`,
  `encColorOfVal` — the layout, padding, counting and sampler models, colours as numbers.

## Main results

* `TCSlib.Cryptography.ColMachines.polyTimeComputable_loopState'`,
  `ColMachines.polyTimeComputable_flatMap_range`, `ColMachines.iterSnd_poly` — loops.
* `TCSlib.Cryptography.ColMachines.map_edgeList`, `ColMachines.edgeCount_eq`,
  `ColMachines.edgeOf_val` — the numeric model of the edge list.
* `TCSlib.Cryptography.ColMachines.map_val_sampleIdx_getD`, `ColMachines.permTable_samplePerm3`
  — the numeric model of the samplers.
* `TCSlib.Cryptography.ColMachines.countTrue_poly`, `ColMachines.nthTrue_poly`,
  `ColMachines.natOfBits_poly`, `ColMachines.sampleVal_poly`, `ColMachines.tableOfIdx_poly`,
  `ColMachines.colorVal_poly`, `ColMachines.encColorOfVal_poly` — the unary machines.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! Seal B (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean`, with every seal candidate of its
full TCSlib import closure (991 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.BitHiding _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.arg _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.emit _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.init _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.loopOut _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.p₁ _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.p₂ _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.p₃ _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.st _root_.TCSlib.Cryptography.CommitmentLemmas.ComLoop.step _root_.TCSlib.Cryptography.CommitmentLemmas.pairSpliceFun _root_.TCSlib.Cryptography.CommitmentLemmas.spliceFun _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.acc _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.out _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.start _root_.TCSlib.Cryptography.EncodingMachines.CountLoop.step _root_.TCSlib.Cryptography.EncodingMachines.bitsToNat_eq_blockVal.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.blockVal _root_.TCSlib.Cryptography.EncodingMachines.blockVal_lt.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.cbound _root_.TCSlib.Cryptography.EncodingMachines.cstep _root_.TCSlib.Cryptography.EncodingMachines.divNum _root_.TCSlib.Cryptography.EncodingMachines.findSome?_range_eq.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.firstIdx _root_.TCSlib.Cryptography.EncodingMachines.firstIdx_congr.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.firstIdx_congr.match_1_3 _root_.TCSlib.Cryptography.EncodingMachines.flatMap_range_ite_eq.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.foldr_swap_val.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.fyApply _root_.TCSlib.Cryptography.EncodingMachines.fyFail _root_.TCSlib.Cryptography.EncodingMachines.fyIter _root_.TCSlib.Cryptography.EncodingMachines.fyIter_le.match_1_1 _root_.TCSlib.Cryptography.EncodingMachines.fyTarget _root_.TCSlib.Cryptography.EncodingMachines.isBij _root_.TCSlib.Cryptography.EncodingMachines.loopState _root_.TCSlib.Cryptography.EncodingMachines.loopState.match_1 _root_.TCSlib.Cryptography.EncodingMachines.modNum _root_.TCSlib.Cryptography.EncodingMachines.offsetVal _root_.TCSlib.Cryptography.EncodingMachines.permFromCoinsNum _root_.TCSlib.Cryptography.EncodingMachines.permInvNum _root_.TCSlib.Cryptography.EncodingMachines.permNum _root_.TCSlib.Cryptography.EncodingMachines.rowFirst _root_.TCSlib.Cryptography.EncodingMachines.rowInv _root_.TCSlib.Cryptography.EncodingMachines.rowMap _root_.TCSlib.Cryptography.EncodingMachines.swapNum _root_.TCSlib.Cryptography.EncodingMachines.trialIdx _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Graph.ofSimpleGraph _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.IP _root_.TCSlib.Cryptography.InteractiveProof.exists_accept.match_1_1 _root_.TCSlib.Cryptography.InteractiveProof.exists_accept.match_1_3 _root_.TCSlib.Cryptography.InteractiveProofErr.exists_accept.match_1_1 _root_.TCSlib.Cryptography.InteractiveProofErr.exists_accept.match_1_3 _root_.TCSlib.Cryptography.L3COL _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.ProperColoring _root_.TCSlib.Cryptography.Protocol.ProverBounded _root_.TCSlib.Cryptography.Protocol.ProverBounded.exists_complete.match_1_1 _root_.TCSlib.Cryptography.Protocol.execution _root_.TCSlib.Cryptography.Protocol.outP _root_.TCSlib.Cryptography.Protocol.outV _root_.TCSlib.Cryptography.Protocol.transcript _root_.TCSlib.Cryptography.Protocol.transcriptWith _root_.TCSlib.Cryptography.Protocol.viewP _root_.TCSlib.Cryptography.Protocol.viewV _root_.TCSlib.Cryptography.Protocol.withV _root_.TCSlib.Cryptography.Protocol.withV_vCoinsEquiv _root_.TCSlib.Cryptography.R3COL _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.Strategy.Efficient _root_.TCSlib.Cryptography.Strategy.ReadsPrefix _root_.TCSlib.Cryptography.Strategy.coinLen _root_.TCSlib.Cryptography.Strategy.encodeMsgs _root_.TCSlib.Cryptography.Strategy.ofNUPPT _root_.TCSlib.Cryptography.Strategy.out _root_.TCSlib.Cryptography.ThreeColorable _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.View.encode _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitCom _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinTable _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decColor _root_.TCSlib.Cryptography.decColoring _root_.TCSlib.Cryptography.decGraph _root_.TCSlib.Cryptography.decPerm _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.edgeAt _root_.TCSlib.Cryptography.edgeIdxOfMsg _root_.TCSlib.Cryptography.edgeList _root_.TCSlib.Cryptography.edgeMsg _root_.TCSlib.Cryptography.edgeOf _root_.TCSlib.Cryptography.encColor _root_.TCSlib.Cryptography.encColoring _root_.TCSlib.Cryptography.encGraph _root_.TCSlib.Cryptography.encPerm _root_.TCSlib.Cryptography.exec _root_.TCSlib.Cryptography.exec.match_1 _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.fisherYates _root_.TCSlib.Cryptography.fisherYates_injOn.match_1_1 _root_.TCSlib.Cryptography.foldr_swap_succ.match_1_1 _root_.TCSlib.Cryptography.fyOffsets _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.liftSucc _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.moverIsV _root_.TCSlib.Cryptography.multiCom _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.npProtocol _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpCom _root_.TCSlib.Cryptography.owpComAt _root_.TCSlib.Cryptography.owpComLen _root_.TCSlib.Cryptography.owpComStr _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padColor _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.pairHybrid _root_.TCSlib.Cryptography.pairRed _root_.TCSlib.Cryptography.pairTuple _root_.TCSlib.Cryptography.perm3Equiv _root_.TCSlib.Cryptography.permBits _root_.TCSlib.Cryptography.permFromCoins _root_.TCSlib.Cryptography.permGraph _root_.TCSlib.Cryptography.permTrials _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.prod_sub_eq_factorial.match_1_1 _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.sampleEdgeIdx _root_.TCSlib.Cryptography.sampleIdx _root_.TCSlib.Cryptography.samplePerm3 _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.witnessLanguage _root_.TCSlib.Cryptography.witnessSet _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ### Generic tools -/

/-- Polynomial-time computability transfers along pointwise equality (the reversed-equality
form of `PolyTimeComputable.congr`). -/
theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g :=
  hf.congr fun w => (h w).symm

/-- Composition of polynomial-time functions in applied form (`fun z => g (f z)` rather than
`g ∘ f`, so that later unifications never have to unfold `Function.comp` against a large
definition). -/
theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  PolyTimeComputable.comp' hg hf

/-- **Counted loops bounded along the genuine orbit:** `EncodingMachines.polyTimeComputable_loopState`
with the length bound required only of the states `loopState upd init x i`, `i ≤ N x`
(the update may lengthen arbitrary words). **Proof sketch.** Same proof: a state loop
(`EncodingMachines.polyTimeComputable_stateFind`, data in `EncodingMachines.CountLoop`) whose
states `⟨1^i, loopState upd init x i⟩` (`CountLoop.orbit_eq`) are bounded by `hstate`. -/
theorem polyTimeComputable_loopState' {upd init : List Bool → List Bool}
    (hupd : PolyTimeComputable upd) (hinit : PolyTimeComputable init)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun x => List.replicate (N x) true)
    (B : PolyExpr)
    (hstate : ∀ x i, i ≤ N x → (loopState upd init x i).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => loopState upd init x (N x) := by
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have hNR : ∀ x, N x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hbound : ∀ x i, i ≤ N x →
      (orbit (CountLoop.start init) (CountLoop.step upd) x i).length ≤
        (PolyExpr.add (.mul (.const 2) (PolyExpr.normal C c)) (.add (.const 2) B)).eval
          x.length := by
    intro x i hi
    rw [CountLoop.orbit_eq, length_pairEncode, List.length_replicate]
    have h1 := hstate x i hi
    have h2 := hNR x
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hfirst : ∀ x i, i < N x →
      CountLoop.acc N (pairEncode x (orbit (CountLoop.start init) (CountLoop.step upd) x i)) =
        false := by
    intro x i hi
    rw [CountLoop.orbit_eq]
    simp [CountLoop.acc_def, hi]
  have hlast : ∀ x, CountLoop.acc N
      (pairEncode x (orbit (CountLoop.start init) (CountLoop.step upd) x (N x))) = true := by
    intro x
    rw [CountLoop.orbit_eq]
    simp [CountLoop.acc_def]
  have h := EncodingMachines.polyTimeComputable_stateFind (CountLoop.start_poly hinit)
    (CountLoop.step_poly hupd) (CountLoop.acc_poly hN) CountLoop.out_poly (PolyExpr.normal C c) _ N
    hNR hbound hfirst hlast
  convert h using 1
  funext x
  rw [CountLoop.orbit_eq]
  simp [CountLoop.out_def]

/-- Emitting `E i` at the indices `i < L` of `List.range N` gives the concatenation of the
`E i` over `i < min N L` (`EncodingMachines.flatMap_range_ite_eq` for arbitrary chunks). -/
theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
      (List.range (min N L)).flatMap E
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite E L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]

/-- **Concatenating loops over a data-dependent range:** if the chunk `E z i` is a
polynomial-time function of `⟨1^i, z⟩` and the range `n z` is a unary function, then
`z ↦ E z 0 ++ ⋯ ++ E z (n z - 1)` is polynomial-time computable. **Proof sketch.** An instance of
`Complexity.polyTimeComputable_iterateEmit` on the counter step `EncodingMachines.cstep` (as
`EncodingMachines.polyTimeComputable_of_getD`), emitting `E z i` while `i < n z`
(`flatMap_range_ite`). -/
theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
  obtain ⟨C, c, hC⟩ := hn.output_length_le
  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD) (hn.comp polyTimeComputable_pairSndD)
  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  convert hL.comp hpre using 1
  funext z
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]

/-- **The iterated second projection** `pairSndD^[i z] (s z)` is polynomial-time for a
polynomial-time `s` and a unary `i`. **Proof sketch.** A counted loop
(`polyTimeComputable_loopState'`) whose `j`-th state is `pairSndD^[j] (s z)`, never longer than
`|s z|` (`length_pair_components_le`). -/
theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
  have hupd : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hclosed : ∀ z j, loopState (fun w => pairSndD (pairSndD (pairSndD w))) s z j =
      pairSndD^[j] (s z) := by
    intro z j
    induction j with
    | zero => rw [loopState_zero]; rfl
    | succ j ih =>
      rw [loopState_succ, ih, pairSndD_pairEncode, pairSndD_pairEncode,
        Function.iterate_succ_apply']
  have hlen : ∀ (w : List Bool) (j : ℕ), (pairSndD^[j] w).length ≤ w.length := by
    intro w j
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ((Nat.le_add_left _ _).trans (length_pair_components_le _)).trans ih
  obtain ⟨C, c, hC⟩ := hs.output_length_le
  have h := polyTimeComputable_loopState' hupd hs hi (PolyExpr.normal C c) fun z j _ => by
    rw [hclosed]
    exact (hlen _ _).trans (by simpa [PolyExpr.eval_normal] using hC z)
  convert h using 1
  funext z
  rw [hclosed]

/-! ### The interactive layout and its projections -/

/-- The interactive machine layout of a strategy activation,
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`Strategy.ofNUPPT`, `NUPPT.runAtL`). -/
def ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) : List Bool :=
  NUPPT.layout (List.replicate x.length true)
    (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r

/-- The defining equation of `ilayout`: `ilayout x z hist r = NUPPT.layout
(List.replicate x.length true) (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r`. -/
theorem ilayout_def (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    ilayout x z hist r =
      (NUPPT.layout (List.replicate x.length true)
        (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) := rfl

/-- A strategy whose next-message function is a polynomial-time function `F` of the machine
layout `ilayout x z hist r` is efficient: `NUPPT.ofPolyTimeUniform` of `F` with the strategy's
coin polynomial is the uniform machine computing it (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem efficient_of_polyTime (S : Strategy) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F)
    (h : ∀ x z r hist, S.next x z r hist = F (ilayout x z hist r)) : S.Efficient :=
  (Strategy.efficient_iff S).2 ⟨NUPPT.ofPolyTimeUniform hF S.coins, NUPPT.ofPolyTimeUniform_uniform hF _,
    (NUPPT.coins_ofPolyTimeUniform hF S.coins).symm,
    fun x z r hist => by
      rw [h, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, ilayout_def, NUPPT.layout_eq,
        NUPPT.advInput_eq]⟩

/-- The common-input slot of the interactive layout. -/
def argX (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inArg w))

/-- The defining equation of `argX`. -/
theorem argX_eq (w : List Bool) : argX w = pairFstD (pairFstD (NUPPT.inArg w)) := rfl

/-- The auxiliary-input slot of the interactive layout. -/
def argZ (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inArg w))

/-- The encoded-messages slot of the interactive layout. -/
def argM (w : List Bool) : List Bool := pairSndD (NUPPT.inArg w)

/-- The common input of a layout. -/
@[simp] theorem argX_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argX (ilayout x z hist r) = x := by
  simp [argX, ilayout]

/-- The auxiliary input of a layout. -/
@[simp] theorem argZ_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argZ (ilayout x z hist r) = z := by
  simp [argZ, ilayout]

/-- The encoded messages of a layout. -/
@[simp] theorem argM_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argM (ilayout x z hist r) = Strategy.encodeMsgs hist := by
  simp [argM, ilayout]

/-- The coins of a layout. -/
@[simp] theorem inCoins_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    NUPPT.inCoins (ilayout x z hist r) = r := by
  simp [ilayout]

/-- The common-input projection is polynomial-time. -/
theorem argX_poly : PolyTimeComputable argX :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The auxiliary-input projection is polynomial-time. -/
theorem argZ_poly : PolyTimeComputable argZ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The messages projection is polynomial-time. -/
theorem argM_poly : PolyTimeComputable argM :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg

/-! ### Zero padding -/

/-- `L` zeros from a unary length (the bit-extraction principle with the constant bit `0`). -/
theorem zeros_poly {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => List.replicate (L x) false := by
  refine polyTimeComputable_of_getD (F := fun x => List.replicate (L x) false) ?_ ?_
  · convert polyTimeComputable_const [false] using 1
    funext w
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  · simpa using hL

/-- Padding a word with zeros to length `L` (and truncating to `L`): the string form of the
typed value `padFin L w` (`ofFn_padFin`). -/
def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- Padding to a unary length is polynomial-time. -/
theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => padTo (L x) (s x) :=
  truncate_poly (hs.append (zeros_poly hL)) hL

/-- The padded word has length `L`. -/
theorem length_padTo (L : ℕ) (w : List Bool) : (padTo L w).length = L := by
  simp [padTo]

/-- The bits of the padded word below `L` are the bits of `w` read with default `false`. -/
theorem getD_padTo (L : ℕ) (w : List Bool) {i : ℕ} (hi : i < L) :
    (padTo L w).getD i false = w.getD i false := by
  rw [padTo, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_append,
    List.getD_eq_getElem?_getD]
  split_ifs with h
  · rfl
  · have hw : w[i]? = none := List.getElem?_eq_none_iff.2 (by omega)
    rw [hw, List.getElem?_replicate]
    split_ifs <;> rfl

/-- The typed value `padFin L w` as a string is the padded word. -/
theorem ofFn_padFin (L : ℕ) (w : List Bool) : List.ofFn (padFin L w) = padTo L w := by
  apply List.ext_getElem
  · simp [length_padTo]
  · intro i h1 h2
    rw [List.getElem_ofFn, padFin_apply]
    rw [← getD_padTo L w (by simpa [length_padTo] using h2), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

/-- A block of `L` bits read with default `false` from position `b` of a tape is the padded
`drop`. -/
theorem ofFn_getD_add (r : List Bool) (b L : ℕ) :
    List.ofFn (fun j : Fin L => r.getD (b + j) false) = padTo L (r.drop b) := by
  rw [← ofFn_padFin]
  congr 1
  funext j
  simp [padFin_def, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ### Counting set bits -/

/-- The number of set bits among the first `j` positions of `x` (read with default `false`). -/
def countTrue (x : List Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => countTrue x j + (x.getD j false).toNat

/-- No bits are counted in the empty prefix. -/
@[simp] theorem countTrue_zero (x : List Bool) : countTrue x 0 = 0 := rfl

/-- The count of the first `j + 1` bits adds bit `j`. -/
@[simp] theorem countTrue_succ (x : List Bool) (j : ℕ) :
    countTrue x (j + 1) = countTrue x j + (x.getD j false).toNat := rfl

/-- At most `j` of the first `j` bits are set. -/
theorem countTrue_le (x : List Bool) (j : ℕ) : countTrue x j ≤ j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [countTrue_succ]
    have := Bool.toNat_le (x.getD j false)
    omega

/-- The bit count is monotone in the prefix length. -/
theorem countTrue_mono (x : List Bool) {i j : ℕ} (h : i ≤ j) : countTrue x i ≤ countTrue x j := by
  induction j with
  | zero =>
    rw [Nat.le_zero.1 h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · rw [countTrue_succ]
      exact (ih (by omega)).trans (Nat.le_add_right _ _)
    · rw [show i = j + 1 by omega]

/-- The unary bit count of a prefix of a polynomial-time word is polynomial-time.
**Proof sketch.** A counted loop appending a token for each set bit
(`polyTimeComputable_loopState'`; state `i` is `1^{countTrue (s z) i}`, of length `≤ i ≤ N`). -/
theorem countTrue_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun z => List.replicate (N z) true) :
    PolyTimeComputable fun z => List.replicate (countTrue (s z) (N z)) true := by
  let upd : List Bool → List Bool := fun w =>
    if (s (pairFstD w)).getD (pairFstD (pairSndD w)).length false then
      true :: pairSndD (pairSndD w) else pairSndD (pairSndD w)
  have hupd : PolyTimeComputable upd :=
    polyTimeComputable_ite
      (getBit_poly (hs.comp polyTimeComputable_pairFstD)
        (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
      ((cons_poly true).comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hclosed : ∀ z i, loopState upd (fun _ => []) z i =
      List.replicate (countTrue (s z) i) true := by
    intro z i
    induction i with
    | zero => rw [loopState_zero]; rfl
    | succ i ih =>
      rw [loopState_succ, ih]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
        countTrue_succ]
      cases (s z).getD i false <;> simp [List.replicate_succ]
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have h := polyTimeComputable_loopState' hupd (polyTimeComputable_const []) hN
    (PolyExpr.normal C c) fun z i hi => by
      rw [hclosed, List.length_replicate]
      exact (countTrue_le _ _).trans (hi.trans (by simpa [PolyExpr.eval_normal] using hC z))
  convert h using 1
  funext z
  rw [hclosed]

/-! ### The `e`-th set bit -/

/-- The position of the `e`-th set bit (0-based) among the first `N` positions of `x`: the
least `j < N` whose bit is set and preceded by exactly `e` set bits, `N` if there is none. -/
noncomputable def nthTrue (x : List Bool) (N e : ℕ) : ℕ :=
  firstIdx (fun j => x.getD j false && decide (countTrue x j = e)) N

/-- The `e`-th set position in unary is polynomial-time (`polyTimeComputable_firstIdx` with
the test `bit j ∧ countTrue j = e` on `⟨1^j, z⟩`). -/
theorem nthTrue_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun z => List.replicate (N z) true)
    {e : List Bool → ℕ} (he : PolyTimeComputable fun z => List.replicate (e z) true) :
    PolyTimeComputable fun z => List.replicate (nthTrue (s z) (N z) (e z)) true :=
  polyTimeComputable_firstIdx
    (p := fun z j => (s z).getD j false && decide (countTrue (s z) j = e z))
    (polyTimeComputable_and
      (getBit_poly (hs.comp polyTimeComputable_pairSndD) (unaryLength_poly polyTimeComputable_pairFstD))
      (eqTest_poly
        (countTrue_poly (hs.comp polyTimeComputable_pairSndD)
          (unaryLength_poly polyTimeComputable_pairFstD))
        (he.comp polyTimeComputable_pairSndD)))
    hN

/-- Filtering `List.range (N + 1)` by the bits of `x` appends position `N` iff its bit is set. -/
theorem filter_range_succ (x : List Bool) (N : ℕ) :
    (List.range (N + 1)).filter (fun j => x.getD j false) =
      (List.range N).filter (fun j => x.getD j false) ++ (if x.getD N false then [N] else []) := by
  rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]

/-- The filtered range has `countTrue x N` elements. -/
theorem length_filter_range (x : List Bool) (N : ℕ) :
    ((List.range N).filter (fun j => x.getD j false)).length = countTrue x N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [filter_range_succ, List.length_append, ih, countTrue_succ]
    cases x.getD N false <;> simp

/-- The `e`-th element of the filtered range is the set position `j` preceded by exactly `e`
set bits. -/
theorem getElem?_filter_range (x : List Bool) {N e j : ℕ} (hj : j < N)
    (hbit : x.getD j false = true) (hcnt : countTrue x j = e) :
    ((List.range N).filter (fun j => x.getD j false))[e]? = some j := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [filter_range_succ]
    rcases Nat.lt_or_ge j N with h | h
    · have hlt : e < countTrue x N := by
        have h1 := countTrue_mono x (Nat.succ_le_of_lt h)
        rw [countTrue_succ, hbit, hcnt] at h1
        simpa using h1
      rw [List.getElem?_append_left (by rw [length_filter_range]; exact hlt)]
      exact ih h
    · have hjN : j = N := by omega
      subst hjN
      rw [List.getElem?_append_right (by rw [length_filter_range, hcnt]),
        length_filter_range, hcnt, Nat.sub_self, if_pos hbit]
      rfl

/-- Every rank `e < countTrue x N` is realised by a set position below `N`. -/
theorem exists_nth_set (x : List Bool) :
    ∀ N e, e < countTrue x N → ∃ j < N, x.getD j false = true ∧ countTrue x j = e := by
  intro N
  induction N with
  | zero => intro e h; simp at h
  | succ N ih =>
    intro e he
    rcases Nat.lt_or_ge e (countTrue x N) with h | h
    · obtain ⟨j, hj, hb, hc⟩ := ih e h
      exact ⟨j, by omega, hb, hc⟩
    · rw [countTrue_succ] at he
      have hb : x.getD N false = true := by
        cases hx : x.getD N false
        · rw [hx] at he; simp at he; omega
        · rfl
      refine ⟨N, Nat.lt_succ_self N, hb, ?_⟩
      rw [hb] at he
      simp at he
      omega

/-- For `e < countTrue x N`, `nthTrue x N e` is below `N`, its bit is set, and exactly `e` set
bits precede it. -/
theorem nthTrue_spec (x : List Bool) {N e : ℕ} (he : e < countTrue x N) :
    nthTrue x N e < N ∧ x.getD (nthTrue x N e) false = true ∧ countTrue x (nthTrue x N e) = e := by
  obtain ⟨j, hj, hb, hc⟩ := exists_nth_set x N e he
  have hlt : nthTrue x N e < N := by
    refine firstIdx_lt_iff.2 ⟨j, hj, ?_⟩
    rw [hb, hc]
    simp
  have hq := q_firstIdx (q := fun j => x.getD j false && decide (countTrue x j = e)) hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨hlt, hq.1, hq.2⟩

/-- The `e`-th element of the filtered range is `nthTrue x N e`. -/
theorem getElem?_filter_range_nthTrue (x : List Bool) {N e : ℕ} (he : e < countTrue x N) :
    ((List.range N).filter (fun j => x.getD j false))[e]? = some (nthTrue x N e) :=
  let h := nthTrue_spec x he
  getElem?_filter_range x h.1 h.2.1 h.2.2

/-! ### The numeric model of the edge list -/

/-- The row-major indices of the lexicographically ordered pairs `Fin m × Fin n` enumerate
`range (m n)`. -/
theorem flatMap_range_mul (n : ℕ) :
    ∀ m, (List.range m).flatMap (fun u => (List.range n).map (fun v => v + n * u)) =
      List.range (m * n)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_mul n m, List.flatMap_singleton,
      Nat.succ_mul, List.range_add]
    congr 1
    apply List.map_congr_left
    intro v _
    ring

/-- The indices `v + n u` of the lexicographically ordered pairs of `finRange n ×ˢ finRange n`
enumerate `range (n²)` (`finProdFinEquiv`). -/
theorem map_product_finRange (n : ℕ) :
    (List.finRange n ×ˢ List.finRange n).map
        (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)) =
      List.range (n * n) := by
  rw [← flatMap_range_mul n n]
  show ((List.finRange n).flatMap fun u => (List.finRange n).map (Prod.mk u)).map _ = _
  rw [List.map_flatMap]
  conv_rhs => rw [← List.map_coe_finRange n, List.flatMap_map]
  congr 1
  funext u
  rw [List.map_map, List.map_map]
  congr 1

/-- **The numeric model of the edge list:** through the index `(u, v) ↦ v + n u` of
`finProdFinEquiv`, the lexicographically ordered edge list of a graph whose adjacency bit
`(u, v)` is bit `v + n u` of the word `x` is the increasing list of set positions `j < n²` of
`x` (`List.filter_map` and `map_product_finRange`). -/
theorem map_edgeList {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) :
    (edgeList G).map (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)) =
      (List.range (n * n)).filter (fun j => x.getD j false) := by
  rw [← map_product_finRange, List.filter_map]
  simp only [edgeList_def]
  congr 1
  apply List.filter_congr
  rintro ⟨u, v⟩ _
  exact hG u v

/-- The number of edges is the number of set bits among the `n²` matrix positions. -/
theorem edgeCount_eq {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) :
    edgeCount G = countTrue x (n * n) := by
  have := congrArg List.length (map_edgeList G x hG)
  rwa [List.length_map, length_filter_range] at this

/-- The endpoints of the edge of index `e` are the quotient and remainder by `n` of the
`e`-th set position `nthTrue x (n²) e` of the adjacency word. -/
theorem edgeOf_val {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) (e : Fin (edgeCount G)) :
    ((edgeOf G e).1 : ℕ) = nthTrue x (n * n) e / n ∧
      ((edgeOf G e).2 : ℕ) = nthTrue x (n * n) e % n := by
  have he : (e : ℕ) < countTrue x (n * n) := by
    rw [← edgeCount_eq G x hG]
    exact e.isLt
  have h1 : ((edgeList G).map
      (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)))[(e : ℕ)]? =
      some ((finProdFinEquiv (edgeOf G e) : Fin (n * n)) : ℕ) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem e.isLt, Option.map_some, edgeOf_eq]
    rfl
  rw [map_edgeList G x hG, getElem?_filter_range_nthTrue x he, Option.some.injEq,
    finProdFinEquiv_apply_val] at h1
  have hn : 0 < n := (edgeOf G e).1.pos
  have hv := (edgeOf G e).2.isLt
  constructor
  · rw [h1, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hv, zero_add]
  · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- The adjacency matrix of a graph decoded from `x` is the matrix read from `x` (the
hypothesis of `map_edgeList` for `decGraph`). -/
theorem decGraph_apply (x : List Bool) (u v : Fin (decGraph x).1) :
    (decGraph x).2 u v = x.getD (finProdFinEquiv (u, v)) false :=
  decGraph_snd_apply x u v

/-- Re-encoding the graph decoded from `x` truncates `x` to its first `n²` bits, `n = √|x|`. -/
theorem encGraph_decGraph_eq_take (x : List Bool) :
    encGraph (decGraph x).2 = x.take ((decGraph x).1 * (decGraph x).1) := by
  apply List.ext_getElem
  · rw [length_encGraph, List.length_take,
      min_eq_left (show (decGraph x).1 * (decGraph x).1 ≤ x.length by
        rw [decGraph_fst]; exact Nat.sqrt_le _)]
  · intro i h1 h2
    have hi : i < x.length := by
      rw [List.length_take] at h2
      omega
    rw [List.getElem_take]
    simp only [encGraph_def, List.getElem_ofFn]
    rw [decGraph_apply, Equiv.apply_symm_apply, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]

/-! ### The numeric model of the samplers -/

/-- The number read (most significant bit first) from the `k` bits of `s` at positions
`b, …, b + k - 1` (default `false`): the loop value of `bitsToNat` on a tape window. -/
def natOfBits (s : List Bool) (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 2 * natOfBits s b j + (s.getD (b + j) false).toNat

/-- The empty window reads as `0`. -/
@[simp] theorem natOfBits_zero (s : List Bool) (b : ℕ) : natOfBits s b 0 = 0 := rfl

/-- Reading one more bit doubles the value and adds the bit. -/
@[simp] theorem natOfBits_succ (s : List Bool) (b j : ℕ) :
    natOfBits s b (j + 1) = 2 * natOfBits s b j + (s.getD (b + j) false).toNat := rfl

/-- A `k`-bit window reads as a number below `2^k`. -/
theorem natOfBits_lt (s : List Bool) (b : ℕ) : ∀ k, natOfBits s b k < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [natOfBits_succ, pow_succ]
    have := natOfBits_lt s b k
    have := Bool.toNat_le (s.getD (b + k) false)
    omega

/-- `bitsToNat` of a tape window is `natOfBits` (`List.ofFn_succ_last`, `List.foldl_append`). -/
theorem bitsToNat_eq_natOfBits (s : List Bool) (b : ℕ) :
    ∀ k, bitsToNat (fun j : Fin k => s.getD (b + j) false) = natOfBits s b k
  | 0 => by rw [bitsToNat_def]; rfl
  | k + 1 => by
    have ih := bitsToNat_eq_natOfBits s b k
    simp only [bitsToNat_def] at ih ⊢
    rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.coe_castSucc]
    rw [ih, natOfBits_succ]
    show (2 * natOfBits s b k + if s.getD (b + k) false = true then 1 else 0) =
      2 * natOfBits s b k + (s.getD (b + k) false).toNat
    cases s.getD (b + k) false <;> rfl

/-- **Reading a window as a number is polynomial-time** when `2^k` is polynomially bounded.
**Proof sketch.** A counted loop doubling the accumulator and adding the next bit
(`polyTimeComputable_loopState'`, states `1^{natOfBits} < 1^{2^k}`, `natOfBits_lt`). -/
theorem natOfBits_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {b : List Bool → ℕ} (hb : PolyTimeComputable fun z => List.replicate (b z) true)
    {k : List Bool → ℕ} (hk : PolyTimeComputable fun z => List.replicate (k z) true)
    (Bd : PolyExpr) (hBd : ∀ z, 2 ^ k z ≤ Bd.eval z.length) :
    PolyTimeComputable fun z => List.replicate (natOfBits (s z) (b z) (k z)) true := by
  let upd : List Bool → List Bool := fun w =>
    List.replicate (2 * (pairSndD (pairSndD w)).length +
      ((s (pairFstD w)).getD (b (pairFstD w) + (pairFstD (pairSndD w)).length) false).toNat) true
  have hupd : PolyTimeComputable upd :=
    unaryAdd_poly
      (unaryMul_poly (unaryConst_poly 2)
        (unaryLength_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
      (unaryOfTest_poly (getBit_poly (hs.comp polyTimeComputable_pairFstD)
        (unaryAdd_poly (hb.comp polyTimeComputable_pairFstD)
          (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))))
  have hclosed : ∀ z i, loopState upd (fun _ => []) z i =
      List.replicate (natOfBits (s z) (b z) i) true := by
    intro z i
    induction i with
    | zero =>
      rw [loopState_zero]
      rfl
    | succ i ih =>
      rw [loopState_succ, ih]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
        natOfBits_succ]
  have h := polyTimeComputable_loopState' hupd (polyTimeComputable_const []) hk Bd
    fun z i hi => by
      rw [hclosed, List.length_replicate]
      exact ((natOfBits_lt _ _ _).le.trans (Nat.pow_le_pow_right (by norm_num) hi)).trans (hBd z)
  convert h using 1
  funext z
  rw [hclosed]

/-- `List.findSome?` over `finRange T` of a test-and-value function returns the value at the
first accepted index (`firstIdx`), `none` if no index below `T` is accepted. **Proof sketch.**
Split `finRange T` at `firstIdx` (`q_firstIdx`, `firstIdx_min`), or none is accepted. -/
theorem findSome?_finRange_eq {α : Type*} {T : ℕ} (f : Fin T → Option α) (q : ℕ → Bool)
    (v : ℕ → α) (hf : ∀ t : Fin T, f t = if q t then some (v t) else none) :
    (List.finRange T).findSome? f =
      if firstIdx q T < T then some (v (firstIdx q T)) else none := by
  by_cases h : firstIdx q T < T
  · rw [if_pos h, List.findSome?_eq_some_iff]
    refine ⟨(List.finRange T).take (firstIdx q T), ⟨firstIdx q T, h⟩,
      (List.finRange T).drop (firstIdx q T + 1), ?_, ?_, ?_⟩
    · conv_lhs => rw [← List.take_append_drop (firstIdx q T) (List.finRange T)]
      congr 1
      rw [List.drop_eq_getElem_cons (by simpa using h)]
      simp
    · rw [hf, if_pos (q_firstIdx h)]
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 ha
      rw [hf]
      have hlt : ((List.finRange T)[i] : ℕ) < firstIdx q T := by
        simp only [List.getElem_finRange, Fin.cast_mk]
        exact lt_of_lt_of_le hi (min_le_left _ _)
      rw [if_neg (by simpa using firstIdx_min hlt)]
  · rw [if_neg h, List.findSome?_eq_none_iff]
    intro t _
    rw [hf]
    have hT : firstIdx q T = T := le_antisymm firstIdx_le (not_lt.1 h)
    rw [if_neg (by simpa using firstIdx_eq_iff.1 hT t t.isLt)]

/-- The index of the first accepted trial of `T` rejection trials of `k` bits on the tape `s`
(a value below `m` is accepted), `T` if none is accepted. -/
noncomputable def firstTrial (s : List Bool) (m k T : ℕ) : ℕ :=
  firstIdx (fun t => decide (natOfBits s (t * k) k < m)) T

/-- The value of the rejection sampler as a number, with default `d` on failure. -/
noncomputable def sampleVal (s : List Bool) (m k T d : ℕ) : ℕ :=
  if firstTrial s m k T < T then natOfBits s (firstTrial s m k T * k) k else d

/-- The rejection sampler of `Language.lean`, numerically: the value read at the first accepted
trial. -/
theorem map_val_sampleIdx (m k T : ℕ) (s : List Bool) :
    (sampleIdx m k T s).map Fin.val =
      if firstTrial s m k T < T then some (natOfBits s (firstTrial s m k T * k) k) else none := by
  simp only [sampleIdx_def, rejectionSample_def]
  rw [List.map_findSome?]
  apply findSome?_finRange_eq (q := fun t => decide (natOfBits s (t * k) k < m))
    (v := fun t => natOfBits s (t * k) k)
  intro t
  simp only [Function.comp_apply, uniformFromBits_def, bitsToNat_eq_natOfBits]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by simpa using h2)
  · exact absurd (by simpa using h2) h1
  · rfl

/-- The total rejection sampler with default `d` is `sampleVal`. -/
theorem map_val_sampleIdx_getD (m k T : ℕ) (s : List Bool) (d : ℕ) :
    ((sampleIdx m k T s).map Fin.val).getD d = sampleVal s m k T d := by
  rw [map_val_sampleIdx]
  unfold sampleVal
  split_ifs <;> rfl

/-- **The rejection sampler is polynomial-time** (in unary, when `2^k` is polynomially
bounded). **Proof sketch.** The first accepted trial by `polyTimeComputable_firstIdx` with the
window test `natOfBits_poly`, then the value at that trial (`polyTimeComputable_ite`). -/
theorem sampleVal_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {m : List Bool → ℕ} (hm : PolyTimeComputable fun z => List.replicate (m z) true)
    {k : List Bool → ℕ} (hk : PolyTimeComputable fun z => List.replicate (k z) true)
    {T : List Bool → ℕ} (hT : PolyTimeComputable fun z => List.replicate (T z) true)
    {d : List Bool → ℕ} (hd : PolyTimeComputable fun z => List.replicate (d z) true)
    (Bd : PolyExpr) (hBd : ∀ z, 2 ^ k z ≤ Bd.eval z.length) :
    PolyTimeComputable fun z => List.replicate (sampleVal (s z) (m z) (k z) (T z) (d z)) true := by
  have hBd' : ∀ w : List Bool, 2 ^ k (pairSndD w) ≤ Bd.eval w.length := fun w =>
    (hBd _).trans (Bd.eval_mono
      ((Nat.le_add_left _ _).trans (length_pair_components_le w)))
  have hwin : PolyTimeComputable fun w =>
      List.replicate (natOfBits (s (pairSndD w)) ((pairFstD w).length * k (pairSndD w))
        (k (pairSndD w))) true :=
    natOfBits_poly (hs.comp polyTimeComputable_pairSndD)
      (unaryMul_poly (unaryLength_poly polyTimeComputable_pairFstD)
        (hk.comp polyTimeComputable_pairSndD))
      (hk.comp polyTimeComputable_pairSndD) Bd hBd'
  have hfirst : PolyTimeComputable fun z =>
      List.replicate (firstTrial (s z) (m z) (k z) (T z)) true :=
    polyTimeComputable_firstIdx (p := fun z t => decide (natOfBits (s z) (t * k z) (k z) < m z))
      (ltTest_poly hwin (hm.comp polyTimeComputable_pairSndD)) hT
  have hval : PolyTimeComputable fun z =>
      List.replicate (natOfBits (s z) (firstTrial (s z) (m z) (k z) (T z) * k z) (k z)) true :=
    natOfBits_poly hs (unaryMul_poly hfirst hk) hk Bd hBd
  convert polyTimeComputable_ite (ltTest_poly hfirst hT) hval hd using 1
  funext z
  simp only [decide_eq_true_eq]
  unfold sampleVal
  split_ifs <;> rfl

/-! ### The colour permutation as a table -/

/-- The six-bit table of a colour permutation: the encodings of the images of the three
colours. -/
def permTable (σ : Equiv.Perm (Fin 3)) : List Bool :=
  encColor (σ 0) ++ encColor (σ 1) ++ encColor (σ 2)

/-- The table of the permutation of index `i < 6` under `perm3Equiv`, the identity's table for
`i ≥ 6` (the sampler's failure value). -/
noncomputable def tableOfIdx (i : ℕ) : List Bool :=
  if i = 0 then permTable (perm3Equiv 0) else if i = 1 then permTable (perm3Equiv 1) else
  if i = 2 then permTable (perm3Equiv 2) else if i = 3 then permTable (perm3Equiv 3) else
  if i = 4 then permTable (perm3Equiv 4) else if i = 5 then permTable (perm3Equiv 5) else
  permTable 1

/-- On the indices below `6` the table lookup is the table of `perm3Equiv`. -/
theorem tableOfIdx_perm3Equiv (i : Fin 6) : tableOfIdx i = permTable (perm3Equiv i) := by
  fin_cases i <;> simp [tableOfIdx]

/-- The honest prover's permutation table is the table lookup on the sampled index (default
`6`, the identity). -/
theorem permTable_samplePerm3 (T : ℕ) (s : List Bool) :
    permTable (samplePerm3 T s) = tableOfIdx (sampleVal s 6 3 T 6) := by
  rw [← map_val_sampleIdx_getD]
  simp only [samplePerm3_def]
  cases sampleIdx 6 3 T s with
  | none => simp [tableOfIdx]
  | some i =>
    simp only [Option.map_some, Option.getD_some]
    exact (tableOfIdx_perm3Equiv i).symm

/-- The table lookup is polynomial-time (seven constant tables selected by equality tests on
the unary index). -/
theorem tableOfIdx_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun z => List.replicate (f z) true) :
    PolyTimeComputable fun z => tableOfIdx (f z) := by
  have t : ∀ c : ℕ, PolyTimeComputable fun z => [decide (f z = c)] := fun c =>
    eqTest_poly hf (unaryConst_poly c)
  convert polyTimeComputable_ite (t 0) (polyTimeComputable_const (permTable (perm3Equiv 0)))
    (polyTimeComputable_ite (t 1) (polyTimeComputable_const (permTable (perm3Equiv 1)))
      (polyTimeComputable_ite (t 2) (polyTimeComputable_const (permTable (perm3Equiv 2)))
        (polyTimeComputable_ite (t 3) (polyTimeComputable_const (permTable (perm3Equiv 3)))
          (polyTimeComputable_ite (t 4) (polyTimeComputable_const (permTable (perm3Equiv 4)))
            (polyTimeComputable_ite (t 5) (polyTimeComputable_const (permTable (perm3Equiv 5)))
              (polyTimeComputable_const (permTable 1))))))) using 1
  funext z
  simp [tableOfIdx]

/-- The two bits of a table at colour `a`: bits `2a` and `2a + 1`. -/
def colorFromTable (tbl : List Bool) (a : ℕ) : List Bool :=
  [tbl.getD (2 * a) false, tbl.getD (2 * a + 1) false]

/-- The encoding of a colour, numerically: `[a / 2 = 1, a % 2 = 1]`. -/
theorem encColor_eq (a : Fin 3) : encColor a = [decide (a.val / 2 = 1), decide (a.val % 2 = 1)] := by
  rw [encColor_def, encColoring_eq]
  fin_cases a <;> rfl

/-- Looking up colour `a` in the table of `σ` gives the encoding of `σ a`. -/
theorem colorFromTable_permTable (σ : Equiv.Perm (Fin 3)) (a : Fin 3) :
    colorFromTable (permTable σ) a = encColor (σ a) := by
  fin_cases a <;> simp [colorFromTable, permTable, encColor_eq]

/-- The table lookup of a colour is polynomial-time (two bit extractions). -/
theorem colorFromTable_poly {tbl : List Bool → List Bool} (htbl : PolyTimeComputable tbl)
    {a : List Bool → ℕ} (ha : PolyTimeComputable fun z => List.replicate (a z) true) :
    PolyTimeComputable fun z => colorFromTable (tbl z) (a z) :=
  ptc_congr ((getBit_poly htbl (unaryMul_poly (unaryConst_poly 2) ha)).append
    (getBit_poly htbl (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) ha) (unaryConst_poly 1))))
    fun _ => rfl

/-! ### Colours as numbers -/

/-- The colour of vertex `u` read from an encoded colouring: `(2 b₀ + b₁) mod 3` from bits
`2u`, `2u + 1`. -/
def colorVal (y : List Bool) (u : ℕ) : ℕ :=
  (2 * (y.getD (2 * u) false).toNat + (y.getD (2 * u + 1) false).toNat) % 3

/-- `decColoring` numerically. -/
theorem decColoring_val (n : ℕ) (y : List Bool) (u : Fin n) :
    ((decColoring n y u : Fin 3) : ℕ) = colorVal y u := by
  have h0 : ((finProdFinEquiv (u, (0 : Fin 2)) : Fin (n * 2)) : ℕ) = 2 * u := by
    rw [finProdFinEquiv_apply_val]
    simp
  have h1 : ((finProdFinEquiv (u, (1 : Fin 2)) : Fin (n * 2)) : ℕ) = 2 * u + 1 := by
    rw [finProdFinEquiv_apply_val]
    simp
    omega
  rw [decColoring_val_eq, h0, h1]
  rfl

/-- `decColor` numerically. -/
theorem decColor_val (w : List Bool) : ((decColor w : Fin 3) : ℕ) = colorVal w 0 := by
  rw [decColor_def, decColoring_val]
  rfl

/-- The colour value of a vertex is polynomial-time in unary. -/
theorem colorVal_poly {y : List Bool → List Bool} (hy : PolyTimeComputable y)
    {u : List Bool → ℕ} (hu : PolyTimeComputable fun z => List.replicate (u z) true) :
    PolyTimeComputable fun z => List.replicate (colorVal (y z) (u z)) true := by
  have h2u := unaryMul_poly (unaryConst_poly 2) hu
  have h := modNum_poly
    (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) (unaryOfTest_poly (getBit_poly hy h2u)))
      (unaryOfTest_poly (getBit_poly hy (unaryAdd_poly h2u (unaryConst_poly 1)))))
    (unaryConst_poly 3)
  convert h using 1
  funext z
  rw [modNum_eq]
  rfl

/-- The encoding of a colour from its value: `[a / 2 = 1, a % 2 = 1]`. -/
def encColorOfVal (a : ℕ) : List Bool := [decide (a / 2 = 1), decide (a % 2 = 1)]

/-- `encColor` is `encColorOfVal` of the colour's value. -/
theorem encColor_eq_ofVal (a : Fin 3) : encColor a = encColorOfVal a := encColor_eq a

/-- The colour encoding from a unary value is polynomial-time. -/
theorem encColorOfVal_poly {a : List Bool → ℕ}
    (ha : PolyTimeComputable fun z => List.replicate (a z) true) :
    PolyTimeComputable fun z => encColorOfVal (a z) := by
  have h1 := eqTest_poly (divNum_poly ha (unaryConst_poly 2)) (unaryConst_poly 1)
  have h2 := eqTest_poly (modNum_poly ha (unaryConst_poly 2)) (unaryConst_poly 1)
  convert h1.append h2 using 1
  funext z
  simp [encColorOfVal, divNum_eq, modNum_eq]

/-! ### Message encodings -/

/-- A pair is the pair with empty second component followed by the second component. -/
theorem pairEncode_eq_append_nil (a b : List Bool) : pairEncode a b = pairEncode a [] ++ b := by
  simp [pairEncode_eq]

/-- An encoded message list is the concatenation of the self-delimiting messages
`pairEncode m []`. -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap (fun m => pairEncode m []) := by
  induction l with
  | nil => rw [Strategy.encodeMsgs_nil]; rfl
  | cons m h ih => rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ih, pairEncode_eq_append_nil]

/-- `List.ofFn f` is the image of `range n` under any `ℕ`-indexed extension of `f`. -/
theorem ofFn_eq_map_range {α : Type*} {n : ℕ} (f : Fin n → α) (F : ℕ → α)
    (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) : List.ofFn f = (List.range n).map F := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact h i (by simpa using h1)

/-- The `i`-th second projection of an encoded history drops its first `i` messages. -/
theorem iterate_pairSndD_encodeMsgs (hist : List (List Bool)) :
    ∀ i, pairSndD^[i] (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop i) := by
  intro i
  induction i generalizing hist with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases hist with
    | nil =>
      rw [Strategy.encodeMsgs_nil, pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil, List.drop_nil,
        Strategy.encodeMsgs_nil]
      exact Function.iterate_fixed (pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil) i
    | cons m h => rw [Strategy.encodeMsgs_cons, pairSndD_pairEncode, ih, List.drop_succ_cons]

/-- An encoded history is empty iff the history is. -/
theorem encodeMsgs_eq_nil_iff (hist : List (List Bool)) :
    Strategy.encodeMsgs hist = [] ↔ hist = [] := by
  cases hist with
  | nil => simp
  | cons m h => simp [pairEncode_eq]

/-- A history is no longer than its encoding. -/
theorem length_le_length_encodeMsgs (hist : List (List Bool)) :
    hist.length ≤ (Strategy.encodeMsgs hist).length := by
  induction hist with
  | nil => exact Nat.zero_le _
  | cons m h ih =>
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons]
    omega

/-- The `i`-th message of a history (default `[]`) is the first projection after `i` second
projections of its encoding (`Strategy.pairFstD_encodeMsgs`). -/
theorem getD_eq_pairFstD_iterate (hist : List (List Bool)) (i : ℕ) :
    hist.getD i [] = pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) := by
  rw [iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD]

/-- The last message of a history (default `[]`) is its message of index `length - 1`. -/
theorem getLastD_eq_getD (hist : List (List Bool)) : hist.getLastD [] = hist.getD (hist.length - 1) [] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The number of messages of an encoded history: the number of second projections needed to
reach the empty word, searched below `|M| + 1`. -/
noncomputable def histLen (M : List Bool) : ℕ :=
  firstIdx (fun i => decide (pairSndD^[i] M = [])) (M.length + 1)

/-- `histLen` recovers the length of the history. -/
theorem histLen_encodeMsgs (hist : List (List Bool)) :
    histLen (Strategy.encodeMsgs hist) = hist.length := by
  unfold histLen
  apply firstIdx_eq_of
  · exact Nat.lt_succ_of_le (length_le_length_encodeMsgs hist)
  · rw [iterate_pairSndD_encodeMsgs, List.drop_length]
    simp
  · intro i hi
    rw [iterate_pairSndD_encodeMsgs, decide_eq_false_iff_not, encodeMsgs_eq_nil_iff,
      ← List.length_eq_zero_iff, List.length_drop]
    omega

/-- The message count of an encoded history is polynomial-time in unary. -/
theorem histLen_poly : PolyTimeComputable fun M => List.replicate (histLen M) true :=
  polyTimeComputable_firstIdx (p := fun M i => decide (pairSndD^[i] M = []))
    (polyTimeComputable_isNil.comp (iterSnd_poly polyTimeComputable_pairSndD
      (unaryLength_poly polyTimeComputable_pairFstD)))
    (unaryAdd_poly (unaryLength_poly polyTimeComputable_id) (unaryConst_poly 1))

/-- An encoded `ofFn` list is the concatenation of the self-delimiting messages
`pairEncode (F i) []` over `i < n`, for any `ℕ`-indexed extension `F` of `f`. -/
theorem encodeMsgs_ofFn_eq_flatMap {n : ℕ} (f : Fin n → List Bool) (F : ℕ → List Bool)
    (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) :
    Strategy.encodeMsgs (List.ofFn f) = (List.range n).flatMap (fun i => pairEncode (F i) []) := by
  rw [ofFn_eq_map_range f F h, encodeMsgs_eq_flatMap, List.flatMap_map]

/-- With at least one edge, `edgeAt G e` is the edge of index `e mod |E|`. -/
theorem edgeAt_eq_some_of_pos {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (e : ℕ) :
    edgeAt G e = some (edgeOf G ⟨e % edgeCount G, Nat.mod_lt _ hm⟩) := by
  simp only [edgeAt_def]
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hm), edgeOf_eq, List.get_eq_getElem]

end TCSlib.Cryptography.ColMachines
