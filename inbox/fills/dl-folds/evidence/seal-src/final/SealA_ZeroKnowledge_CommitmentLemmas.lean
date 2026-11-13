/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the commitment theorems

The machine constructions and probability bookkeeping behind the theorems of
`TCSlib.Cryptography.ZeroKnowledge.Commitment` [PS10, §4.7.1]: multi-value hiding of a
commitment scheme (Claim-126.a), the hiding of the bitwise scheme of Theorem 126.4
(Claim-127.d) and the polynomial-time evaluator of its `Com` (Alg-127.a). Nothing here mentions
the commitment definitions themselves; the file supplies

* **averaging over a coin factor** (`exists_fixCoins`): for a distinguisher whose coins split as
  `κ × ρ`, some fixed value `c₀` of the first factor has at least the advantage of the
  distinguisher. This is the non-uniform way to run the coordinatewise hybrid reduction
  `pairRed` of Claim-126.a without any sampler: the randomness of the other coordinates is
  hard-wired as advice, so neither hiding theorem needs an efficient evaluator of the scheme
  (the text's "simple hybrid argument" tacitly uses the non-uniformity of [PS10, Definition 126.3]);
* **coin transport** (`acceptProb_distinguisher_of_runAtL`, `acceptProb_distinguisherL_of_runAtL`):
  a machine with `D`'s coins whose activation is `D` on a pre-processed input has the acceptance
  probabilities of the pre-processed distinguisher;
* **splitting a tuple at a position** (`ofFn_update_eq`, `ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update`): the block string, respectively the message encoding
  `Strategy.encodeMsgs`, of a tuple with one position replaced by a challenge `z` is a fixed
  prefix, then `z` (respectively the pair `⟨z, ·⟩`), then a fixed suffix;
* **the splice machines** (`exists_spliceRed`, `exists_pairSpliceRed`): the `NUPPT`s that
  plant their argument between two hard-wired strings and call `D` once
  (`Complexity.NUPPT.exists_comp`, `Complexity.NUPPT.exists_withAdvice`);
* **the bitwise commitment loop** (`ComLoop`): the state loop evaluating
  `Com(v, (r_i)_i) = (F ⟨1^n, r_i⟩ ‖ (v_i ⊕ H ⟨1^n, r_i⟩))_i` from evaluators `F`, `H` of `f`, `h`
  (`Complexity.polyTimeComputable_iterateEmit`), with the closed form of its emissions.

## Main definitions

* `TCSlib.Cryptography.CommitmentLemmas.spliceFun`, `pairSpliceFun` — the splice pre-processings.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.step`, `ComLoop.emit`, `ComLoop.loopOut`,
  `ComLoop.init` — the bitwise commitment loop.

## Main results

* `TCSlib.Cryptography.CommitmentLemmas.exists_fixCoins` — averaging over a coin factor.
* `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisher_of_runAtL`,
  `acceptProb_distinguisherL_of_runAtL` — coin transport.
* `TCSlib.Cryptography.CommitmentLemmas.ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update` — splitting a tuple at a position.
* `TCSlib.Cryptography.CommitmentLemmas.exists_spliceRed`, `exists_pairSpliceRed` — the
  splice machines.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.loopOut_poly`, `ComLoop.emit_init_of_lt`,
  `ComLoop.emit_init_of_le` — the loop is polynomial-time and its emissions are the one-bit
  commitments.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.1: Definition 126.3, Theorem 126.4; §3.1.1: Lemma 71.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.3 (the multicopy hybrid argument).
-/

namespace TCSlib.Cryptography.CommitmentLemmas

open Complexity Turing Finset

/-! Seal A (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean`, with every seal candidate of its
full TCSlib import closure (895 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquivPoly _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.Protocol.ProverBounded _root_.TCSlib.Cryptography.Protocol.execution _root_.TCSlib.Cryptography.Protocol.outP _root_.TCSlib.Cryptography.Protocol.outV _root_.TCSlib.Cryptography.Protocol.transcript _root_.TCSlib.Cryptography.Protocol.transcriptWith _root_.TCSlib.Cryptography.Protocol.viewP _root_.TCSlib.Cryptography.Protocol.viewV _root_.TCSlib.Cryptography.Protocol.withV _root_.TCSlib.Cryptography.Protocol.withV_vCoinsEquiv _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.Strategy.Efficient _root_.TCSlib.Cryptography.Strategy.ReadsPrefix _root_.TCSlib.Cryptography.Strategy.coinLen _root_.TCSlib.Cryptography.Strategy.encodeMsgs _root_.TCSlib.Cryptography.Strategy.ofNUPPT _root_.TCSlib.Cryptography.Strategy.out _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.View.encode _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.exec _root_.TCSlib.Cryptography.exec.match_1 _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.moverIsV _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ### Averaging over a coin factor -/

/-- Some point of a finite nonempty type carries at least the absolute value of the average:
`|E f| ≤ |f c₀|` for some `c₀` (`Finset.exists_le_of_sum_le` against the constant `|E f|`). -/
theorem exists_abs_uexp_le {κ : Type*} [Fintype κ] [Nonempty κ] (f : κ → ℝ) :
    ∃ c₀, |uexp f| ≤ |f c₀| := by
  have hcard : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hsum : ∑ _c : κ, |uexp f| ≤ ∑ c, |f c| := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uexp_def, abs_div, abs_of_pos hcard,
      mul_div_cancel₀ _ hcard.ne']
    exact Finset.abs_sum_le_sum_abs _ _
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨c₀, hc₀⟩

/-- The acceptance probability of a distinguisher with coins `κ × ρ` is the average over the
first coin factor of the acceptance probabilities with that factor fixed (`uprob_prod` after
regrouping the sample space). -/
theorem acceptProb_eq_uexp_fst {σ γ κ ρ : Type*} [Fintype σ] [Fintype κ] [Fintype ρ]
    (X : σ → γ) (D : γ → κ × ρ → Bool) :
    acceptProb X D = uexp fun c₀ => acceptProb X fun z c => D z (c₀, c) := by
  simp only [acceptProb_def]
  refine ((uprob_comp_equiv (EnsembleLemmas.swapAux κ σ ρ)
    fun z : σ × (κ × ρ) => D (X z.1) z.2 = true).symm.trans ?_)
  rw [uprob_prod]
  rfl

/-- **Averaging over a coin factor**: for a distinguisher `D` whose coins split as `κ × ρ`,
some fixed value `c₀` of the first factor does at least as well as `D` itself,
`distAdv X Y D ≤ distAdv X Y (D(·, (c₀, ·)))`. This is how a non-uniform reduction hard-wires
the randomness of the other coordinates of a hybrid argument instead of sampling them
([PS10, Definition 26.8], advice).

**Proof sketch.** Both acceptance probabilities are averages over `c₀`
(`acceptProb_eq_uexp_fst`), so the advantage is `|E_{c₀}[a(c₀) − b(c₀)]|`, and some `c₀` has
`|a(c₀) − b(c₀)|` at least the average (`exists_abs_uexp_le`). -/
theorem exists_fixCoins {σ τ γ κ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [Fintype ρ]
    [Nonempty κ] (X : σ → γ) (Y : τ → γ) (D : γ → κ × ρ → Bool) :
    ∃ c₀ : κ, distAdv X Y D ≤ distAdv X Y fun z c => D z (c₀, c) := by
  obtain ⟨c₀, hc₀⟩ := exists_abs_uexp_le fun c₀ : κ =>
    acceptProb X (fun z c => D z (c₀, c)) - acceptProb Y (fun z c => D z (c₀, c))
  refine ⟨c₀, ?_⟩
  simp only [distAdv_def]
  rw [acceptProb_eq_uexp_fst X D, acceptProb_eq_uexp_fst Y D]
  convert hc₀ using 2
  rw [uexp_def, uexp_def, uexp_def, ← sub_div, Finset.sum_sub_distrib]

/-- The distinguishing advantage is symmetric in the two distributions. -/
theorem distAdv_comm {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : distAdv X Y D = distAdv Y X D :=
  abs_sub_comm _ _

/-! ### Coin transport -/

/-- A machine `B` with `D`'s coins whose activation on `y` is `D`'s on `g y` has, as a typed
distinguisher, the acceptance probabilities of the distinguisher `D(1^n, g ·)` (the coin types
correspond along `B.coins = D.coins`). -/
theorem acceptProb_distinguisher_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n m : ℕ} (X : σ → Fin m → Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisher n m) =
      acceptProb X fun z c => D.distinguisherL n (g (List.ofFn z)) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen_eq, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hrun]

/-- As `acceptProb_distinguisher_of_runAtL`, for untyped samples. -/
theorem acceptProb_distinguisherL_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n : ℕ} (X : σ → List Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisherL n) = acceptProb X fun z c => D.distinguisherL n (g z) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen_eq, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hrun]

/-! ### Splitting a tuple at a position -/

/-- Splitting `List.ofFn F` at position `j`: the first `j` entries, the entry `j`, the rest
(`List.ext_getElem` with `List.getElem_append`, `List.getElem_cons`; private copy of
`ofFn_eq_append_cons` of `Encryption/PublicKey/HybridMachine.lean`, which this file does not import). -/
theorem ofFn_eq_append_cons {α : Type*} {N : ℕ} (F : Fin N → α) (j : Fin N) :
    List.ofFn F = (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
      F j :: List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro t h1 h2
    rw [List.getElem_append]
    simp only [List.length_ofFn]
    split_ifs with h
    · simp only [List.getElem_ofFn]
      congr 1
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)

/-- `List.ofFn (update W k z)` is the entries before `k`, then `z`, then the entries after `k`.

**Proof sketch.** `ofFn_eq_append_cons` splits `List.ofFn (update W k z)` at `k`; the entry at
`k` is `z` (`Function.update_self`) and the entries before and after `k` are those of `W`
(`Function.update_of_ne`, the indices `castLE i < k` and `k + 1 + i` differing from `k`). -/
theorem ofFn_update_eq {α : Type*} {N : ℕ} (W : Fin N → α) (k : Fin N) (z : α) :
    List.ofFn (Function.update W k z) = (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
      z :: List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩ := by
  rw [ofFn_eq_append_cons (Function.update W k z) k, Function.update_self]
  have h₁ : ∀ i : Fin k, Function.update W k z (Fin.castLE k.2.le i) = W (Fin.castLE k.2.le i) := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    have hi := i.2
    simp only [Fin.coe_castLE] at hv
    omega
  have h₂ : ∀ i : Fin (N - k - 1),
      Function.update W k z ⟨k + 1 + i, by omega⟩ = W ⟨k + 1 + i, by omega⟩ := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  simp only [h₁, h₂]

/-- The concatenation of `j` strings of `L` bits has `j · L` bits. -/
theorem length_flatten_ofFn {j L : ℕ} (f : Fin j → Fin L → Bool) :
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L := by
  simp [List.length_flatten, List.sum_ofFn]

/-- The block string of a tuple with block `k` replaced by `z`: the blocks before `k`, then
`z`, then the blocks after `k` (`FunFamily.ofFn_blocks_symm`, `ofFn_update_eq`). -/
theorem ofFn_blocks_symm_update {q ℓ : ℕ} (W : Fin q → Fin ℓ → Bool) (k : Fin q)
    (z : Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks q ℓ).symm (Function.update W k z)) =
      (List.ofFn fun i : Fin k => List.ofFn (W (Fin.castLE k.2.le i))).flatten ++ List.ofFn z ++
        (List.ofFn fun i : Fin (q - k - 1) => List.ofFn (W ⟨k + 1 + i, by omega⟩)).flatten := by
  rw [FunFamily.ofFn_blocks_symm]
  have h2 : (fun i => List.ofFn (Function.update W k z i)) =
      Function.update (fun i => List.ofFn (W i)) k (List.ofFn z) := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [h2, ofFn_update_eq, List.flatten_append, List.flatten_cons, List.append_assoc]

/-- The encoding of a concatenated history is the concatenation of the encodings
(`pairEncode a (b ++ c) = pairEncode a b ++ c`). -/
theorem encodeMsgs_append (L M : List (List Bool)) :
    Strategy.encodeMsgs (L ++ M) = Strategy.encodeMsgs L ++ Strategy.encodeMsgs M := by
  induction L with
  | nil => rfl
  | cons m L ih => simp [ih, pairEncode_eq, List.append_assoc]

/-- The encoding of a history of messages of length `≤ M` has length at most
`|L| · (2M + 2)` (`length_pairEncode`). -/
theorem length_encodeMsgs_le (L : List (List Bool)) (M : ℕ) (hM : ∀ m ∈ L, m.length ≤ M) :
    (Strategy.encodeMsgs L).length ≤ L.length * (2 * M + 2) := by
  induction L with
  | nil => simp
  | cons m L ih =>
    have h1 := hM m (by simp)
    have h2 := ih fun m' hm' => hM m' (by simp [hm'])
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The encoding of a tuple with position `k` replaced by `z`: the encoding of the entries
before `k`, then the pair `⟨z, ·⟩` around the encoding of the entries after `k`
(`ofFn_update_eq`, `encodeMsgs_append`). -/
theorem encodeMsgs_ofFn_update {N : ℕ} (W : Fin N → List Bool) (k : Fin N) (z : List Bool) :
    Strategy.encodeMsgs (List.ofFn (Function.update W k z)) =
      Strategy.encodeMsgs (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
        pairEncode z (Strategy.encodeMsgs
          (List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩)) := by
  rw [ofFn_update_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]

/-- Chunks that are empty from index `n` on do not contribute: the concatenation over
`range m` equals the one over `range n` for `n ≤ m`. -/
theorem flatMap_range_eq_of_nil (F : ℕ → List Bool) {n m : ℕ} (hnm : n ≤ m)
    (hF : ∀ i, n ≤ i → F i = []) : (List.range m).flatMap F = (List.range n).flatMap F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have h : (List.range d).flatMap (fun a => F (n + a)) = [] :=
    List.flatMap_eq_nil_iff.2 fun x _ => hF _ (Nat.le_add_right n x)
  rw [h, List.append_nil]

/-! ### The splice machines -/

/-- The splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ z ++ suf`. -/
def spliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairFstD y ++ pairSndD (pairSndD y)

/-- The splice pre-processing is polynomial-time. -/
theorem spliceFun_poly : PolyTimeComputable spliceFun :=
  ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    polyTimeComputable_pairFstD).append
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The splice pre-processing on a well-formed argument. -/
@[simp] theorem spliceFun_pairEncode (z pre suf : List Bool) :
    spliceFun (pairEncode z (pairEncode pre suf)) = pre ++ z ++ suf := by
  simp [spliceFun]

/-- The pair-splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ ⟨z, suf⟩`. -/
def pairSpliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairEncode (pairFstD y) (pairSndD (pairSndD y))

/-- The pair-splice pre-processing is polynomial-time. -/
theorem pairSpliceFun_poly : PolyTimeComputable pairSpliceFun :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The pair-splice pre-processing on a well-formed argument. -/
@[simp] theorem pairSpliceFun_pairEncode (z pre suf : List Bool) :
    pairSpliceFun (pairEncode z (pairEncode pre suf)) = pre ++ pairEncode z suf := by
  simp [pairSpliceFun]

/-- **The splice machine**: for an `NUPPT` `D` and polynomially bounded strings `pre n`, `suf n`
there is an `NUPPT` `B` with `D`'s coins computing `D(1^n, pre n ++ y ++ suf n; r)`
(`Complexity.NUPPT.exists_comp` with `spliceFun`, then `Complexity.NUPPT.exists_withAdvice`
hard-wiring `⟨pre n, suf n⟩`). -/
theorem exists_spliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧ ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ y ++ suf n) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp spliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, spliceFun_pairEncode]
  rfl

/-- **The pair-splice machine**: as `exists_spliceRed`, computing
`D(1^n, pre n ++ ⟨y, suf n⟩; r)` (the argument planted as a message of an encoded history). -/
theorem exists_pairSpliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧
      ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ pairEncode y (suf n)) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp pairSpliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, pairSpliceFun_pairEncode]
  rfl

/-! ### The bitwise commitment loop -/

namespace ComLoop

/-- The unary parameter slot `u` of the state word `⟨u, ⟨vs, rs⟩⟩`. -/
def p₁ (w : List Bool) : List Bool := pairFstD w

/-- The remaining value bits `vs` of the state word. -/
def p₂ (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The remaining randomness `rs` of the state word. -/
def p₃ (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The state word `⟨u, ⟨vs, rs⟩⟩`. -/
def st (u vs rs : List Bool) : List Bool := pairEncode u (pairEncode vs rs)

/-- Reading the parameter slot. -/
@[simp] theorem p₁_st (u vs rs : List Bool) : p₁ (st u vs rs) = u := by simp [p₁, st]

/-- Reading the value bits. -/
@[simp] theorem p₂_st (u vs rs : List Bool) : p₂ (st u vs rs) = vs := by simp [p₂, st]

/-- Reading the randomness. -/
@[simp] theorem p₃_st (u vs rs : List Bool) : p₃ (st u vs rs) = rs := by simp [p₃, st]

/-- The projections are polynomial-time. -/
theorem p₁_poly : PolyTimeComputable p₁ := polyTimeComputable_pairFstD

/-- The projections are polynomial-time. -/
theorem p₂_poly : PolyTimeComputable p₂ :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The projections are polynomial-time. -/
theorem p₃_poly : PolyTimeComputable p₃ :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Assembling a state word from three polynomial-time components is polynomial-time. -/
theorem st_poly {f₁ f₂ f₃ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) :
    PolyTimeComputable fun z => st (f₁ z) (f₂ z) (f₃ z) :=
  h₁.pairEncode (h₂.pairEncode h₃)

/-- The evaluators' argument at a state word: `⟨u, rs.take |u|⟩`, i.e. `⟨1^n, r_i⟩` for the
current randomness block. -/
def arg (w : List Bool) : List Bool := pairEncode (p₁ w) ((p₃ w).take (p₁ w).length)

/-- The argument is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` on
`⟨u, rs⟩`). -/
theorem arg_poly : PolyTimeComputable arg := by
  convert p₁_poly.pairEncode
    ((polyTimeComputable_pairTakePoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [arg]

/-- The step: drop the first value bit and the first `|u|` randomness bits. -/
def step (w : List Bool) : List Bool := st (p₁ w) (p₂ w).tail ((p₃ w).drop (p₁ w).length)

/-- The step is polynomial-time (`Complexity.polyTimeComputable_tail`,
`Complexity.polyTimeComputable_pairDropPoly` on `⟨u, rs⟩`). -/
theorem step_poly : PolyTimeComputable step := by
  convert st_poly p₁_poly ((polyTimeComputable_tail.congr fun _ => List.drop_one).comp p₂_poly)
    ((polyTimeComputable_pairDropPoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [step]

/-- One step grows a word by at most four symbols (the pairing overhead; both components
only shrink). -/
theorem length_step_le (w : List Bool) : (step w).length ≤ w.length + 4 := by
  have h₁ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le w
  have h₂ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le (pairSndD w)
  simp only [step, st, length_pairEncode, List.length_tail, List.length_drop, p₁, p₂, p₃]
  omega

/-- The orbit of any word grows at most linearly in the number of rounds. -/
theorem length_iterate_step_le (w : List Bool) (i : ℕ) :
    (step^[i] w).length ≤ w.length + 4 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := length_step_le (step^[i] w)
    omega

/-- The closed form of the orbit from `⟨u, ⟨vs, rs⟩⟩`: after `i` rounds the state word is
`⟨u, ⟨vs.drop i, rs.drop (i · |u|)⟩⟩`. -/
theorem iterate_step (u vs rs : List Bool) (i : ℕ) :
    step^[i] (st u vs rs) = st u (vs.drop i) (rs.drop (i * u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, p₁_st, p₂_st, p₃_st, List.tail_drop, List.drop_drop]
    congr 2
    ring

variable (F H : List Bool → List Bool)

/-- The emission at a state word: nothing once the value bits are exhausted, else the one-bit
commitment `F ⟨u, r_i⟩ ++ [v_i ⊕ H ⟨u, r_i⟩]` of the current value bit with the current block
(Alg-127.a). -/
def emit (w : List Bool) : List Bool :=
  if p₂ w = [] then [] else F (arg w) ++ [xor ((p₂ w).headD false) ((H (arg w)).headD false)]

/-- The emission is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
`polyTimeComputable_isNil`, `polyTimeComputable_headD`, `BinArith.polyTimeComputable_xor`,
`PolyTimeComputable.append`). -/
theorem emit_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (emit F H) := by
  convert polyTimeComputable_ite (polyTimeComputable_isNil.comp p₂_poly)
      (polyTimeComputable_const []) ((hF.comp arg_poly).append
        (BinArith.polyTimeComputable_xor (polyTimeComputable_headD.comp p₂_poly)
      (polyTimeComputable_headD.comp (hH.comp arg_poly)))) using 1
  funext w
  simp [emit]

/-- The loop output: the emissions along the `|x| + 1` rounds from `x`, concatenated. -/
def loopOut (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => emit F H (step^[i] x)

/-- The loop output is polynomial-time (`Complexity.polyTimeComputable_iterateEmit` with the
orbit bound `|x| + 4 |x| = 5 |x|`). -/
theorem loopOut_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (loopOut F H) := by
  unfold loopOut
  refine polyTimeComputable_iterateEmit step_poly (emit_poly F H hF hH) .var (.mul (.const 5) .var)
    fun x i hi => ?_
  have := length_iterate_step_le x i
  simp only [PolyExpr.eval_var] at hi
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- The initial state from the argument `⟨v, r⟩`: `⟨1^{|v|}, ⟨v, padL (|v|²) r⟩⟩` (the
randomness padded or cut to `|v|²` bits, as `padFin` does). -/
def init (w : List Bool) : List Bool :=
  st (List.replicate (pairFstD w).length true) (pairFstD w)
    (EnsembleLemmas.padL ((pairFstD w).length * (pairFstD w).length) (pairSndD w))

/-- The initial state is polynomial-time (`Complexity.polyTimeComputable_unary`,
`EnsembleLemmas.polyTimeComputable_padL`). -/
theorem init_poly : PolyTimeComputable init := by
  convert st_poly (polyTimeComputable_unary.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairFstD (EnsembleLemmas.polyTimeComputable_padL (.mul .var .var)
      polyTimeComputable_pairFstD polyTimeComputable_pairSndD) using 1

/-- The initial state only depends on the two components of the argument. -/
theorem init_eq (w : List Bool) : init w = init (pairEncode (pairFstD w) (pairSndD w)) := by
  simp [init]

/-- Once the value bits are exhausted (round `i ≥ |v|`), the loop emits nothing. -/
theorem emit_init_of_le {v r : List Bool} {i : ℕ} (hi : v.length ≤ i) :
    emit F H (step^[i] (init (pairEncode v r))) = [] := by
  simp [init, iterate_step, emit, List.drop_eq_nil_of_le hi]

/-- At round `i < |v|` the loop emits the one-bit commitment of the bit `v[i]` with the `i`-th
block of the padded randomness: `F ⟨1^n, r_i⟩ ++ [v[i] ⊕ (H ⟨1^n, r_i⟩)[0]]` with
`r_i = blocks n n (padFin (n²) r) i`, `n = |v|` (`EnsembleLemmas.take_drop_ofFn_blocks`). -/
theorem emit_init_of_lt {v r : List Bool} {i : ℕ} (hi : i < v.length) :
    emit F H (step^[i] (init (pairEncode v r))) =
      F (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks v.length v.length
        (padFin (v.length * v.length) r) ⟨i, hi⟩))) ++
      [xor (v.getD i false) ((H (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks
        v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩)))).headD false)] := by
  have hne : v.drop i ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff]
    omega
  have hblock : ((EnsembleLemmas.padL (v.length * v.length) r).drop (i * v.length)).take v.length =
      List.ofFn (EnsembleLemmas.blocks v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩) :=
    EnsembleLemmas.take_drop_ofFn_blocks (padFin (v.length * v.length) r) i hi
  simp only [init, pairFstD_pairEncode, pairSndD_pairEncode, iterate_step, List.length_replicate,
    emit, arg, p₁_st, p₂_st, p₃_st, hne, if_false, hblock, NUPPT.advInput_eq, headD_drop]

end ComLoop

end TCSlib.Cryptography.CommitmentLemmas
