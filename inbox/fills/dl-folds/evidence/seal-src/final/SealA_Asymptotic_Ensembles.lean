/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
-- `NonUniform` is not used here. It replaces, for downstream files, the former import of the
-- facade `TCSlib.Complexity.Randomized`: `ZeroKnowledge/ThreeColoring/SimulatorMachine.lean`
-- uses `NUPPT.Uniform.advice_eq` and reaches `NonUniform` only through this file (gate 03a,
-- finding 12). Drop it once that file imports `NonUniform` itself.
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Ensembles and computational indistinguishability

The asymptotic notion of [PS10, §3.1]: *ensembles* of probability distributions over
`{0,1}^{ℓ(n)}` and *computational indistinguishability* `{X_n} ≈ {Y_n}` against non-uniform
PPT distinguishers, with the three properties the rest of chapters 3 and 4 use over and over:
closure under efficient operations (Lemma 71.5), the hybrid lemma (Lemma 71.6) and the
prediction lemma (Lemma 73.8).

Foundation decision D6: an ensemble is a family of samplers `X n : σ n → (Fin (ℓ n) → Bool)`
from arbitrary finite nonempty seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`); every
length is a syntactic polynomial `Complexity.PolyExpr` (D9). "Efficiently samplable" is the
distribution-level predicate `Ensemble.Samplable`: a polynomial-time sampler from `s n`
uniform bits whose output law is exactly `X n` (`StatClose … 0`). The headline form of
Definition 69.4 gives the distinguisher the input `1^n` (`Ensemble.Indist`, D5); the literal
form `Ensemble.IndistLit` (the distinguisher receives the sample `t` only, activation at
parameter `|t| = ℓ n`) is stated next to it with the bridges `Indist.toLit` and
`IndistLit.toIndist` (injective, i.e. non-constant, `ℓ`; for constant `ℓ` the two forms
coincide as well, by point tests, which is not formalized), never unified silently.

Every asymptotic statement is proved by instantiating a concrete reduction of
`TCSlib.Cryptography.Pseudorandom.Indistinguishability` [Gar26, §3.2] at each `n`, exhibiting
the reduction as a `Complexity.NUPPT` by the closure catalogue of
`TCSlib.Complexity.Randomized.Closure`, and finishing with negligible-function arithmetic
(`not_negligible_iff`, the "infinitely many `n` with `1/p(n)`" idiom of the text,
`not_negligible_iff_exists_polyExpr`).

**Deviation:** `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n`
(literal form `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the
constant case by point tests, not formalized).

The machine constructions and the probability bookkeeping behind the proofs (the negated,
padded-image and multicopy reductions as `NUPPT`s, coin-splitting bijections, the exactness
transfer `StatClose … 0` through `copies`) live in the sibling file
`TCSlib.Cryptography.Asymptotic.EnsemblesLemmas` (inner namespace `EnsembleLemmas`), which
exists only to keep this file within the repository's size limit.

**Repair (run-3 audit P2-2):** `Ensemble` carries the field `nonempty` (an empty seed type is
not a distribution), which restores the frozen shapes of `prediction_lemma` and
`Ensemble.NextBitUnpredictable.pseudorandom` (`NextBit.lean`); the nonemptiness instances
of `predict_eq` are discharged automatically for ensemble seeds and machine coins.

## Main definitions

* `TCSlib.Cryptography.Ensemble` — an ensemble over `{0,1}^{ℓ(n)}` [PS10, Definition 69.3];
  `Ensemble.uniform` — the uniform ensemble `{U_{ℓ(n)}}`.
* `TCSlib.Cryptography.Ensemble.Samplable` — efficiently samplable (distribution level, D6).
* `TCSlib.Cryptography.Ensemble.Indist`, `TCSlib.Cryptography.Ensemble.IndistLit` —
  computational indistinguishability [PS10, Definition 69.4], headline and literal forms;
  `TCSlib.Cryptography.Distinguishes`, `TCSlib.Cryptography.Ensemble.DistinguishesWith` —
  "`D` distinguishes with probability `ε` / `μ(·)`".
* `TCSlib.Cryptography.Ensemble.Pseudorandom` — indistinguishable from uniform
  [PS10, Definition 74.1].
* `TCSlib.Cryptography.Ensemble.push` — the image ensemble `{M(X_n)}` under an `NUPPT`;
  `TCSlib.Cryptography.Ensemble.copies` — `t(n)` independent copies.
* `TCSlib.Cryptography.mixEnsemble` — the sampler of `b ← {0,1}; t ← X^b_n` [PS10, Lemma 73.8].

## Main results

* `TCSlib.Cryptography.Ensemble.Indist.refl`, `Indist.symm`, `Indist.trans` — `≈` is an
  equivalence relation (transitivity is the two-step hybrid lemma, [PS10, §3.1.1]).
* `TCSlib.Cryptography.Ensemble.Indist.push` — closure under efficient operations
  [PS10, Lemma 71.5].
* `TCSlib.Cryptography.hybrid_lemma` — the hybrid lemma [PS10, Lemma 71.6], concrete.
* `TCSlib.Cryptography.Ensemble.Indist.copies` — polynomially many copies (the multicopy
  corollary of the hybrid lemma, [Gar26, Lemma 3.3]).
* `TCSlib.Cryptography.predict_eq` — predicting is distinguishing, the identity behind
  [PS10, p. 73 ("show this!") and Lemma 73.8].
* `TCSlib.Cryptography.prediction_lemma` — the prediction lemma [PS10, Lemma 73.8].
* `TCSlib.Cryptography.not_negligible_iff_exists_polyExpr` — "for infinitely many `n`,
  advantage `≥ 1/p(n)`" is non-negligibility [PS10, §3.1, the ubiquitous contradiction idiom].
* `TCSlib.Cryptography.pairwise_sampling_ineq` — the pairwise-independent sampling
  inequality [PS10, Appendix A, p. 189].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.1: Definitions 69.3, 69.4; §3.1.1: Lemmas 71.5, 71.6, 73.8; §3.2.1: Definition 74.1;
  Appendix A, p. 189.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (Definition 3.4, Lemmas 3.2 and 3.3), Theorem 2.4.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! Seal A (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Asymptotic/Ensembles.lean`, with every seal candidate of its
full TCSlib import closure (548 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockDone _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquivPoly _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ### Ensembles -/

/-- An **ensemble** of probability distributions over `{0,1}^{ℓ(n)}` [PS10, Definition 69.3]:
at each `n` a sampler `X n` from a finite seed type `σ n` (uniformly distributed seeds) into
the `ℓ(n)`-bit strings, the distribution `X_n` being the pushforward of the uniform seed. The
length `ℓ` is a syntactic polynomial (D9).

**Deviation:** each `X_n` is the pushforward of the uniform distribution on a finite nonempty
seed set, so its probabilities are rational (not necessarily dyadic: three seeds mapped to
distinct strings give masses `1/3`; every efficiently samplable ensemble, `Samplable`, has dyadic
laws, D6, but not every dyadic ensemble is samplable, e.g. the point mass at an uncomputable bit;
gate 03a, round 2, R2-3), and it lives
on strings of the fixed length `ℓ(n)` that Definition 69.4 requires (Definition 69.3 allows
arbitrary distributions over `{0,1}^*`). Every ensemble of chapters 3 and 4 is of this form;
the non-dyadic ideal distributions (primes, `Z_q`, permutations) appear only inside
experiments, approximated by the rejection samplers of `Asymptotic/Sampling.lean` (D6, D10).

**Repair (run-3 audit P2-2):** the field `nonempty` was added to the frozen structure of
DESIGN.md §2.11. An empty seed type is not a distribution (every event has probability `0`),
and without the field `NextBitUnpredictable` was vacuous for an empty-seed ensemble that is
not pseudorandom, so `prediction_lemma` and `NextBitUnpredictable.pseudorandom` needed ad hoc
nonemptiness hypotheses. Machine coin types `Fin k → Bool` and every seed type of the campaign
are nonempty, so constructions fill the field by instance resolution. -/
structure Ensemble (ℓ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- Seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- Seed types are nonempty: the sampler defines a probability distribution. -/
  [nonempty : ∀ n, Nonempty (σ n)]
  /-- The sampler at parameter `n`. -/
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)

attribute [instance] Ensemble.fintype Ensemble.nonempty

namespace Ensemble

variable {ℓ : PolyExpr}

/-- The uniform ensemble `{U_{ℓ(n)}}` [PS10, §3.2.1]: seeds are the strings themselves. -/
def uniform (ℓ : PolyExpr) : Ensemble ℓ where
  σ n := Fin (ℓ.eval n) → Bool
  X _ := id

/-- Field equation of the uniform ensemble: the seed type at `n` is `{0,1}^{ℓ(n)}`. -/
theorem uniform_σ (ℓ : PolyExpr) (n : ℕ) : (uniform ℓ).σ n = (Fin (ℓ.eval n) → Bool) := rfl

/-- Field equation of the uniform ensemble: the sampler at `n` is the identity on seeds, read
along `uniform_σ`. -/
theorem uniform_X (ℓ : PolyExpr) (n : ℕ) (x : (uniform ℓ).σ n) :
    (uniform ℓ).X n x = cast (uniform_σ ℓ n) x := rfl

/-- **Efficiently samplable** ensemble (distribution level, D6): there is a syntactic
polynomial `s` and a polynomial-time sampler `S` such that at every `n` the law of
`S(⟨1^n, r⟩)` for `s(n)` uniform bits `r` (padded or truncated to `ℓ(n)` bits) is exactly the
law of `X n` (`StatClose … 0`). This is the "efficiently sample" of [PS10, p. 72, Example];
the multicopy lemma that assumes it is [Gar26, Lemma 3.3] (`Indist.copies`). -/
def Samplable (X : Ensemble ℓ) : Prop :=
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool =>
      padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0

/-- **Computational indistinguishability** `{X_n} ≈ {Y_n}` [PS10, Definition 69.4], headline
form: for every non-uniform PPT `D`, the advantage
`|Pr[t ← X_n : D(1^n, t) = 1] − Pr[t ← Y_n : D(1^n, t) = 1]|` is a negligible function of
`n`. (The text's "there exists a negligible `ε` with advantage `< ε(n)` for all `n`" is
equivalent, `indist_iff_exists_negligible`.)

**Deviation:** `D` receives `1^n` in addition to the sample (D5); the literal form is
`IndistLit`, and the two are related by `Indist.toLit` and `IndistLit.toIndist`. -/
def Indist (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))

/-- **Computational indistinguishability, literal form** [PS10, Definition 69.4]: the
distinguisher receives the sample `t` only, i.e. is activated at parameter `|t| = ℓ(n)`
(`D_{|t|}(t)` in the machine-sequence reading of [PS10, Definition 26.8]). -/
def IndistLit (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n =>
    distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))

/-- A **pseudorandom ensemble** [PS10, Definition 74.1]: indistinguishable from the uniform
ensemble `{U_{ℓ(n)}}`. -/
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)

/-- The defining property of `Pseudorandom`: `X.Pseudorandom ↔ Indist X (uniform ℓ)`. -/
theorem pseudorandom_iff (X : Ensemble ℓ) : X.Pseudorandom ↔ Indist X (uniform ℓ) := Iff.rfl

/-- The image ensemble `{M(X_n)}` of [PS10, Lemma 71.5]: at parameter `n`, draw a seed of `X`
and coins for `M`, run `M(1^n, X_n)` and pad or truncate the output to `ℓ'(n)` bits. The
output length `ℓ'` is an explicit syntactic polynomial so that the padding is itself
polynomial-time (`polyTimeComputable_unaryPoly`). The padding (`padFin`: `false`-padding or
truncation) is lossless when `M` outputs exactly `ℓ'(n)` bits, the only case Definition 69.4
can type (a sufficient condition), and can be lossy otherwise (`[1]` and `[1, 0]` both pad to
`[1, 0, …]`; gate 03a, round 2, R2-5): variable-length
outputs (ciphertexts, views, transcripts) are not ensembles of this kind. -/
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ' where
  σ n := X.σ n × M.Coins n
  X n z := padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X.X n z.1)) z.2)

/-- The blockwise bijection `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q`: a load-bearing private alias of the
canonical `FunFamily.blocks` of `Asymptotic/Adversary.lean`, kept so that the body of
`Ensemble.copies` stays unchanged. -/
private def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  FunFamily.blocks q ℓ

/-- The private alias is the canonical block bijection. -/
private theorem blocks_eq (q ℓ : ℕ) : blocks q ℓ = FunFamily.blocks q ℓ := rfl

/-- `t(n)` independent copies of `X_n`, concatenated into one `t(n)·ℓ(n)`-bit string: the
ensemble `{X_n^{(1)} ‖ ⋯ ‖ X_n^{(t(n))}}` of the multicopy corollary of the hybrid lemma
[PS10, Lemma 71.6; Gar26, Lemma 3.3]. -/
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ) where
  σ n := Fin (t.eval n) → X.σ n
  X n s := (blocks (t.eval n) (ℓ.eval n)).symm (TCSlib.Cryptography.copies (t.eval n) (X.X n) s)

/-- Unfolding of `copies`: bit `i` of the concatenation is bit `i mod ℓ` of copy `i / ℓ`
(through `finProdFinEquiv`).

**Proof sketch.** Expand the copied ensemble's sample field and apply the inverse block
and copy family equations. -/
theorem copies_X (t : PolyExpr) (X : Ensemble ℓ) (n : ℕ) (s : Fin (t.eval n) → X.σ n)
    (i : Fin (t.eval n * ℓ.eval n)) :
    (X.copies t).X n s i = X.X n (s (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 := by
  simp only [copies, blocks_eq, FunFamily.blocks_symm_apply, TCSlib.Cryptography.copies_def,
    finProdFinEquiv_symm_apply]

/-- The uniform ensemble is efficiently samplable: `s := ℓ` and the sampler returns its coins
(`pairSndD` of `⟨1^n, r⟩`). Non-vacuity of `Samplable` (the case `U_n` of D6). -/
theorem uniform_samplable (ℓ : PolyExpr) : (uniform ℓ).Samplable := by
  refine ⟨ℓ, pairSndD, polyTimeComputable_pairSndD, fun n => ?_⟩
  have h : (fun r : Fin (ℓ.eval n) → Bool =>
      padFin (ℓ.eval n) (pairSndD (NUPPT.advInput n (List.ofFn r)))) = (uniform ℓ).X n := by
    funext r
    simp [NUPPT.advInput_eq, padFin_ofFn, uniform]
  rw [h]
  exact StatClose.refl _

end Ensemble

/-! ### The "distinguishes with probability" notations of Definition 69.4 -/

/-- `D` **distinguishes** the distributions `X` and `Y` **with probability `ε`**
[PS10, p. 70, after Definition 69.4]: `|Pr[t ← X : D(t) = 1] − Pr[t ← Y : D(t) = 1]| > ε`. -/
def Distinguishes {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) (ε : ℝ) : Prop :=
  ε < distAdv X Y D

/-- `D` **distinguishes the ensembles** `{X_n}` and `{Y_n}` **with probability `μ(·)`**
[PS10, p. 70]: for all `n`, `D` distinguishes `X_n` and `Y_n` with probability `μ(n)`. -/
def Ensemble.DistinguishesWith {ℓ : PolyExpr} (X Y : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ) :
    Prop :=
  ∀ n, Distinguishes (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) (μ n)

/-- The text's form of Definition 69.4 — "there exists a negligible `ε` with advantage
`< ε(n)` for all `n`" — is equivalent to the frozen form "the advantage is negligible"
[PS10, Definition 69.4]: the advantage lies in `[0, 1]`, so one direction is `Negligible.mono`
and the other takes `ε(n) := advantage(n) + 2^{-n}`. -/
theorem Ensemble.indist_iff_exists_negligible {ℓ : PolyExpr} (X Y : Ensemble ℓ) :
    X.Indist Y ↔ ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) < ε n := by
  constructor
  · intro h D
    refine ⟨fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) + (2 : ℝ)⁻¹ ^ n,
      (h D).add negligible_two_pow_neg, fun n => ?_⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    linarith
  · intro h D
    obtain ⟨ε, hε, hlt⟩ := h D
    refine hε.mono ⟨0, fun n _ => ?_⟩
    have h0 : 0 ≤ distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    rw [abs_of_nonneg h0]
    exact (hlt n).le.trans (le_abs_self _)

/-- **The contradiction idiom of the text** [PS10, §3.1, Lemma 71.5's proof and passim]:
"assume for contradiction that there is a polynomial `p` such that for infinitely many `n` the
advantage is at least `1/p(n)`" is exactly non-negligibility (`not_negligible_iff`), with the
polynomial a syntactic `PolyExpr` with positive values.

**Proof sketch.** (⇒) `not_negligible_iff` gives an exponent `c`; take `p := (n+1)^c`
(`PolyExpr.normal 1 c`), which is positive and dominates `n^c`. (⇐) `p(n) ≤ C(n+1)^c`
(`PolyExpr.eval_le`) and `(n+1)^c ≤ 2^c n^c`, so `p(n) ≤ n^{c+1}` once `n ≥ C·2^c`; the
exponent `c + 1` witnesses `not_negligible_iff`. -/
theorem not_negligible_iff_exists_polyExpr {μ : ℕ → ℝ} :
    ¬ Negligible μ ↔ ∃ p : PolyExpr, (∀ n, 0 < p.eval n) ∧
      ∀ n₀, ∃ n ≥ n₀, 1 / (p.eval n : ℝ) ≤ |μ n| := by
  rw [not_negligible_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨.normal 1 c, fun n => by simp [PolyExpr.eval_normal], fun n₀ => ?_⟩
    obtain ⟨n, hn, h⟩ := hc (max n₀ 1)
    refine ⟨n, le_trans (le_max_left _ _) hn, le_trans ?_ h⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    rw [PolyExpr.eval_normal]
    push_cast
    rw [one_mul]
    exact one_div_le_one_div_of_le (pow_pos (by linarith) c)
      (pow_le_pow_left₀ (by linarith) (by linarith) c)
  · rintro ⟨p, hp, h⟩
    obtain ⟨C, c, hC⟩ := p.eval_le
    refine ⟨c + 1, fun n₀ => ?_⟩
    obtain ⟨n, hn, hμ⟩ := h (max n₀ (C * 2 ^ c + 1))
    refine ⟨n, le_trans (le_max_left _ _) hn, le_trans ?_ hμ⟩
    have hn' : C * 2 ^ c + 1 ≤ n := le_trans (le_max_right _ _) hn
    have key : p.eval n ≤ n ^ (c + 1) := by
      calc p.eval n ≤ C * (n + 1) ^ c := hC n
        _ ≤ C * (2 * n) ^ c := by gcongr; omega
        _ = C * 2 ^ c * n ^ c := by rw [mul_pow, mul_assoc]
        _ ≤ n * n ^ c := by gcongr; omega
        _ = n ^ (c + 1) := by ring
    have hpos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast key)

/-! ### Properties of computational indistinguishability [PS10, §3.1.1] -/

/-- **Reflexivity of `≈`** (non-vacuity of `Indist`): every ensemble is indistinguishable
from itself, the advantage being identically zero. -/
theorem Ensemble.Indist.refl {ℓ : PolyExpr} (X : Ensemble ℓ) : X.Indist X := by
  intro D
  have h : (fun n => distAdv (X.X n) (X.X n) (D.distinguisher n (ℓ.eval n))) =
      fun _ => (0 : ℝ) := by
    funext n
    simp [distAdv_def]
  rw [h]
  exact negligible_zero

/-- **Symmetry of `≈`**: the advantage is symmetric in the two distributions. -/
theorem Ensemble.Indist.symm {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) : Y.Indist X := by
  intro D
  have e : (fun n => distAdv (Y.X n) (X.X n) (D.distinguisher n (ℓ.eval n))) =
      fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) :=
    funext fun n => abs_sub_comm _ _
  rw [e]
  exact h D

/-- **Bridge from the `1^n` form to the literal form** of Definition 69.4: if `{X_n} ≈ {Y_n}`
against distinguishers receiving `1^n`, then also against distinguishers receiving the sample
only [PS10, Definition 69.4; D5].

**Proof sketch.** A literal distinguisher `D` activated at parameter `ℓ(n)` is, as a function
of `n`, the activation of the machine `B := NUPPT.exists_reparam D ℓ` (advice
`D.advice (ℓ n)`, coins `D.coins.subst ℓ`), whose `runAtL n t r` equals `D.runAtL (ℓ n) t r`;
`B` ignores `1^n`. The coin types `B.Coins n` and `D.Coins (ℓ n)` correspond along
`PolyExpr.eval_subst` (`finCongr`), so the acceptance probabilities of
`B.distinguisher n (ℓ n)` and `D.distinguisher (ℓ n) (ℓ n)` agree
(`EnsembleLemmas.acceptProb_reparam`); hence the two advantage functions are equal and `h B`
gives negligibility. -/
theorem Ensemble.Indist.toLit {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) :
    X.IndistLit Y := by
  intro D
  obtain ⟨B, hBc, -, hB⟩ := D.exists_reparam ℓ
  refine (h B).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  simp only [distAdv_def]
  rw [EnsembleLemmas.acceptProb_reparam hBc hB, EnsembleLemmas.acceptProb_reparam hBc hB]

/-- **Bridge from the literal form to the `1^n` form** for injective `ℓ` (every ensemble of
the text): if `{X_n} ≈ {Y_n}` against literal distinguishers, then also against distinguishers
receiving `1^n` [PS10, Definition 69.4; D5].

The hypothesis `hℓ` excludes only constant `ℓ`: a `PolyExpr` has natural-number coefficients,
so `ℓ.eval` is constant or strictly increasing. For constant `ℓ ≡ L` the two forms coincide as
well (not formalized, no consumer): the `2^L` point tests `t ↦ [t = t₀]` are advice-free
literal distinguishers, so `IndistLit` makes `Σ_{t₀} |Pr[X_n = t₀] − Pr[Y_n = t₀]|`, hence the
statistical distance of `X_n` and `Y_n`, negligible, and that bounds every distinguisher
(`distAdv_le_of_statClose`). So D5's "`D` receives `1^n`" costs nothing for ensembles.

**Proof sketch.** `ℓ.eval` is monotone (`PolyExpr.eval_mono`) and injective, hence strictly
increasing, so `n ≤ ℓ n` for all `n`. Let `φ m := n` if `m = ℓ n` (`Classical.choose` of the
preimage, unique by injectivity) and `φ m := 0` off the image; then `φ m ≤ m`, so
`NUPPT.exists_reparam_advice D φ .var` gives a machine `B` with coins `D.coins.subst var =
D.coins` that at parameter `m = ℓ n` runs `D` at parameter `φ m = n` on its first
`D.coinLen n` coins, with the advice `⟨1^n, D.advice n⟩` hard-wired at length `ℓ n`. Hence
`B.distinguisher (ℓ n) (ℓ n)` and `D.distinguisher n (ℓ n)` have equal advantages after
discarding the unread coins (`EnsembleLemmas.acceptProb_reparam_advice`: the coin split
`EnsembleLemmas.coinsEquiv` built on `Fin.appendEquiv`, then
`EnsembleLemmas.acceptProb_coins_fst`), and `h B` gives negligibility. -/
theorem Ensemble.IndistLit.toIndist {ℓ : PolyExpr} {X Y : Ensemble ℓ}
    (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y := by
  classical
  intro D
  have hsm : StrictMono ℓ.eval := ℓ.eval_mono.strictMono_of_injective hℓ
  have hle : ∀ n, n ≤ ℓ.eval n := fun n => hsm.id_le n
  let φ : ℕ → ℕ := fun m => if hm : ∃ n, ℓ.eval n = m then hm.choose else 0
  have hφ : ∀ m, φ m ≤ PolyExpr.var.eval m := by
    intro m
    simp only [φ, PolyExpr.eval_var]
    split_ifs with hm
    · exact (hle _).trans_eq hm.choose_spec
    · exact Nat.zero_le _
  have hφn : ∀ n, φ (ℓ.eval n) = n := by
    intro n
    have hm : ∃ n', ℓ.eval n' = ℓ.eval n := ⟨n, rfl⟩
    simp only [φ, dif_pos hm]
    exact hℓ hm.choose_spec
  obtain ⟨A, hAc, hA⟩ := D.exists_reparam_advice φ .var hφ
  refine (h A).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  have hle' : D.coinLen (φ (ℓ.eval n)) ≤ D.coinLen (PolyExpr.var.eval (ℓ.eval n)) := by
    rw [hφn, PolyExpr.eval_var]
    exact D.coins.eval_mono (hle n)
  simp only [distAdv_def]
  rw [EnsembleLemmas.acceptProb_reparam_advice hAc hA (ℓ.eval n) hle',
    EnsembleLemmas.acceptProb_reparam_advice hAc hA (ℓ.eval n) hle', hφn]

/-- **Closure under efficient operations** [PS10, Lemma 71.5]: if `{X_n} ≈ {Y_n}` then for every
non-uniform PPT `M` (and every explicit output length `ℓ'`), `{M(X_n)} ≈ {M(Y_n)}`.

**Proof sketch.** Fix a distinguisher `D` of the image ensembles. The machine
`D' := EnsembleLemmas.exists_pushRed M D ℓ'` (coins `M.coins + D.coins`, advice
`combineAdvice (M.advice n) (D.advice n)`, built as `NUPPT.ofPolyTime` of a raw function of
the layout `⟨⟨⟨1^n, t⟩, α⟩, r⟩` as in `NUPPT.exists_seq`) runs `M` on `t` with the first
`M.coins n` coins, pads the result to `ℓ'(n)` bits *inside the layout*, where `1^n` is
available (`NUPPT.exists_comp` sees only `y`, gate 03a finding 3; the padding is
`EnsembleLemmas.polyTimeComputable_padL`, a typed cut `pairTakePoly ℓ'` of the output
followed by `0^{ℓ'(n)}`), and hands it to `D` with the remaining coins. Its distinguisher at
`n` is the concrete `sunglassRed P (D.distinguisher n (ℓ' n))` with
`P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` up to the coin split
`EnsembleLemmas.coinsEquiv` (`Fin.appendEquiv`), so by `acceptProb_bind`
(`EnsembleLemmas.acceptProb_pushRed`) its acceptance probabilities on `X_n`, `Y_n` are those
of `D` on `pushSampler P (X.X n) = (X.push M ℓ').X n` and `(Y.push M ℓ').X n`. Hence the
advantage function of `D` on the images is that of `D'` on `X, Y`, negligible by `h D'`. -/
theorem Ensemble.Indist.push {ℓ ℓ' : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) :
    (X.push M ℓ').Indist (Y.push M ℓ') := by
  intro D
  obtain ⟨B, hBc, hB⟩ := EnsembleLemmas.exists_pushRed M D ℓ'
  refine (h B).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  simp only [distAdv_def]
  rw [EnsembleLemmas.acceptProb_pushRed hBc hB (X := X.X n),
    EnsembleLemmas.acceptProb_pushRed hBc hB (X := Y.X n)]
  rfl

/-- **The hybrid lemma** [PS10, Lemma 71.6], at one parameter: if `D` distinguishes `X^0` and
`X^m` with advantage `ε` then some consecutive pair `X^i, X^{i+1}` (`i < m`) is distinguished
by `D` with advantage at least `ε / m`. (The text indexes `X^1, …, X^m` and loses the factor
`m` where `m − 1` steps would do; harmless.) This is the concrete `exists_hybrid_gap` applied to
the acceptance probabilities `g_i = Pr[t ← X^i : D(t) = 1]`. All hybrids share one seed type
`σ` (`X : ℕ → σ → γ`); hybrids with seeds of different shapes are first embedded into a
common product seed. -/
theorem hybrid_lemma {σ γ ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (X : ℕ → σ → γ) (D : γ → ρ → Bool) :
    ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i + 1)) D := by
  obtain ⟨i, hi, h⟩ := exists_hybrid_gap (fun i => acceptProb (X i) D) hm
  exact ⟨i, hi, h⟩

/-- **Transitivity of `≈`** [PS10, §3.1.1, "Transitivity – The Hybrid Lemma"]: the two-step
case of the hybrid lemma. The advantage between `X` and `Z` is at most the sum of the
advantages between `X, Y` and `Y, Z` (triangle inequality), and sums of negligible functions
are negligible. -/
theorem Ensemble.Indist.trans {ℓ : PolyExpr} {X Y Z : Ensemble ℓ} (h₁ : X.Indist Y)
    (h₂ : Y.Indist Z) : X.Indist Z := by
  intro D
  refine ((h₁ D).add (h₂ D)).mono ⟨0, fun n _ => ?_⟩
  have h0 : 0 ≤ distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) +
      distAdv (Y.X n) (Z.X n) (D.distinguisher n (ℓ.eval n)) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg h0]
  simp only [distAdv_def]
  rw [abs_abs]
  exact abs_sub_le _ _ _

/-- **Polynomially many copies** (the multicopy corollary of the hybrid lemma,
[PS10, Lemma 71.6; Gar26, Lemma 3.3]): if `{X_n} ≈ {Y_n}` and both ensembles are efficiently
samplable, then `t(n)` independent copies remain indistinguishable for every syntactic
polynomial `t`.

The samplability hypotheses are those of [Gar26, Lemma 3.3]'s uniform reduction, which
samples the other copies (D6). Against non-uniform distinguishers they can be dropped: hard-wire
the hybrid index and the other `t(n) − 1` copies that keep the gap as advice
(`NUPPT.exists_withAdvice`). That form is not proved, since no consumer needs copies of a
non-samplable ensemble (gate 03a, finding 2).

**Proof sketch.** Fix a distinguisher `D` of the `t(n)`-fold products. At each `n` with
`t(n) > 0`, `exists_multicopyRed_ge` (through the block bijection `blocks`) gives a hybrid
index `k_n < t(n)` such that the concrete reduction `multicopyRed (X.X n) (Y.X n) (t n) k_n D'`
(sample `k_n` copies of `Y`, `t(n) − k_n − 1` copies of `X`, plant the challenge at position
`k_n`, call `D` once) has advantage at least `ε(n) / t(n)`; the index is chosen per `n`
(`choose`; for `t(n) = 0` any index, both products being the one-point distribution,
`EnsembleLemmas.distAdv_eq_zero_of_subsingleton`) and `1^{k_n}` is hard-wired into the
advice (`NUPPT.exists_withAdvice`). The reduction is the `NUPPT` of
`EnsembleLemmas.exists_copiesRed`: the `Samplable` evaluators of `X` and `Y` are run on the
`t(n)` chunks of fresh coins by the state loop `EnsembleLemmas.CopiesLoop`
(`polyTimeComputable_iterateEmit`, coins cut by `pairTakePoly`/`pairDropPoly`, the challenge
planted at the hard-wired position), and `D` is called through `NUPPT.exists_seq`. The laws
of the sampled copies equal the ideal `X.X n`, `Y.X n` (`StatClose … 0`, lifted to the product
by `EnsembleLemmas.statClose_copies` and `StatClose.prod`), so the acceptance probabilities
coincide exactly (`EnsembleLemmas.acceptProb_multicopyRed_congr`). Hence
`distAdv ((X.copies t).X n) ((Y.copies t).X n) D ≤ t(n) · distAdv (X.X n) (Y.X n) B_n` with
the reduction `B` independent of `n` up to the advice, and `t(n) ≤ C (n+1)^c`
(`PolyExpr.eval_le`) makes the right-hand side negligible
(`EnsembleLemmas.negligible_polyExpr_mul`, from `Negligible.mul_pow` and
`Negligible.const_mul`); `Negligible.mono` concludes. -/
theorem Ensemble.Indist.copies {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y)
    (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) :
    (X.copies t).Indist (Y.copies t) := by
  classical
  obtain ⟨sX, SX, hSX, hXc⟩ := hX
  obtain ⟨sY, SY, hSY, hYc⟩ := hY
  intro D
  -- the distinguisher of `t(n)`-tuples behind `D`
  obtain ⟨D', hD'⟩ : ∃ D' : ∀ n, (Fin (t.eval n) → Fin (ℓ.eval n) → Bool) → D.Coins n → Bool,
      ∀ n v r, D' n v r = D.distinguisher n ((PolyExpr.mul t ℓ).eval n)
        ((EnsembleLemmas.blocks (t.eval n) (ℓ.eval n)).symm v) r := ⟨_, fun _ _ _ => rfl⟩
  have hadv : ∀ n, distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) =
      distAdv (TCSlib.Cryptography.copies (t.eval n) (X.X n))
        (TCSlib.Cryptography.copies (t.eval n) (Y.X n)) (D' n) := by
    intro n
    have e : ∀ Z : Ensemble ℓ, acceptProb ((Z.copies t).X n)
        (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) =
        acceptProb (TCSlib.Cryptography.copies (t.eval n) (Z.X n)) (D' n) := by
      intro Z
      refine OneWay.uprob_congr fun z => ?_
      rw [hD']
      exact Iff.rfl
    simp only [distAdv_def]
    rw [e, e]
  -- the hybrid index at each `n` (any index when `t(n) = 0`)
  have hex : ∀ n, ∃ k, k ≤ t.eval n ∧ (0 < t.eval n → k < t.eval n ∧
      distAdv (TCSlib.Cryptography.copies (t.eval n) (X.X n))
        (TCSlib.Cryptography.copies (t.eval n) (Y.X n)) (D' n) / t.eval n ≤
        distAdv (X.X n) (Y.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) k (D' n))) := by
    intro n
    by_cases ht : 0 < t.eval n
    · obtain ⟨k, hk, hge⟩ := exists_multicopyRed_ge (X.X n) (Y.X n) ht (D' n)
      exact ⟨k, hk.le, fun _ => ⟨hk, hge⟩⟩
    · exact ⟨0, Nat.zero_le _, fun h' => absurd h' ht⟩
  choose k hk using hex
  obtain ⟨B, hBc, hB⟩ := EnsembleLemmas.exists_copiesRed D hSX hSY sX sY ℓ t k fun n => (hk n).1
  -- the machine's advantage is the concrete reduction's advantage
  have hBadv : ∀ n, distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) =
      distAdv (X.X n) (Y.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) (k n) (D' n)) := by
    intro n
    have hlen : B.coinLen n = (t.eval n * sX.eval n + t.eval n * sY.eval n) + D.coinLen n := by
      simp [NUPPT.coinLen_eq, hBc]
    obtain ⟨e, he⟩ : ∃ e : ((Fin (t.eval n) → Fin (sX.eval n) → Bool) ×
        (Fin (t.eval n) → Fin (sY.eval n) → Bool)) × D.Coins n ≃ B.Coins n,
        ∀ c, e c = EnsembleLemmas.coinsEquiv hlen
          (EnsembleLemmas.coinsEquiv rfl ((EnsembleLemmas.blocks _ _).symm c.1.1,
            (EnsembleLemmas.blocks _ _).symm c.1.2), c.2) :=
      ⟨((((EnsembleLemmas.blocks _ _).symm.prodCongr (EnsembleLemmas.blocks _ _).symm).trans
        (EnsembleLemmas.coinsEquiv rfl)).prodCongr (Equiv.refl _)).trans
          (EnsembleLemmas.coinsEquiv hlen), fun _ => rfl⟩
    have hpt : ∀ (z : Fin (ℓ.eval n) → Bool) c, B.distinguisher n (ℓ.eval n) z (e c) =
        multicopyRed
          (fun r : Fin (sX.eval n) → Bool => padFin (ℓ.eval n) (SX (NUPPT.advInput n (List.ofFn r))))
          (fun r : Fin (sY.eval n) → Bool => padFin (ℓ.eval n) (SY (NUPPT.advInput n (List.ofFn r))))
          (t.eval n) (k n) (D' n) z c := by
      intro z c
      rw [he]
      simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
          EnsembleLemmas.ofFn_coinsEquiv, hB,
        multicopyRed_def, hD']
    have hdist : ∀ Z : Ensemble ℓ, acceptProb (Z.X n) (B.distinguisher n (ℓ.eval n)) =
        acceptProb (Z.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) (k n) (D' n)) := by
      intro Z
      rw [← EnsembleLemmas.acceptProb_coins_equiv e, ← EnsembleLemmas.acceptProb_multicopyRed_congr
        (hXc n) (hYc n)]
      congr 1
      funext z c
      exact hpt z c
    simp only [distAdv_def]
    rw [hdist, hdist]
  -- the hybrid bound at each `n`
  have hbound : ∀ n, distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) ≤
      (t.eval n : ℝ) * distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) := by
    intro n
    rw [hBadv, hadv]
    by_cases ht : 0 < t.eval n
    · obtain ⟨-, hk2⟩ := (hk n).2 ht
      have htR : (0 : ℝ) < t.eval n := by exact_mod_cast ht
      rw [div_le_iff₀ htR] at hk2
      linarith
    · have ht0 : t.eval n = 0 := Nat.eq_zero_of_not_pos ht
      have hsub : Subsingleton (Fin (t.eval n) → Fin (ℓ.eval n) → Bool) := by
        rw [ht0]
        infer_instance
      rw [EnsembleLemmas.distAdv_eq_zero_of_subsingleton]
      exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  refine (EnsembleLemmas.negligible_polyExpr_mul t (h B)).mono ⟨0, fun n _ => ?_⟩
  have h₁ : (0 : ℝ) ≤ distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) := abs_nonneg _
  have h₂ : (0 : ℝ) ≤ distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) := abs_nonneg _
  rw [abs_of_nonneg h₁, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) h₂)]
  exact hbound n

/-! ### Distinguishing versus predicting [PS10, p. 73, Lemma 73.8] -/

/-- The sampler of the prediction experiment `b ← {0,1}; t ← X^b_n` [PS10, Lemma 73.8]: output
the bit `b` together with a sample of `X¹_n` if `b = 1` and of `X⁰_n` otherwise (both seeds are
drawn; the unused one is ignored). -/
def mixEnsemble {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (n : ℕ) :
    Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool) :=
  fun z => (z.1, if z.1 then X₁.X n z.2.2 else X₀.X n z.2.1)

/-- **Predicting is distinguishing** — the identity behind [PS10, p. 73 ("any such predictor
would be a valid distinguisher (show this!)") and the proof of Lemma 73.8]: for samplers
`X⁰, X¹` and any `D` (used as a predictor of the bit `b` in `b ← {0,1}; t ← X^b`),
`Pr[D(t) = b] = 1/2 + (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2`. In particular a predictor with
success `1/2 + δ` is a distinguisher with advantage `2δ`, and conversely.

**Repair (run-3 audit P2-2):** the seed types and the coin type carry `Nonempty` instances
(with an empty `ρ`, `σ₀` or `σ₁` the left-hand side is the probability over an empty space,
`0`, while the right-hand side is `1/2`); for ensemble seeds (`Ensemble.nonempty`) and machine
coins (`Fin k → Bool`) they are found by instance resolution.

**Proof sketch.** Split on `b` (`uprob_bool_prod` after regrouping the sample space): for
`b = 1` the event is `D(X¹) = 1`, for `b = 0` it is `D(X⁰) ≠ 1`, whose probability is
`1 − Pr[D(X⁰) = 1]` (`uprob_not`); the unused seed is an ignored uniform coordinate
(`acceptProb_fst`, `acceptProb_snd`). -/
theorem predict_eq {ℓ : ℕ} {σ₀ σ₁ ρ : Type*} [Fintype σ₀] [Fintype σ₁] [Fintype ρ]
    [Nonempty σ₀] [Nonempty σ₁] [Nonempty ρ]
    (X₀ : σ₀ → (Fin ℓ → Bool)) (X₁ : σ₁ → (Fin ℓ → Bool)) (D : (Fin ℓ → Bool) → ρ → Bool) :
    uprob (fun z : (Bool × (σ₀ × σ₁)) × ρ =>
        D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) =
      1 / 2 + (acceptProb X₁ D - acceptProb X₀ D) / 2 := by
  rw [← uprob_comp_equiv (Equiv.prodAssoc Bool (σ₀ × σ₁) ρ).symm, uprob_bool_prod]
  have hA : uprob (fun c : (σ₀ × σ₁) × ρ => D (X₀ c.1.1) c.2 = false) =
      1 - acceptProb X₀ D := by
    rw [← acceptProb_fst (τ := σ₁) X₀ D, acceptProb_def, ← uprob_not]
    congr 1
    funext c
    simp
  have hB : uprob (fun c : (σ₀ × σ₁) × ρ => D (X₁ c.1.2) c.2 = true) = acceptProb X₁ D := by
    rw [← acceptProb_snd (τ := σ₀) X₁ D]
    rfl
  simp only [Equiv.prodAssoc_symm_apply, Bool.false_eq_true, if_false, if_true]
  rw [hA, hB]
  ring

/-- **The prediction lemma** [PS10, Lemma 73.8]: if a non-uniform PPT `D` distinguishes
`{X⁰_n}` and `{X¹_n}` with probability `μ(n)` for infinitely many `n`, then there is a
non-uniform PPT `A` with `Pr[b ← {0,1}; t ← X^b_n : A(1^n, t) = b] > 1/2 + μ(n)/2` for
infinitely many `n`.

**Repair (run-3 audit P2-2):** the ad hoc hypotheses `h₀ h₁ : ∀ n, Nonempty (X.σ n)` of the
run-2 statement were dropped; they are the field `Ensemble.nonempty`, and the frozen shape of
DESIGN.md §2.11 is restored.

**Proof sketch.** By `predict_eq` at each `n`, `D` itself predicts with probability
`1/2 + (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2` and the negated machine `D'` (output `[true]`
iff `D`'s output is not `[true]`: `EnsembleLemmas.exists_negRed`, i.e. `NUPPT.exists_comp`
with the FP-level `polyTimeComputable_ite` on `pairEq`) predicts with probability
`1/2 − (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2`. On the infinite set of `n` where
`μ(n) < |Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]|`, the sign of the difference is positive infinitely
often or negative infinitely often (pigeonhole on an infinite set, no advice needed); take
`A := D` in the first case and `A := D'` in the second. The seed-space reindexing between the
experiment of the statement and `predict_eq` is `uprob_comp_equiv`. -/
theorem prediction_lemma {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ)
    (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ.eval n))) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1 / 2 + μ n / 2 <
      uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
        A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1 := by
  -- the signed advantage of `D`
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ n, δ n = acceptProb (X₁.X n) (D.distinguisher n (ℓ.eval n)) -
      acceptProb (X₀.X n) (D.distinguisher n (ℓ.eval n)) := ⟨_, fun _ => rfl⟩
  have hkey : ∀ n, distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ.eval n)) = |δ n| := fun n => by
    rw [hδ]
    exact abs_sub_comm _ _
  -- predicting is distinguishing, for any machine `A`
  have hpred : ∀ (A : NUPPT) n, (uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
      A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1) =
      1 / 2 + (acceptProb (X₁.X n) (A.distinguisher n (ℓ.eval n)) -
        acceptProb (X₀.X n) (A.distinguisher n (ℓ.eval n))) / 2 := fun A n =>
    predict_eq (X₀.X n) (X₁.X n) (A.distinguisher n (ℓ.eval n))
  by_cases hpos : ∀ n₀, ∃ n ≥ n₀, μ n < δ n
  · -- the difference is positive infinitely often: `D` itself predicts
    refine ⟨D, fun n₀ => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hpos n₀
    refine ⟨n, hn, ?_⟩
    rw [hpred, ← hδ]
    linarith
  · -- otherwise it is negative infinitely often: the negated machine predicts
    push_neg at hpos
    obtain ⟨n₁, hn₁⟩ := hpos
    have hneg : ∀ n₀, ∃ n ≥ n₀, μ n < -δ n := by
      intro n₀
      obtain ⟨n, hn, hlt⟩ := h (max n₀ n₁)
      refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
      have h1 := hn₁ n (le_trans (le_max_right _ _) hn)
      rw [hkey] at hlt
      rcases le_or_gt 0 (δ n) with h0 | h0
      · rw [abs_of_nonneg h0] at hlt
        linarith
      · rw [abs_of_neg h0] at hlt
        exact hlt
    obtain ⟨A, hAc, hA⟩ := EnsembleLemmas.exists_negRed D
    refine ⟨A, fun n₀ => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hneg n₀
    refine ⟨n, hn, ?_⟩
    rw [hpred, EnsembleLemmas.acceptProb_negRed hAc hA, EnsembleLemmas.acceptProb_negRed hAc hA]
    have := hδ n
    linarith

/-! ### The pairwise-independent sampling inequality [PS10, Appendix A, p. 189] -/

/-- **Pairwise-independent sampling inequality** [PS10, Appendix A, p. 189]: for pairwise
independent bits `X_1, …, X_m`, each `true` with probability `p`, and `ε > 0`,
`Pr[|∑ᵢ X_i / m − p| ≥ ε] ≤ 1 / (4 ε² m)`. The concrete lemma is
`HardcoreBit.chebyshev_pairwise_ident` [Gar26, Theorem 2.4], restated with the empirical mean.

**Deviation:** the text states the inequality for real random variables with `|X_i| ≤ 1` and
mean `μ` with the bound `(1 − μ²)/(m ε²)`; here the variables are bits (the only case used in
the campaign) and the bound is the variance bound `p(1−p) ≤ 1/4` of the concrete layer. Bits
satisfy the text's hypothesis, and `1/4 > 1 − p²` exactly when `p > √3/2`, so for such `p`
this bound is weaker than the text's (at `p = 1` the text gives `0`); the variance form
`p(1−p)/(m ε²)` would imply both. -/
theorem pairwise_sampling_ineq {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    {X : ι → Ω → Bool} (hX : HardcoreBit.PairwiseIndep X) {p : ℝ}
    (hp : ∀ i, uprob (fun ω => X i ω = true) = p) {ε : ℝ} (hε : 0 < ε)
    (hm : 0 < Fintype.card ι) :
    uprob (fun ω => ε ≤ |(∑ i, HardcoreBit.ind (X i ω)) / Fintype.card ι - p|) ≤
      1 / (4 * ε ^ 2 * Fintype.card ι) := by
  have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  refine le_of_eq_of_le ?_ (HardcoreBit.chebyshev_pairwise_ident hX hp hε hm)
  apply OneWay.uprob_congr
  intro ω
  rw [show (∑ i, HardcoreBit.ind (X i ω)) / (Fintype.card ι : ℝ) - p =
      (∑ i, HardcoreBit.ind (X i ω) - p * Fintype.card ι) / Fintype.card ι by
        field_simp, abs_div, abs_of_pos hm', le_div_iff₀ hm']

end TCSlib.Cryptography
