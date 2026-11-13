/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lamport's one-time signatures (statement phase)

[PS10, Protocol 137.1]: for a one-way function `f`,
- `Gen(1^n)` samples `x_i^b ← U_n` for `i ∈ [n]` and `b ∈ {0, 1}`, and outputs
  `sk = (x_i^b)` and `pk = (f(x_i^b))`;
- `Sign_sk(m)` outputs `σ = (x_1^{m_1}, …, x_n^{m_n})`;
- `Ver_pk(m, σ)` accepts iff `f(σ_i) = f(x_i^{m_i})` for all `i`.

Theorem 137.2: if `f` is one-way, the scheme is one-time secure.

**The encoding.**
- `f` is a function family with `n`-bit inputs at parameter `n` (`lamportOWF`), given with a
  polynomial-time evaluator `E` on `⟨1^n, x⟩` that agrees with `f` on `n`-bit `x` (`hfE`, the
  form of `FunFamily.Easy`).
- The secret key is `Gen`'s `2n²` coins. Segment `i` (bits `2ni` to `2ni + 2n − 1`) is
  `x_i^0 ‖ x_i^1`.
- The public key is the tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩`, and a signature is the
  concatenation of the `n` revealed preimages: `n²` bits.
- The three algorithms are instances of the ch. 2–4 layer's block loop (`blockEncFun`), run over
  the message bits.

**Deviations, declared once here.**
- **`Ver` tests lengths first.** It rejects unless the message has `n` bits and the signature
  `n²`. So `E` is only ever evaluated on `n`-bit preimage candidates, where it agrees with `f`. An
  evaluator is unconstrained elsewhere, and a `Ver` evaluating it there could accept forgeries
  that do not invert `f`.
- **The one-way function is strong** ([PS10, Definition 27.3], `FunFamily.StrongOneWay`), the
  notes' "one-way function"; by §2.4 a weak one suffices.

## Main definitions

* `Authentication.lamportOWF`: `f` as a `FunFamily`.
* `Authentication.lamport`: Protocol 137.1 as a `SignatureScheme`, with correctness proved.

## Main results

* The ordinary `lamportHalf_eq`, emission and string-function equations expose the algorithms.
* `Authentication.lamportOWF_inLen`, `lamportOWF_outLen`, `lamportOWF_f`: the function-family fields.
* `Authentication.lamport_msgLen`, `lamport_sigLen`, `lamport_gen`, `lamport_sign`, `lamport_ver`:
  the signature-scheme data fields.
* `Authentication.lamportVerFun_sign`: correctness, `Ver` accepts honest signatures.
* `Authentication.lamport_oneTimeSecure` (Thm 137.2, stated; a `sorry` under the source's sketch).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.4, Protocol 137.1 and Theorem 137.2 (book pp. 136–138).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal B (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Authentication/Signatures/Lamport.lean`, with every seal candidate of its
full TCSlib import closure (764 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.TCSlib.Cryptography.Authentication.SignatureScheme.Accepts _root_.TCSlib.Cryptography.Authentication.SignatureScheme.OneTimeSecure _root_.TCSlib.Cryptography.Authentication.SignatureScheme.Secure _root_.TCSlib.Cryptography.Authentication.SignatureScheme.forgeGame _root_.TCSlib.Cryptography.Authentication.SignatureScheme.forgerCodec _root_.TCSlib.Cryptography.Authentication.SignatureScheme.signImpl _root_.TCSlib.Cryptography.Authentication.atParam _root_.TCSlib.Cryptography.Authentication.splitBits _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.seedEquivPoly _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.ansRead _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.cntRead _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs

open TCSlib.Cryptography.PrivateKeyScheme (encodeList)

/-! ### Blocks and block loops -/

/-- The preimage `x_i^b` inside the segment `x_i^0 ‖ x_i^1` of `2n` bits. -/
def lamportHalf (n : ℕ) (b : Bool) (s : List Bool) : List Bool := if b then s.drop n else s.take n

/-- The selected preimage is the suffix after `n` bits for `true`, and the first `n` bits
for `false`. -/
theorem lamportHalf_eq (n : ℕ) (b : Bool) (s : List Bool) :
    lamportHalf n b s = if b then s.drop n else s.take n := rfl

/-- A half of a `2n`-bit segment has `n` bits. -/
theorem length_lamportHalf {n : ℕ} (b : Bool) {s : List Bool} (hs : s.length = 2 * n) :
    (lamportHalf n b s).length = n := by
  cases b <;> simp [lamportHalf, hs] <;> omega

/-- The concatenation of `q` blocks of `B` bits has `q · B` bits. -/
theorem length_flatten_ofFn {B : ℕ} : ∀ {q : ℕ} (g : Fin q → List Bool),
    (∀ i, (g i).length = B) → (List.ofFn g).flatten.length = q * B
  | 0, _, _ => by simp
  | q + 1, g, hg => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hg 0,
      length_flatten_ofFn (fun i => g i.succ) (fun i => hg i.succ), Nat.succ_mul]
    omega

/-- Segment `i` of the concatenation of `B`-bit blocks `g 0, …, g (q − 1)` is `g i`. -/
theorem coinBlock_flatten_ofFn {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ i, (g i).length = B)
    (i : Fin q) : coinBlock B i (List.ofFn g).flatten = g i := by
  rw [coinBlock_flatten (List.ofFn g) (fun c hc => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact hg j) i (by simp)]
  simp

/-- **The block loop over a message** (`blockEncFun` with one-bit blocks): its output is the
tuple of the emissions on the layouts `⟨⟨⟨u, ⟨pk, [m_i]⟩⟩, []⟩, segment i⟩`. -/
theorem blockEncFun_ofFn (G : List Bool → List Bool) (B : PolyExpr) (u pk : List Bool) {q : ℕ}
    (m : Fin q → Bool) (r : List Bool) :
    blockEncFun G (.const 1) B (blockState u pk (List.ofFn m) r) =
      encodeList (List.ofFn fun i : Fin q =>
        G (NUPPT.layout u (pairEncode pk [m i]) [] (coinBlock (B.eval u.length) i r))) := by
  have hlen : (List.ofFn m).length ≤ (blockState u pk (List.ofFn m) r).length := by
    simp only [blockState_eq, length_pairEncode, List.length_ofFn]
    omega
  rw [blockEncFun_eq]
  rw [blockEncFun_spec G (.const 1) B u pk (blockState u pk (List.ofFn m) r).length
    (List.ofFn m) r (by simpa using hlen)]
  simp only [PolyExpr.eval_const]
  rw [blockList_ofFn G _ u pk q m r _ (by simp only [List.length_ofFn] at hlen; omega)]

/-- **The tuple flattener** (`decListFun pairSndD`): on `⟨[], encodeList l⟩` it concatenates `l`. -/
theorem decListFun_pairSndD (l : List (List Bool)) :
    decListFun pairSndD (pairEncode [] (encodeList l)) = l.flatten := by
  have hlen : l.length ≤ (pairEncode [] (encodeList l)).length := by
    have := length_le_length_encodeList l
    simp only [length_pairEncode]
    omega
  rw [decListFun_eq]
  rw [decListFun_spec pairSndD [] _ l hlen]
  simp

/-! ### The algorithms as string functions -/

/-- `f(x)` on the layout `⟨⟨⟨1^n, y⟩, α⟩, x⟩`: `E(⟨1^n, x⟩)`. -/
def lamportEvalEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  E (pairEncode (NUPPT.inParam v) (NUPPT.inCoins v))

/-- The evaluation emission applies `E` to the parameter paired with the current coin block. -/
theorem lamportEvalEmit_eq (E : List Bool → List Bool) (v : List Bool) :
    lamportEvalEmit E v = E (pairEncode (NUPPT.inParam v) (NUPPT.inCoins v)) := rfl

/-- `Gen`'s emission on the layout `⟨⟨⟨1^n, y⟩, α⟩, x^0 ‖ x^1⟩`: the pair `⟨f(x^0), f(x^1)⟩`. -/
def lamportPairEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).take (NUPPT.inParam v).length)))
    (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).drop (NUPPT.inParam v).length)))

/-- The key-generation emission pairs the images of the first and second preimage blocks. -/
theorem lamportPairEmit_eq (E : List Bool → List Bool) (v : List Bool) :
    lamportPairEmit E v =
      pairEncode (E (pairEncode (NUPPT.inParam v)
          ((NUPPT.inCoins v).take (NUPPT.inParam v).length)))
        (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).drop (NUPPT.inParam v).length))) := rfl

/-- `Sign`'s emission on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, x^0 ‖ x^1⟩`: the preimage `x^b`. -/
def lamportSelEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then (NUPPT.inCoins v).drop (NUPPT.inParam v).length
  else (NUPPT.inCoins v).take (NUPPT.inParam v).length

/-- The signing emission chooses the second or first preimage block according to the message
bit in the argument. -/
theorem lamportSelEmit_eq (v : List Bool) :
    lamportSelEmit v =
      if (pairSndD (NUPPT.inArg v)).headD false then
        (NUPPT.inCoins v).drop (NUPPT.inParam v).length
      else (NUPPT.inCoins v).take (NUPPT.inParam v).length := rfl

/-- `Ver`'s selection on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, ⟨⟨y^0, y^1⟩, []⟩⟩` (a block of the
public key): `y^b`. -/
def lamportPkEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then pairSndD (pairFstD (NUPPT.inCoins v))
  else pairFstD (pairFstD (NUPPT.inCoins v))

/-- The public-key emission chooses the second or first image in the current encoded block
according to the message bit. -/
theorem lamportPkEmit_eq (v : List Bool) :
    lamportPkEmit v =
      if (pairSndD (NUPPT.inArg v)).headD false then pairSndD (pairFstD (NUPPT.inCoins v))
      else pairFstD (pairFstD (NUPPT.inCoins v)) := rfl

/-- The length of a public-key block `⟨⟨y^0, y^1⟩, []⟩` with `L`-bit images: `6L + 6`. -/
def lamportPkBlock (L : PolyExpr) : PolyExpr := .add (.mul (.const 6) L) (.const 6)

/-- The public-key block polynomial is `6L + 6`. -/
theorem lamportPkBlock_eq (L : PolyExpr) :
    lamportPkBlock L = .add (.mul (.const 6) L) (.const 6) := rfl

/-- `Gen` on the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with `2n²` coins `ρ`: `⟨pk, ρ⟩`, where `pk` is the
tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the `2n`-bit segments of `ρ`. -/
def lamportGenFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (blockEncFun (lamportPairEmit E) (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (List.replicate (NUPPT.inParam z).length true)
        (NUPPT.inCoins z)))
    (NUPPT.inCoins z)

/-- The generator word pairs the public-key block-loop output with the original preimage tape. -/
theorem lamportGenFun_eq (E : List Bool → List Bool) (z : List Bool) :
    lamportGenFun E z =
      pairEncode
        (blockEncFun (lamportPairEmit E) (.const 1) (.mul (.const 2) .var)
          (blockState (NUPPT.inParam z) [] (List.replicate (NUPPT.inParam z).length true)
            (NUPPT.inCoins z)))
        (NUPPT.inCoins z) := rfl

/-- `Sign` on the layout `⟨⟨⟨1^n, ⟨sk, m⟩⟩, α⟩, r⟩`: the concatenation of the `x_i^{m_i}`. -/
def lamportSignFun (z : List Bool) : List Bool :=
  decListFun pairSndD (pairEncode []
    (blockEncFun lamportSelEmit (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (pairSndD (NUPPT.inArg z)) (pairFstD (NUPPT.inArg z)))))

/-- The signing word concatenates the preimage blocks selected by the message bits. -/
theorem lamportSignFun_eq (z : List Bool) :
    lamportSignFun z =
      decListFun pairSndD (pairEncode []
        (blockEncFun lamportSelEmit (.const 1) (.mul (.const 2) .var)
          (blockState (NUPPT.inParam z) [] (pairSndD (NUPPT.inArg z))
            (pairFstD (NUPPT.inArg z))))) := rfl

/-- `Ver` on `⟨1^n, ⟨pk, ⟨m, σ⟩⟩⟩`: `[true]` iff `m` has `n` bits, `σ` has `n²` bits, and the
images of the `n`-bit blocks of `σ` are the public-key entries selected by `m`. -/
def lamportVerFun (L : PolyExpr) (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  [(decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length) &&
      decide ((pairSndD (pairSndD (pairSndD w))).length =
        (pairFstD w).length * (pairFstD w).length)) &&
    decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
        (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
          (pairSndD (pairSndD (pairSndD w)))) =
      blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
        (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w))) (pairFstD (pairSndD w))))]

/-- Verification conjoins the message and signature length tests with equality of the
signature-image word and the selected public-key word. -/
theorem lamportVerFun_eq (L : PolyExpr) (E : List Bool → List Bool) (w : List Bool) :
    lamportVerFun L E w =
      [(decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length) &&
          decide ((pairSndD (pairSndD (pairSndD w))).length =
            (pairFstD w).length * (pairFstD w).length)) &&
        decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
            (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
              (pairSndD (pairSndD (pairSndD w)))) =
          blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
            (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
              (pairFstD (pairSndD w))))] := rfl

/-! ### Efficiency -/

section Efficiency

variable {E : List Bool → List Bool} (hE : PolyTimeComputable E)

include hE in
/-- `f(x)` on a layout is polynomial-time. -/
theorem polyTimeComputable_lamportEvalEmit : PolyTimeComputable (lamportEvalEmit E) :=
  hE.comp (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)

include hE in
/-- `Gen`'s emission is polynomial-time. -/
theorem polyTimeComputable_lamportPairEmit : PolyTimeComputable (lamportPairEmit E) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hp := hu.pairEncode NUPPT.polyTimeComputable_inCoins
  have h := (hE.comp (hu.pairEncode ((polyTimeComputable_pairTakePoly .var).comp hp))).pairEncode
    (hE.comp (hu.pairEncode ((polyTimeComputable_pairDropPoly .var).comp hp)))
  convert h using 1
  funext v
  simp [lamportPairEmit, Function.comp_apply]

/-- `Sign`'s emission is polynomial-time. -/
theorem polyTimeComputable_lamportSelEmit : PolyTimeComputable lamportSelEmit := by
  have hp := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have h := polyTimeComputable_ite
    (polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    ((polyTimeComputable_pairDropPoly .var).comp hp)
    ((polyTimeComputable_pairTakePoly .var).comp hp)
  convert h using 1
  funext v
  simp [lamportSelEmit, Function.comp_apply]

/-- `Ver`'s selection is polynomial-time. -/
theorem polyTimeComputable_lamportPkEmit : PolyTimeComputable lamportPkEmit := by
  have hc := NUPPT.polyTimeComputable_inCoins
  have h := polyTimeComputable_ite
    (polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hc)
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp hc)
  convert h using 1

include hE in
/-- `Gen` is polynomial-time. -/
theorem polyTimeComputable_lamportGenFun : PolyTimeComputable (lamportGenFun E) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hst := hu.pairEncode ((polyTimeComputable_const []).pairEncode
    ((polyTimeComputable_unary.comp hu).pairEncode NUPPT.polyTimeComputable_inCoins))
  have h := ((blockEncFun_poly (polyTimeComputable_lamportPairEmit hE) (.const 1)
    (.mul (.const 2) .var)).comp hst).pairEncode NUPPT.polyTimeComputable_inCoins
  refine h.congr fun z => ?_
  simp only [lamportGenFun_eq, blockState_eq, Function.comp_apply]

/-- `Sign` is polynomial-time. -/
theorem polyTimeComputable_lamportSignFun : PolyTimeComputable lamportSignFun := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hArg := NUPPT.polyTimeComputable_inArg
  have hst := hu.pairEncode ((polyTimeComputable_const []).pairEncode
    ((polyTimeComputable_pairSndD.comp hArg).pairEncode (polyTimeComputable_pairFstD.comp hArg)))
  have h := (decListFun_poly polyTimeComputable_pairSndD).comp
    ((polyTimeComputable_const []).pairEncode
      ((blockEncFun_poly polyTimeComputable_lamportSelEmit (.const 1)
        (.mul (.const 2) .var)).comp hst))
  refine h.congr fun z => ?_
  simp only [lamportSignFun_eq, blockState_eq, Function.comp_apply]

include hE in
/-- `Ver` is polynomial-time: two length tests (`polyTimeComputable_lenEq`) and an equality of
two block loops (`polyTimeComputable_pairEq`).

**Proof sketch.** Project the parameter, public key, message and signature from the input.
Compare the message length with `n` and the signature length with `n²`, representing the latter
bound by a unary square. The two polynomial-time block loops produce the images of the
signature blocks and the public-key entries selected by the message. Compare these two words
and conjoin the result with the length tests. -/
theorem polyTimeComputable_lamportVerFun (L : PolyExpr) :
    PolyTimeComputable (lamportVerFun L E) := by
  have hu := polyTimeComputable_pairFstD
  have hpk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hσ := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h₁ : PolyTimeComputable fun w =>
      [decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length)] := by
    convert polyTimeComputable_lenEq.comp (hm.pairEncode hu) using 1
    funext w
    simp [Function.comp_apply]
  have h₂ : PolyTimeComputable fun w =>
      [decide ((pairSndD (pairSndD (pairSndD w))).length =
        (pairFstD w).length * (pairFstD w).length)] := by
    convert polyTimeComputable_lenEq.comp
      (hσ.pairEncode ((polyTimeComputable_unaryPoly (.mul .var .var)).comp hu)) using 1
    funext w
    simp [Function.comp_apply]
  have hX := (blockEncFun_poly (polyTimeComputable_lamportEvalEmit hE) (.const 1) .var).comp
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (hm.pairEncode hσ)))
  have hY := (blockEncFun_poly polyTimeComputable_lamportPkEmit (.const 1)
    (lamportPkBlock L)).comp
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (hm.pairEncode hpk)))
  have h₃ : PolyTimeComputable fun w =>
      [decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
          (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
            (pairSndD (pairSndD (pairSndD w)))) =
        blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
          (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
            (pairFstD (pairSndD w))))] := by
    refine (polyTimeComputable_pairEq.comp (hX.pairEncode hY)).congr fun w => ?_
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    apply congrArg (fun b : Bool => [b])
    apply decide_eq_decide.mpr
    simp only [blockState_eq]
  exact polyTimeComputable_and (polyTimeComputable_and h₁ h₂) h₃

/-! ### The machines -/

/-- The machine `Gen`, with `2n²` coins. -/
noncomputable def lamportGen : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_lamportGenFun hE) (.mul (.mul (.const 2) .var) .var)

/-- The machine `Sign`, deterministic. -/
noncomputable def lamportSign : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_lamportSignFun (.const 0)

/-- `Gen` on coins `ρ`: `⟨pk, ρ⟩`, `pk` the tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the
`2n`-bit segments `x_i^0 ‖ x_i^1` of `ρ`. -/
theorem runAt_lamportGen (n : ℕ) (ρ : (lamportGen hE).Coins n) :
    (lamportGen hE).runAt n [] ρ =
      pairEncode (encodeList (List.ofFn fun i : Fin n =>
          pairEncode
            (E (pairEncode (List.replicate n true) (lamportHalf n false
              (coinBlock (2 * n) i (List.ofFn ρ)))))
            (E (pairEncode (List.replicate n true) (lamportHalf n true
              (coinBlock (2 * n) i (List.ofFn ρ)))))))
        (List.ofFn ρ) := by
  rw [NUPPT.runAt_eq]
  unfold lamportGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [lamportGenFun, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]
  rw [show blockState (List.replicate n true) [] (List.replicate n true) (List.ofFn ρ) =
    blockState (List.replicate n true) [] (List.ofFn fun _ : Fin n => true) (List.ofFn ρ) by simp,
    blockEncFun_ofFn]
  simp [lamportPairEmit, lamportHalf]

/-- `Sign` on `⟨sk, m⟩`: the concatenation of the halves `x_i^{m_i}` of the `2n`-bit segments
of `sk`. -/
theorem runAt_lamportSign (n : ℕ) (sk : List Bool) (m : Fin n → Bool)
    (r : lamportSign.Coins n) :
    lamportSign.runAt n (pairEncode sk (List.ofFn m)) r =
      (List.ofFn fun i : Fin n => lamportHalf n (m i) (coinBlock (2 * n) i sk)).flatten := by
  rw [NUPPT.runAt_eq]
  unfold lamportSign
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [lamportSignFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode,
    pairSndD_pairEncode]
  rw [blockEncFun_ofFn, decListFun_pairSndD]
  congr 1
  simp [lamportSelEmit, lamportHalf]

end Efficiency

/-! ### The scheme -/

variable (L : PolyExpr) (f : ∀ n, (Fin n → Bool) → (Fin (L.eval n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hfE : ∀ n (x : Fin n → Bool), E (NUPPT.advInput n (List.ofFn x)) = List.ofFn (f n x))

/-- **The one-way function of Protocol 137.1** as a function family: `n`-bit inputs and
`L(n)`-bit outputs at parameter `n`. -/
def lamportOWF : FunFamily where
  inLen := .var
  outLen := L
  f := f

/-- Lamport's function family has input-length polynomial `n`. -/
theorem lamportOWF_inLen : (lamportOWF L f).inLen = .var := rfl

/-- Lamport's function family retains the supplied output-length polynomial `L`. -/
theorem lamportOWF_outLen : (lamportOWF L f).outLen = L := rfl

/-- Lamport's function family retains the supplied family `f`. -/
theorem lamportOWF_f : (lamportOWF L f).f = f := rfl

include hfE in
/-- On `n`-bit inputs, `E` returns `L(n)` bits (it agrees with `f`). -/
theorem length_lamportEval {n : ℕ} {x : List Bool} (hx : x.length = n) :
    (E (pairEncode (List.replicate n true) x)).length = L.eval n := by
  have h := hfE n (padFin n x)
  have hx' := Collection.ofFn_padFin_of_le (le_of_eq hx)
  simp only [hx, Nat.sub_self, List.replicate_zero, List.append_nil] at hx'
  rw [hx'] at h
  simp only [NUPPT.advInput_eq] at h
  rw [h, List.length_ofFn]

include hfE in
/-- **Correctness**: `Ver` accepts `Sign`'s signature under the generated keys.

**Proof sketch.** `runAt_lamportGen` and `runAt_lamportSign` unfold the keys and the signature.
The length tests pass (`length_flatten_ofFn`). On both sides of `Ver`'s equality, the block loop
is a tuple over the message bits (`blockEncFun_ofFn`). Block `i` of the signature is
`x_i^{m_i}` (`coinBlock_flatten_ofFn`); block `i` of the public key is the pair
`⟨f(x_i^0), f(x_i^1)⟩`, of `6L + 6` bits (`length_lamportEval`). Both entries are `f(x_i^{m_i})`. -/
theorem lamportVerFun_sign (n : ℕ) (m : Fin n → Bool) (rg : (lamportGen hE).Coins n)
    (rs : lamportSign.Coins n) :
    lamportVerFun L E (atParam n (pairEncode (pairFstD ((lamportGen hE).runAt n [] rg))
      (pairEncode (List.ofFn m) (List.ofFn (padFin (n * n) (lamportSign.runAt n
        (pairEncode (pairSndD ((lamportGen hE).runAt n [] rg)) (List.ofFn m)) rs)))))) =
      [true] := by
  rw [runAt_lamportGen]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [runAt_lamportSign]
  have hρ : (List.ofFn rg).length = 2 * n * n := by
    refine (List.length_ofFn (f := rg)).trans
      (((lamportGen hE).coinLen_eq n).trans ?_)
    simp only [lamportGen, NUPPT.coins_ofPolyTimeUniform,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hseg : ∀ i : Fin n, (coinBlock (2 * n) i (List.ofFn rg)).length = 2 * n := by
    intro i
    apply length_coinBlock
    rw [hρ]
    have := i.isLt
    nlinarith
  have hsel : ∀ i : Fin n, (lamportHalf n (m i) (coinBlock (2 * n) i (List.ofFn rg))).length = n :=
    fun i => length_lamportHalf _ (hseg i)
  have hσ := length_flatten_ofFn _ hsel
  have hpad := Collection.ofFn_padFin_of_le (le_of_eq hσ)
  simp only [hσ, Nat.sub_self, List.replicate_zero, List.append_nil] at hpad
  rw [hpad]
  have hy : ∀ (b : Bool) (i : Fin n), (E (pairEncode (List.replicate n true)
      (lamportHalf n b (coinBlock (2 * n) i (List.ofFn rg))))).length = L.eval n :=
    fun b i => length_lamportEval L f E hfE (length_lamportHalf b (hseg i))
  have hpk : ∀ i : Fin n, (pairEncode (pairEncode
      (E (pairEncode (List.replicate n true) (lamportHalf n false
        (coinBlock (2 * n) i (List.ofFn rg)))))
      (E (pairEncode (List.replicate n true) (lamportHalf n true
        (coinBlock (2 * n) i (List.ofFn rg)))))) []).length =
      (lamportPkBlock L).eval n := by
    intro i
    simp only [length_pairEncode, hy, lamportPkBlock, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, List.length_nil]
    ring
  simp only [lamportVerFun, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_ofFn, hσ, decide_true, Bool.true_and, List.cons.injEq,
    and_true, decide_eq_true_eq]
  have hflat : ∀ g : Fin n → List Bool,
      encodeList (List.ofFn g) = (List.ofFn fun i => pairEncode (g i) []).flatten := by
    intro g
    rw [encodeList_eq_flatMap]
    simp [List.flatMap_def, List.map_ofFn, Function.comp_def]
  rw [hflat, blockEncFun_ofFn, blockEncFun_ofFn]
  congr 1
  congr 1
  funext i
  simp only [lamportEvalEmit, lamportPkEmit, NUPPT.inParam_layout, NUPPT.inCoins_layout,
    NUPPT.inArg_layout, pairSndD_pairEncode, List.headD_cons, PolyExpr.eval_var,
    List.length_replicate]
  rw [coinBlock_flatten_ofFn _ hsel i, coinBlock_flatten_ofFn _ hpk i]
  cases m i <;> simp [lamportHalf]

include hfE in
/-- **Lamport's one-time signature scheme** [PS10, Protocol 137.1] for `f` with evaluator `E`:
`n`-bit messages, `n²`-bit signatures. -/
noncomputable def lamport : SignatureScheme where
  msgLen := .var
  sigLen := .mul .var .var
  gen := lamportGen hE
  sign := lamportSign
  ver := lamportVerFun L E
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sign_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  ver_poly := polyTimeComputable_lamportVerFun hE L
  correct := fun n m rg rs => lamportVerFun_sign L f E hE hfE n m rg rs

/-- Lamport signs messages of length `n`. -/
theorem lamport_msgLen : (lamport L f E hE hfE).msgLen = .var := rfl

/-- Lamport's signature-length polynomial is `n²`. -/
theorem lamport_sigLen : (lamport L f E hE hfE).sigLen = .mul .var .var := rfl

/-- Lamport uses its preimage-pair generator as the scheme's key generator. -/
theorem lamport_gen : (lamport L f E hE hfE).gen = lamportGen hE := rfl

/-- Lamport uses its deterministic selected-preimage signer. -/
theorem lamport_sign : (lamport L f E hE hfE).sign = lamportSign := rfl

/-- Lamport uses its length-guarded block verifier. -/
theorem lamport_ver : (lamport L f E hE hfE).ver = lamportVerFun L E := rfl

/-- **Theorem 137.2: Lamport's scheme is one-time secure** [PS10, Theorem 137.2] when `f` is a
(strong) one-way function.

**Proof sketch** (the source's reduction, with its probability coupling explicit).
1. Fix a forger `A` making at most one signing query, and let `ε(n)` be its forgery probability.
   Work at `n ≥ 1`; the zero parameter is a finite exception for negligibility. The inverter
   `B` receives `1^n` and `y = f(x)` for a uniform `n`-bit `x`.
2. For the averaging argument, choose `i ← [n]` and a fair bit `c`, generate the other key
   entries, and put `y` at position `(i,c)`. Answer query `m` only when `m_i ≠ c`; otherwise
   abort, since the planted preimage is unknown. A valid forgery with `m'_i = c` reveals
   `σ'_i` with `f(σ'_i) = y`.
3. Couple this experiment to an honest execution, choosing `(i,c)` independently of that
   honest execution. The reduction agrees with it whenever it avoids revealing the planted
   preimage. For a successful honest run with query `m` and fresh forged message `m'`, the
   jointly favorable pairs satisfy `m_i ≠ c = m'_i`. Their fraction is
   `#{i : m_i ≠ m'_i}/(2n) ≥ 1/(2n)`. With no query, their fraction is exactly `1/2`.
   This counts the joint event without asserting independence after conditioning on non-abort.
4. Averaging over successful honest runs gives inversion probability at least `ε(n)/(2n)`.
   A best position at each length is at least as good as the uniform-position average; supply
   it as `O(log n)` bits of non-uniform advice and sample only the fair bit `c`. Thus the
   machine need not sample an exactly uniform element of `[n]` from a fixed finite coin tape.
5. `f` is one-way, so this lower bound is negligible, and polynomial-factor closure makes `ε`
   negligible. Apply T1 (`Games.exists_handlerMachine`) to the extended input `⟨y,i(n)⟩`, then
   `NUPPT.exists_withAdvice` supplies the bounded advised position. `advIn` builds the public
   key from that input and the seed, the handler answers or aborts, and `out` extracts `σ′_i`.

For zero-query successful runs the extraction fraction is `1/2`, rather than just `1/(2n)`. -/
theorem lamport_oneTimeSecure (hf : (lamportOWF L f).StrongOneWay) :
    (lamport L f E hE hfE).OneTimeSecure := by
  sorry

end TCSlib.Cryptography.Authentication
