/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the PRF reduction for the §3.9 scheme

The first step of [PS10, Theorem 168.2] replaces `f_k` by a random function: a reduction with
oracle access to a function `f` runs the IND adversary and answers its queries with `f` in place
of `f_k`. This file builds that reduction as a `Games.InteractiveHandler` (`pkHandler`) with one
outer oracle (the function), so that T2 (`Games.exists_interactiveHandlerMachine`) and T4
(`Games.exists_toOracleAdversary_of_bitCodec`) make it a next-query machine.

The handler's seed is `q(n)` nonce tapes of `n` bits (`pkTapes`), one per fresh nonce; its state
counts the tapes used and records the challenge (`pkState`).
- `Enc` on `m`: ask `f` at the next tape `r`, answer `⟨r, m ⊕ f(r)⟩`, count.
- `Dec` on `w`: when open (`atk = CCA1` and no challenge yet) and `w = ⟨x, v⟩` is well formed, ask
  `f` at `x` and answer `⟨1, v ⊕ f(x)⟩`; otherwise answer `⊥`.
- `Challenge` on `⟨m₀, m₁⟩`: the first time, ask `f` at the next tape `r`, answer
  `c = ⟨r, m_b ⊕ f(r)⟩`, record `c` and count; later repeat `c`.
The finalization asks nothing and outputs the adversary's bit.

## Main definitions

* `PRFGame.ctP`, `pkDin`, `pkDout`, `pkStLen`: the lengths.
* `PRFGame.recBits`, `pkState`: the encoded state.
* `PRFGame.pkTapes`: the seed as nonce tapes.
* `PRFGame.pkHandler q atkBit b`: the handler.

## Main results

* `PRFGame.pkHandler_impl_enc`, `_impl_dec_open`, `_impl_dec_closed`, `_impl_challenge_some`,
  `_impl_challenge_none`: its answers on encoded states.
* `PRFGame.pkHandler_finish`, `pkHandler_init_eq`: the finalization and the initial state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal B (dl-folds, cp1): a verbatim copy of `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean`, with every seal candidate of its
full TCSlib import closure (1268 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acSeedTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acStLen _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.expect_tapeImpl.match_1_4 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.extTape _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.simulate_tapeImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.tapeImpl _root_.TCSlib.Cryptography.Composability.Attack.ofNat _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_some_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_3 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_5 _root_.TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager.match_1_7 _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.length_of_firstQ_eq_some.match_1_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.ofPadded _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.PRFGame.ctOf _root_.TCSlib.Cryptography.Composability.PRFGame.decAns _root_.TCSlib.Cryptography.Composability.PRFGame.decWF _root_.TCSlib.Cryptography.Composability.PRFGame.eImpl _root_.TCSlib.Cryptography.Composability.PRFGame.eImpl.match_1 _root_.TCSlib.Cryptography.Composability.PRFGame.expect_eImpl.match_1_4 _root_.TCSlib.Cryptography.Composability.PRFGame.fImpl _root_.TCSlib.Cryptography.Composability.PRFGame.fImpl.match_1 _root_.TCSlib.Cryptography.Composability.PRFGame.fImpl.match_3 _root_.TCSlib.Cryptography.Composability.PRFGame.simulate_eImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.isPadded _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Composability.padDecFun _root_.TCSlib.Cryptography.Composability.padEncFun _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GGMRed.IsQ _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.advPoly _root_.TCSlib.Cryptography.GGMRed.adviceOf _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.ansMap _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinPoly _root_.TCSlib.Cryptography.GGMRed.coinStr _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.concrete _root_.TCSlib.Cryptography.GGMRed.concrete_iterate.match_1_1 _root_.TCSlib.Cryptography.GGMRed.encState _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.firstRound _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.nextQ _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.orbit_eq_encState.match_1_1 _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.prefMap _root_.TCSlib.Cryptography.GGMRed.pureAt _root_.TCSlib.Cryptography.GGMRed.pureStep _root_.TCSlib.Cryptography.GGMRed.pureStep.match_1 _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rawInput _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.stream _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.valStr _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.IInv _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom.match_1 _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.gB _root_.TCSlib.Cryptography.Games.EffFill.gC _root_.TCSlib.Cryptography.Games.EffFill.gCur _root_.TCSlib.Cryptography.Games.EffFill.gLc _root_.TCSlib.Cryptography.Games.EffFill.gLin _root_.TCSlib.Cryptography.Games.EffFill.gO _root_.TCSlib.Cryptography.Games.EffFill.gPh _root_.TCSlib.Cryptography.Games.EffFill.gS _root_.TCSlib.Cryptography.Games.EffFill.hAct _root_.TCSlib.Cryptography.Games.EffFill.hBound _root_.TCSlib.Cryptography.Games.EffFill.hCtx _root_.TCSlib.Cryptography.Games.EffFill.hMove _root_.TCSlib.Cryptography.Games.EffFill.hNext _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.hRes _root_.TCSlib.Cryptography.Games.EffFill.hRounds _root_.TCSlib.Cryptography.Games.EffFill.hStart _root_.TCSlib.Cryptography.Games.EffFill.hState _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iAnsLen _root_.TCSlib.Cryptography.Games.EffFill.iAsk _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallAct _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCallNext _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinAct _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinNext _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iFixBound _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iNext _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iTree _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_le_length_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.relabel _root_.TCSlib.Cryptography.Games.EffFill.relabelEmit _root_.TCSlib.Cryptography.Games.EffFill.relabelN _root_.TCSlib.Cryptography.Games.EffFill.relabelN_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.InteractiveHandler.rAns _root_.TCSlib.Cryptography.Games.InteractiveHandler.rCnt _root_.TCSlib.Cryptography.Games.InteractiveHandler.rI _root_.TCSlib.Cryptography.Games.InteractiveHandler.rL _root_.TCSlib.Cryptography.Games.InteractiveHandler.rS _root_.TCSlib.Cryptography.Games.InteractiveHandler.rU _root_.TCSlib.Cryptography.Games.InteractiveHandler.rW _root_.TCSlib.Cryptography.Games.InteractiveHandler.rX _root_.TCSlib.Cryptography.Games.InteractiveHandler.rZ _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.answer.match_1 _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.ansRead _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.buildComp_singleCodec.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.cntRead _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.singleCodec _root_.TCSlib.Cryptography.Games.singleCodec.match_1 _root_.TCSlib.Cryptography.Games.toHist _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PublicKeyScheme.Secure _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.PublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_prf_of_exists_prg.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmPRF _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.hybridAdv _root_.TCSlib.Cryptography.hybridCoins _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridPlant _root_.TCSlib.Cryptography.hybridPre _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.length_flatten_ofFn.match_1_1 _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multiDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.singleDist _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs

open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt)

/-! ### Lengths and states -/

/-- The ciphertext length `3n + 2`. -/
def ctP : PolyExpr := .add (.mul (.const 3) .var) (.const 2)

/-- `ctP.eval n = 3n + 2`. -/
theorem ctP_eval (n : ℕ) : ctP.eval n = 3 * n + 2 := by
  rw [ctP, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The query lengths: `n`-bit messages to `Enc`, `(3n + 2)`-bit ciphertexts to `Dec`, `2n`-bit
challenge queries. -/
def pkDin : Fin 3 → PolyExpr
  | 0 => .var
  | 1 => ctP
  | 2 => .add .var .var

/-- `Enc` queries have `n` bits: `pkDin 0 = var`. -/
theorem pkDin_zero : pkDin 0 = .var := rfl

/-- `Dec` queries have `3n + 2` bits: `pkDin 1 = ctP`. -/
theorem pkDin_one : pkDin 1 = ctP := rfl

/-- Challenge queries have `2n` bits: `pkDin 2 = var + var`. -/
theorem pkDin_two : pkDin 2 = .add .var .var := rfl

/-- The answer lengths: ciphertexts, `(n + 1)`-bit decryption answers, ciphertexts. -/
def pkDout : Fin 3 → PolyExpr
  | 0 => ctP
  | 1 => .add .var (.const 1)
  | 2 => ctP

/-- `Enc` answers are ciphertexts: `pkDout 0 = ctP`. -/
theorem pkDout_zero : pkDout 0 = ctP := rfl

/-- `Dec` answers have `n + 1` bits: `pkDout 1 = var + 1`. -/
theorem pkDout_one : pkDout 1 = .add .var (.const 1) := rfl

/-- Challenge answers are ciphertexts: `pkDout 2 = ctP`. -/
theorem pkDout_two : pkDout 2 = ctP := rfl

/-- The outer oracle: `n`-bit queries and answers. -/
abbrev pkOut : Fin 1 → PolyExpr := fun _ => .var

/-- `pkOut j = var`. -/
theorem pkOut_eq (j : Fin 1) : pkOut j = .var := rfl

variable (q : PolyExpr)

/-- The state length `2q + 3 + (3n + 2)`. -/
def pkStLen : PolyExpr := .add (.add (.mul (.const 2) q) (.const 3)) ctP

/-- `pkStLen q = 2q + 3 + ctP`. -/
theorem pkStLen_eq : pkStLen q = .add (.add (.mul (.const 2) q) (.const 3)) ctP := rfl

/-- The record of the challenge: `1 :: c` once recorded, `0^{1 + ct(n)}` before. -/
def recBits (n : ℕ) : Option (Fin (ctP.eval n) → Bool) → List Bool
  | none => false :: List.replicate (ctP.eval n) false
  | some c => true :: List.ofFn c

/-- `recBits n none = 0^{1 + ct(n)}`. -/
theorem recBits_none (n : ℕ) : recBits n none = false :: List.replicate (ctP.eval n) false := rfl

/-- `recBits n (some c) = 1 :: ⟦c⟧`. -/
theorem recBits_some (n : ℕ) (c : Fin (ctP.eval n) → Bool) :
    recBits n (some c) = true :: List.ofFn c := rfl

/-- The record has `1 + ct(n)` bits. -/
theorem length_recBits (n : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    (recBits n o).length = ctP.eval n + 1 := by
  cases o with
  | none => rw [recBits_none, List.length_cons, List.length_replicate]
  | some c => rw [recBits_some, List.length_cons, List.length_ofFn]

/-- **The encoded state** after `j` fresh nonces, with the challenge record `o`:
`⟨1^j, recBits o⟩`, padded with `false` to the state length. -/
def pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    Fin ((pkStLen q).eval n) → Bool :=
  padFin _ (pairEncode (List.replicate j true) (recBits n o))

/-- `pkState q n j o = padFin _ ⟨1^j, recBits n o⟩`. -/
theorem pkState_eq (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o)) :=
  rfl

/-- **The seed as nonce tapes:** `q(n) · n` bits as `q(n)` blocks of `n` bits. -/
def pkTapes (n : ℕ) : (Fin ((q.mul .var).eval n) → Bool) ≃ (Fin (q.eval n) → Fin n → Bool) :=
  (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
    (Equiv.refl Bool)).trans (EnsembleLemmas.blocks (q.eval n) n)

/-- **Bit `k` of tape `j` is bit `j·n + k` of the seed:**
`pkTapes q n ω j k = ω (finProdFinEquiv (j, k))`, read at the seed's length. -/
theorem pkTapes_apply (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : Fin (q.eval n))
    (k : Fin n) :
    pkTapes q n ω j k = ω (Fin.cast (by rw [PolyExpr.eval_mul, PolyExpr.eval_var])
      (finProdFinEquiv (j, k))) := by
  unfold pkTapes
  rw [Equiv.trans_apply, EnsembleLemmas.blocks_apply]
  rfl

/-- **Tape `j` is the `j`-th block of the seed:** `⟦pkTapes q n ω j⟧ = (⟦ω⟧.drop (j·n)).take n`.

**Proof sketch.** The width cast keeps the string (`ofFn_arrowCongr_finCongr`), and block `j` of
the seed is its `j`-th window (`EnsembleLemmas.blocks_eq`, `FunFamily.ofFn_blocks`). -/
theorem ofFn_pkTapes (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : Fin (q.eval n)) :
    List.ofFn (pkTapes q n ω j) = ((List.ofFn ω).drop (j * n)).take n := by
  unfold pkTapes
  rw [Equiv.trans_apply, EnsembleLemmas.blocks_eq, FunFamily.ofFn_blocks,
    ofFn_arrowCongr_finCongr]

/-! ### Strings -/

/-- The fields of an encoded state with `j ≤ q(n)`: the count `1^j`, the flag and the record. -/
private theorem fields_pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool))
    (hj : j ≤ q.eval n) :
    pairFstD (List.ofFn (pkState q n j o)) = List.replicate j true ∧
      (pairSndD (List.ofFn (pkState q n j o))).headD false = o.isSome ∧
      ((pairSndD (List.ofFn (pkState q n j o))).drop 1).take (ctP.eval n) =
        (recBits n o).drop 1 := by
  have hlen : (pairEncode (List.replicate j true) (recBits n o)).length ≤ (pkStLen q).eval n := by
    rw [length_pairEncode, List.length_replicate, length_recBits, pkStLen_eq, PolyExpr.eval_add,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const]
    omega
  rw [pkState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right]
  rw [pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨rfl, ?_, ?_⟩
  · cases o <;> rfl
  · cases o with
    | none =>
      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_replicate]
    | some c =>
      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_ofFn]

/-! ### The round function -/

/-- The challenge flag of the state. -/
private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
/-- The recorded challenge of the state. -/
private def rRec (w : List Bool) : List Bool :=
  ((pairSndD (rS w)).drop 1).take (ctP.eval (rU w).length)
/-- The outer answer recorded in the log `⟨⟨[], ⟨x, y⟩⟩, []⟩`. -/
private def rY (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
/-- Tape `j` of the seed. -/
private def rNonce (w : List Bool) : List Bool :=
  ((rW w).drop ((rCnt w).length * (rU w).length)).take (rU w).length
/-- The ciphertext `⟨r, m ⊕ y⟩` with the tape `r` and the outer answer `y`. -/
private def rCt (w m : List Bool) : List Bool :=
  pairEncode (rNonce w) (List.zipWith xor m (rY w))
/-- The selected challenge message `m_b`. -/
private def rMsg (b : Bool) (w : List Bool) : List Bool :=
  if b then (rX w).drop (rU w).length else (rX w).take (rU w).length
/-- Whether the decryption query `⟨x, v⟩` is well formed. -/
private def rWF (w : List Bool) : Bool :=
  decide ((pairFstD (rX w)).length = (rU w).length) &&
    decide ((pairSndD (rX w)).length = (rU w).length)
/-- The new state after a fresh nonce: count `j + 1`, record `t`. -/
private def rNew (w t : List Bool) : List Bool :=
  EnsembleLemmas.padL ((pkStLen q).eval (rU w).length) (pairEncode (true :: rCnt w) t)

/-- **One round of the handler** (see the module docstring), for the attack bit `atkBit` (`true`
for CCA1) and the challenge bit `b`. A first round asks the outer oracle; the second round, with
the answer `y` in the log, returns the answer and the new state. -/
private def pkRun (atkBit b : Bool) (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if ((rI w).drop 1).headD false then
      if rFlag w then pairEncode [true] (rRec w ++ rS w)
      else if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w))
      else pairEncode [true] (rCt w (rMsg b w) ++ rNew q w (true :: rCt w (rMsg b w)))
    else
      if atkBit && !rFlag w && rWF w then
        if decide (rL w = []) then pairEncode [false] (pairEncode [] (pairFstD (rX w)))
        else pairEncode [true] ((true :: List.zipWith xor (pairSndD (rX w)) (rY w)) ++ rS w)
      else pairEncode [true]
        (List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false ++ rS w)
  else
    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w))
    else pairEncode [true] (rCt w (rX w) ++ rNew q w (rFlag w :: rRec w))

/-- The round function is polynomial-time.

**Proof sketch.** Pair projections; the tape by `unaryMulPair`, `dropPrefixByLength` and
`pairTakePoly`; the exclusive-or by `pairXor`; the well-formedness test by `lenEq_poly`; the
padded new state by `padL`; and `polyTimeComputable_ite` for the cases. -/
private theorem polyTimeComputable_pkRun (atkBit b : Bool) :
    PolyTimeComputable (pkRun q atkBit b) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
  have hCnt : PolyTimeComputable rCnt := InteractiveHandler.polyTimeComputable_rCnt
  have hT : PolyTimeComputable fun w => pairSndD (rS w) := hD.comp hS
  have hFlag : PolyTimeComputable fun w => [rFlag w] := polyTimeComputable_headD.comp hT
  have hRec : PolyTimeComputable rRec :=
    ((polyTimeComputable_pairTakePoly ctP).comp
      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hY : PolyTimeComputable rY := hD.comp (hD.comp (hF.comp hL))
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((rCnt w).length * (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp (hCnt.pairEncode hU)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hDrop : PolyTimeComputable fun w => (rW w).drop ((rCnt w).length * (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hNonce : PolyTimeComputable rNonce :=
    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var]; rfl
  have hXor : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => List.zipWith xor (m w) (rY w) := fun hm =>
    (polyTimeComputable_pairXor.comp (hm.pairEncode hY)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hCt : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => rCt w (m w) := fun hm => hNonce.pairEncode (hXor hm)
  have hMsg : PolyTimeComputable (rMsg b) :=
    polyTimeComputable_ite (polyTimeComputable_const [b])
      (((polyTimeComputable_pairDropPoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
      (((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
  have hWF : PolyTimeComputable fun w => [rWF w] :=
    polyTimeComputable_and (EffFill.lenEq_poly (hF.comp hX) hU)
      (EffFill.lenEq_poly (hD.comp hX) hU)
  have hNew : ∀ {t : List Bool → List Bool}, PolyTimeComputable t →
      PolyTimeComputable fun w => rNew q w (t w) := fun ht =>
    EnsembleLemmas.polyTimeComputable_padL (pkStLen q) hU
      (((polyTimeComputable_const [true]).append hCnt).pairEncode ht)
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have hQry : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [false] (pairEncode [] (f w)) := fun hf =>
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hf)
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have cOpen : PolyTimeComputable fun w => [atkBit && !rFlag w && rWF w] :=
    polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_const [atkBit])
      (polyTimeComputable_not hFlag)) hWF
  have hZeros : PolyTimeComputable fun w =>
      List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false :=
    EnsembleLemmas.polyTimeComputable_zeros _ hU
  have hChal := polyTimeComputable_ite hFlag (hRet (hRec.append hS))
    (polyTimeComputable_ite cNil (hQry hNonce)
      (hRet ((hCt hMsg).append (hNew ((polyTimeComputable_const [true]).append (hCt hMsg))))))
  have hDec := polyTimeComputable_ite cOpen
    (polyTimeComputable_ite cNil (hQry (hF.comp hX))
      (hRet (((polyTimeComputable_const [true]).append (hXor (hD.comp hX))).append hS)))
    (hRet (hZeros.append hS))
  have hKeep : PolyTimeComputable fun w => rFlag w :: rRec w :=
    (hFlag.append hRec).congr fun _ => rfl
  have hEnc := polyTimeComputable_ite cNil (hQry hNonce) (hRet ((hCt hX).append (hNew hKeep)))
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
      hChal hDec) hEnc

/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
private def pkFin (w : List Bool) : List Bool :=
  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_pkFin : PolyTimeComputable pkFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the PRF reduction** for the budget `q`, the attack bit `atkBit` (`true` for
CCA1, `false` for CPA) and the challenge bit `b`: state `pkState j o` (initially `j = 0` and no
record), seed `q · n` bits (the tapes `pkTapes`), one outer call per inner query, the adversary
run on the reduction input (ignored), and the finalization outputting the adversary's bit. -/
noncomputable def pkHandler (atkBit b : Bool) :
    InteractiveHandler 3 pkDin pkDout 1 pkOut pkOut where
  stateLen := pkStLen q
  seedLen := q.mul .var
  perCall := .const 1
  init n := pkState q n 0 none
  run := pkRun q atkBit b
  poly := polyTimeComputable_pkRun q atkBit b
  advIn ctx := pairFstD (pairSndD ctx)
  advIn_poly := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  outLen := .const 1
  finCall := .const 0
  finRun := pkFin
  finRun_poly := polyTimeComputable_pkFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init outLen finCall]
  pkHandler

/-- The handler's initial state is the empty count and no record:
`(pkHandler q atkBit b).init n = pkState q n 0 none`. -/
theorem pkHandler_init_eq (atkBit b : Bool) (n : ℕ) :
    (pkHandler q atkBit b).init n = pkState q n 0 none :=
  rfl

/-- The handler's seed as nonce tapes (`pkTapes`), at the handler's seed type. -/
def pkSeedTapes (atkBit b : Bool) (n : ℕ) :
    (Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool) ≃ (Fin (q.eval n) → Fin n → Bool) :=
  pkTapes q n

/-- The encoded state at the handler's state type: `pkHState q atkBit b n j o = pkState q n j o`. -/
def pkHState (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool :=
  pkState q n j o

/-- `pkHState q atkBit b n j o = pkState q n j o`. -/
theorem pkHState_eq (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkHState q atkBit b n j o = pkState q n j o :=
  rfl

/-- The initial state is the encoded `(0, none)`: `(pkHandler q atkBit b).init n =
pkHState q atkBit b n 0 none`. -/
theorem pkHandler_init_hstate (atkBit b : Bool) (n : ℕ) :
    (pkHandler q atkBit b).init n = pkHState q atkBit b n 0 none :=
  rfl

/-- `pkSeedTapes q atkBit b n = pkTapes q n`. -/
theorem pkSeedTapes_eq (atkBit b : Bool) (n : ℕ) : pkSeedTapes q atkBit b n = pkTapes q n :=
  rfl

/-- The finalization outputs the adversary's bit and asks nothing:
`(pkHandler q atkBit b).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem pkHandler_finish (atkBit b : Bool) (n : ℕ) (z : List Bool)
    (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)
    (s : Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool)
    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (pkHandler q atkBit b).finish n z ω s a =
      .pure (padFin ((pkHandler q atkBit b).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  have h0 : (pkHandler q atkBit b).finCall.eval n = 0 := by
    rw [pkHandler_finCall, PolyExpr.eval_const]
  rw [h0]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (pkFin _) = _
  rw [pkFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((pkHandler q atkBit b).outLen.eval n) (List.ofFn a)) =
      List.ofFn a :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

section Answers

variable (atkBit b : Bool) (n : ℕ) (z : List Bool)
  (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)

/-- The round input of a call, field by field, on an encoded state with `j ≤ q(n)`. -/
private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n) :
    let w := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L
    rU w = List.replicate n true ∧ rW w = List.ofFn ω ∧
      rS w = List.ofFn (pkState q n j o) ∧ rI w = List.replicate i true ∧ rX w = x ∧
      rL w = L ∧ rCnt w = List.replicate j true ∧ rFlag w = o.isSome ∧
      rRec w = (recBits n o).drop 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := fields_pkState q n j o hj
  simp only [InteractiveHandler.rU_input, InteractiveHandler.rW_input, InteractiveHandler.rS_input,
    InteractiveHandler.rI_input, InteractiveHandler.rX_input, InteractiveHandler.rL_input,
    InteractiveHandler.rCnt_input, rFlag, rRec, List.length_replicate, h₁, h₂, h₃, and_self]

/-- The tape at the count `j < q(n)` is the `j`-th block of the seed. -/
private theorem rNonce_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j < q.eval n) :
    rNonce (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) := by
  obtain ⟨hU, hW, -, -, -, -, hCnt, -, -⟩ := fields_input q atkBit b n z ω (i := i) x L j o hj.le
  rw [rNonce, hU, hW, hCnt, List.length_replicate, List.length_replicate, pkSeedTapes_eq]
  exact (ofFn_pkTapes q n ω ⟨j, hj⟩).symm

/-- The new state after a fresh nonce from `pkState j o`, with record `t`. -/
private theorem rNew_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o o' : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n) :
    rNew q (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L)
        (recBits n o') = List.ofFn (pkState q n (j + 1) o') := by
  obtain ⟨hU, -, -, -, -, -, hCnt, -, -⟩ := fields_input q atkBit b n z ω (i := i) x L j o hj
  rw [rNew, hU, hCnt, List.length_replicate, pkState_eq, EnsembleLemmas.ofFn_padFin_eq_padL,
    List.replicate_succ]

/-- The flag and the record rebuild the record bits: `rFlag :: rRec = recBits o`. -/
private theorem recBits_fields (o : Option (Fin (ctP.eval n) → Bool)) :
    o.isSome :: (recBits n o).drop 1 = recBits n o := by
  cases o <;> rfl

/-- The outer answer recorded in a one-entry log. -/
private theorem rY_one (w : List Bool) (x' y : List Bool)
    (hL : rL w = pairEncode (pairEncode [] (pairEncode x' y)) []) : rY w = y := by
  rw [rY, hL, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

/-- The index word of oracle `2`. -/
private theorem replicate_two : List.replicate ((2 : Fin 3) : ℕ) true = [true, true] := rfl

/-- The index word of oracle `0`. -/
private theorem replicate_zero' : List.replicate ((0 : Fin 3) : ℕ) true = [] := rfl

/-- A one-entry log is not empty. -/
private theorem log_ne_nil (x' y : List Bool) :
    decide (pairEncode (pairEncode [] (pairEncode x' y)) [] = []) = false :=
  decide_eq_false (pairEncode_ne_nil _ _)

/-- **Encryption with the next tape:** from `pkState j o` with `j < q(n)`, the query `m` asks the
outer oracle at the tape `r = T_j`, and its answer `y` gives the ciphertext `⟨r, m ⊕ y⟩` and the
state `pkState (j + 1) o`.

**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
empty log, asks the outer oracle at the tape `T_j` (`rNonce_fields`); the second, with the answer
`y` in the log (`rY_one`), returns `⟨T_j, m ⊕ y⟩` and the state with count `j + 1`
(`rNew_fields`); `InteractiveHandler.impl_of_query` assembles the two rounds. -/
theorem pkHandler_impl_enc (x : Fin ((pkDin 0).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j < q.eval n) :
    (pkHandler q atkBit b).impl n z ω 0 x (pkState q n j o) =
      .query 0 (padFin _ (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) fun y =>
        .pure (padFin _ (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (List.ofFn x)
          (padFin n (List.ofFn y))), pkState q n (j + 1) o) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hT : List.ofFn (padFin ((pkOut 0).eval n)
      (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
  refine InteractiveHandler.impl_of_query _ n z ω x _ 0 _ _ _
    (by rw [pkHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show pkRun q atkBit b _ = _
    obtain ⟨-, -, -, hI, -, hL, -, -, -⟩ :=
      fields_input q atkBit b n z ω (i := 0) (List.ofFn x) [] j o hj.le
    rw [pkRun, hI, hL, hT, rNonce_fields q atkBit b n z ω (i := 0) _ _ j o hj]
    rfl
  · intro y
    show pkRun q atkBit b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨-, -, -, hI, hX, hL, -, hFlag, hRec⟩ :=
      fields_input q atkBit b n z ω (i := 0) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j o hj.le
    have hY := rY_one _ _ _ hL
    have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
      ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
    have hct : List.ofFn (padFin ((pkDout 0).eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (List.ofFn x) (padFin n (List.ofFn y)))) =
        ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (List.ofFn x) (padFin n (List.ofFn y)) :=
      ofFn_padFin_of_length (by
        rw [length_ctOf _ (by rw [List.length_ofFn, pkDin_zero, PolyExpr.eval_var]), pkDout_zero,
          ctP_eval])
    rw [pkRun, hI, replicate_zero', List.headD_nil, if_neg Bool.false_ne_true, hL, log_ne_nil,
      if_neg Bool.false_ne_true, hct, rCt, rNonce_fields q atkBit b n z ω (i := 0) _ _ j o hj,
      hX, hY, hFlag, hRec, recBits_fields, rNew_fields q atkBit b n z ω (i := 0) _ _ j o o hj.le,
      ctOf_eq, hy]

/-- **Open decryption:** if the oracle is open (`atkBit`, no record) and `w = ⟦x⟧ = ⟨x₀, v⟩` is
well formed, the query asks the outer oracle at `x₀`, and its answer `y` gives `⟨1, v ⊕ y⟩`; the
state is kept.

**Proof sketch.** As for `pkHandler_impl_enc`: the open test reads `atkBit`, the flag and the
well-formedness of `⟦x⟧` (`fields_input`); the first round asks the outer oracle at `x₀`, the second
returns `⟨1, v ⊕ y⟩` with the state unchanged (`InteractiveHandler.impl_of_query`). -/
theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n)
    (hop : (atkBit && !o.isSome && decWF n (List.ofFn x)) = true) :
    (pkHandler q atkBit b).impl n z ω 1 x (pkState q n j o) =
      .query 0 (padFin _ (pairFstD (List.ofFn x))) fun y =>
        .pure (padFin _ (true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y)),
          pkState q n j o) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hwf : decWF n (List.ofFn x) = true := by
    simp only [Bool.and_eq_true] at hop
    exact hop.2
  rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf
  have hx0 : List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x))) =
      pairFstD (List.ofFn x) := ofFn_padFin_of_length (by rw [hwf.1, hn])
  have hc : ((1 : Fin 3) : ℕ) = 1 := rfl
  refine InteractiveHandler.impl_of_query _ n z ω x _ 0 _ _ _
    (by rw [pkHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show pkRun q atkBit b _ = _
    obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
    have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
        (1 : Fin 3)
        (List.ofFn x) []) = decWF n (List.ofFn x) := by
      rw [rWF, hU, hX, List.length_replicate, decWF_eq]
    rw [pkRun, hI, Fin.val_one, List.replicate_one, hFlag, hWF, hop, hL, hX, hx0]
    rfl
  · intro y
    show pkRun q atkBit b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨hU, -, hS, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 1) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (pairFstD (List.ofFn x)))) (List.ofFn y))) []) j o hj
    have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
        (1 : Fin 3)
        (List.ofFn x) (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (pairFstD (List.ofFn x)))) (List.ofFn y))) [])) = decWF n (List.ofFn x) := by
      rw [rWF, hU, hX, List.length_replicate, decWF_eq]
    have hY := rY_one _ _ _ hL
    have hans : List.ofFn (padFin ((pkDout 1).eval n)
        (true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y))) =
        true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y) :=
      ofFn_padFin_of_length (by
        rw [List.length_cons, List.length_zipWith, List.length_ofFn, hwf.2, hn, Nat.min_self,
          pkDout_one, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const])
    rw [pkRun, hI, Fin.val_one, List.replicate_one, hFlag, hWF, hop, hL, log_ne_nil,
      if_neg Bool.false_ne_true, hans, hS, hX, hY]
    rfl

/-- **Closed decryption:** if the oracle is closed (CPA, or a record exists) or the query is not
well formed, the answer is `⊥` (all-`false`) and the state is kept. -/
theorem pkHandler_impl_dec_closed (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n)
    (hcl : (atkBit && !o.isSome && decWF n (List.ofFn x)) = false) :
    (pkHandler q atkBit b).impl n z ω 1 x (pkState q n j o)
        = .pure (zeroBits _, pkState q n j o) := by
  refine InteractiveHandler.impl_of_ret _ n z ω x _ _ _ ?_
  show pkRun q atkBit b _ = _
  obtain ⟨hU, -, hS, hI, hX, -, -, hFlag, -⟩ :=
    fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
  have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
      (1 : Fin 3)
      (List.ofFn x) []) = decWF n (List.ofFn x) := by
    rw [rWF, hU, hX, List.length_replicate, decWF_eq]
  rw [pkRun, hI, Fin.val_one, List.replicate_one, hFlag, hWF, hcl, hU, hS, List.length_replicate,
    ofFn_zeroBits, pkDout_one]
  rfl

/-- **A recorded challenge is repeated:** from `pkState j (some c)`, a challenge is answered `c` and
the state is kept. -/
theorem pkHandler_impl_challenge_some (x : Fin ((pkDin 2).eval n) → Bool) (j : ℕ)
    (c : Fin (ctP.eval n) → Bool) (hj : j ≤ q.eval n) :
    (pkHandler q atkBit b).impl n z ω 2 x (pkState q n j (some c)) =
      .pure (padFin _ (List.ofFn c), pkState q n j (some c)) := by
  refine InteractiveHandler.impl_of_ret _ n z ω x _ _ _ ?_
  show pkRun q atkBit b _ = _
  obtain ⟨-, -, hS, hI, -, -, -, hFlag, hRec⟩ :=
    fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j (some c) hj
  have hc : List.ofFn (padFin ((pkDout 2).eval n) (List.ofFn c)) = List.ofFn c :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, pkDout_two])
  rw [pkRun, hI, replicate_two, hFlag, hRec, hS, hc]
  rfl

/-- **The first challenge with the next tape:** from `pkState j none` with `j < q(n)`, the
challenge `⟨m₀, m₁⟩` asks the outer oracle at the tape `r = T_j`, and its answer `y` gives the
ciphertext `c = ⟨r, m_b ⊕ y⟩`, recorded in the state `pkState (j + 1) (some c)`.

**Proof sketch.** As for `pkHandler_impl_enc`, with the selected half `m_b` (`rMsg`, `msgOf_eq`)
and the new record `recBits (some c)` written into the state (`rNew_fields`). -/
theorem pkHandler_impl_challenge_none (x : Fin ((pkDin 2).eval n) → Bool) (j : ℕ)
    (hj : j < q.eval n) :
    (pkHandler q atkBit b).impl n z ω 2 x (pkState q n j none) =
      .query 0 (padFin _ (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) fun y =>
        .pure (padFin _ (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
            (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y))),
          pkState q n (j + 1) (some (padFin (ctP.eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
            (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)))))) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hT : List.ofFn (padFin ((pkOut 0).eval n)
      (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
  have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
    have hx : (List.ofFn x).length = n + n := by
      rw [List.length_ofFn, pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
    rw [AdaptiveCPA.msgOf_eq]
    cases b <;> simp [hx]
  refine InteractiveHandler.impl_of_query _ n z ω x _ 0 _ _ _
    (by rw [pkHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show pkRun q atkBit b _ = _
    obtain ⟨-, -, -, hI, -, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j none hj.le
    rw [pkRun, hI, replicate_two, hFlag, hL, hT,
      rNonce_fields q atkBit b n z ω (i := 2) _ _ j none hj]
    rfl
  · intro y
    show pkRun q atkBit b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 2) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j none hj.le
    have hY := rY_one _ _ _ hL
    have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
      ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
    have hlen : (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
        (padFin n (List.ofFn y))).length = ctP.eval n := by
      rw [length_ctOf _ hmsg, ctP_eval]
    have hct : List.ofFn (padFin ((pkDout 2).eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)))) =
        ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
          (padFin n (List.ofFn y)) :=
      ofFn_padFin_of_length (by rw [hlen, pkDout_two])
    have hrec : true :: ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)) =
        recBits n (some (padFin (ctP.eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
          (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y))))) := by
      rw [recBits_some, ofFn_padFin_of_length hlen]
    have hMsg : rMsg b (InteractiveHandler.input n z (List.ofFn ω)
        (List.ofFn (pkState q n j none)) (2 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) [])) =
        AdaptiveCPA.msgOf n b (List.ofFn x) := by
      rw [rMsg, hU, hX, List.length_replicate, AdaptiveCPA.msgOf_eq]
    have hctOf : ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
        (padFin n (List.ofFn y)) = pairEncode (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))
          (List.zipWith xor (AdaptiveCPA.msgOf n b (List.ofFn x)) (List.ofFn y)) := by
      rw [ctOf_eq, hy]
    rw [pkRun, hI, replicate_two]
    simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero, if_true]
    rw [hFlag, hL, log_ne_nil]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    rw [hMsg, hct, rCt, rNonce_fields q atkBit b n z ω (i := 2) _ _ j none hj, hY, ← hctOf, hrec,
      rNew_fields q atkBit b n z ω (i := 2) _ _ j none _ hj.le]

end Answers

end TCSlib.Cryptography.Composability.PRFGame
