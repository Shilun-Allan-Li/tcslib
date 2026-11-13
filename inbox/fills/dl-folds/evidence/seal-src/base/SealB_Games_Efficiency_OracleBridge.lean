/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one-oracle `bitCodec` machines to next-query machines (efficiency fill, T4)

The translators behind `Games.exists_toOracleAdversary_of_bitCodec` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T4"). A machine `B` against one
`bitCodec` oracle with a one-bit output reads `⟨[], log⟩` and writes `bitCodec` moves; a
next-query machine of the ch. 2–4 layer reads a history (`encodeHist`) and writes
`decodeOracleMove` moves. Two polynomial-time maps translate:
- `bridgePre` turns the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` into `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`,
  the empty input followed by the `bitCodec` log (the index of the only oracle is `1^0 = []`);
- `bridgePost` turns a canonical query word `⟨[false], ⟨[], x⟩⟩` into `⟨[false], x⟩`, the word
  `⟨[true], [true]⟩` into the verdict `[true, true]`, and every other word into `[true, false]`.

Both decoders check the payload length `ℓ₁(n)` themselves and agree on it, so neither map
needs the parameter.

## Main definitions

* `EffFill.relabelEmit`, `EffFill.relabel`, `EffFill.bridgePre`, `EffFill.bridgePost`.

## Main results

* `EffFill.bridgePre_encodeHist`: the history of a log translates to the log.
* `EffFill.bridgePost_spec`: the translated move is the decoded move.
* `EffFill.eval_buildTree_bridge`: the two computations evaluate alike against every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 96.1 (oracle indistinguishability against oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

/-! Seal B (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean`, with every seal candidate of its
full TCSlib import closure (595 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.encodeNat _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ### The history translator -/

/-- The piece emitted for the suffix `w` of an encoded history: `⟨⟨[], fst w⟩, []⟩` for a
non-empty suffix, nothing for the empty one. -/
def relabelEmit (w : List Bool) : List Bool :=
  if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) []

/-- `relabelEmit w = if w = [] then [] else ⟨⟨[], fst w⟩, []⟩`. -/
theorem relabelEmit_eq (w : List Bool) :
    relabelEmit w = if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) [] :=
  rfl

/-- The pieces of the first `m` suffixes `w, snd w, snd (snd w), …`, concatenated. -/
def relabelN (m : ℕ) (w : List Bool) : List Bool :=
  (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w)

/-- `relabelN m w = ⋃_{i < m} relabelEmit (snd^i w)`. -/
theorem relabelN_eq (m : ℕ) (w : List Bool) :
    relabelN m w = (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w) :=
  rfl

/-- **The history translator's body:** the pieces of the first `|x| + 1` suffixes of `x`. -/
def relabel (x : List Bool) : List Bool := relabelN (x.length + 1) x

/-- `relabel x = relabelN (|x| + 1) x`. -/
theorem relabel_eq (x : List Bool) : relabel x = relabelN (x.length + 1) x := rfl

/-- **The history translator:** `bridgePre x = ⟨[], relabel x⟩`. -/
def bridgePre (x : List Bool) : List Bool := pairEncode [] (relabel x)

/-- `bridgePre x = ⟨[], relabel x⟩`. -/
theorem bridgePre_eq (x : List Bool) : bridgePre x = pairEncode [] (relabel x) := rfl

/-- The empty word has no pieces: `relabelN m [] = []`. -/
theorem relabelN_nil (m : ℕ) : relabelN m [] = [] := by
  rw [relabelN_eq, List.flatMap_eq_nil_iff]
  intro i _
  have h : ∀ j, pairSndD^[j] ([] : List Bool) = [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      exact pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil
  rw [h, relabelEmit_eq, if_pos rfl]

/-- One more suffix: `relabelN (m + 1) w = relabelEmit w ++ relabelN m (snd w)`. -/
theorem relabelN_succ (m : ℕ) (w : List Bool) :
    relabelN (m + 1) w = relabelEmit w ++ relabelN m (pairSndD w) := by
  rw [relabelN_eq, relabelN_eq, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rfl

/-- The history of a one-oracle `bitCodec` log, as (query, answer) pairs. -/
def logHist {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  L.map fun e => (e.2.1, e.2.2)

/-- `logHist L` maps each entry `⟨0, x, y⟩` to `(x, y)`. -/
theorem logHist_eq {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    logHist L = L.map fun e => (e.2.1, e.2.2) :=
  rfl

/-- **The pieces of an encoded history form the `bitCodec` log:** for every `m ≥ |L|`,
`relabelN m (encodeHist (logHist L)) = encodeLog L`.

**Proof sketch.** Induction on `L`. The empty history is `[]`, which has no pieces
(`relabelN_nil`). A non-empty history `⟨⟨x, y⟩, rest⟩` emits `⟨⟨[], ⟨x, y⟩⟩, []⟩` and continues
with `rest` (`relabelN_succ`, `encodeHist_cons`); the piece is the entry's `bitCodec` encoding
(`bitCodec_encodeEntry`, the index of the only oracle being `1^0 = []`), and the concatenation is
the nested pair (`GGMRed.pairEncode_append_right`, `encodeLog_cons`). -/
theorem relabelN_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ) :
    ∀ (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) (m : ℕ), L.length ≤ m →
      relabelN m (encodeHist (logHist L)) =
        (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L
  | [], m, _ => by
    rw [logHist_eq, List.map_nil, encodeHist_nil, relabelN_nil, MachineCodec.encodeLog_nil]
  | e :: L, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [logHist_eq, List.map_cons, ← logHist_eq, encodeHist_cons, relabelN_succ,
      pairSndD_pairEncode, relabelN_encodeHist dα L m (by rw [List.length_cons] at hm; omega),
      relabelEmit_eq, if_neg (pairEncode_ne_nil _ _), pairFstD_pairEncode,
      MachineCodec.encodeLog_cons, bitCodec_encodeEntry, ← GGMRed.pairEncode_append_right,
      List.nil_append, Fin.fin_one_eq_zero e.1, Fin.val_zero, List.replicate_zero]

/-- An encoded history has at least as many bits as entries. -/
theorem length_le_length_encodeHist {ℓ₁ ℓ₂ : ℕ} :
    ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)), h.length ≤ (encodeHist h).length
  | [] => Nat.zero_le _
  | p :: h => by
    rw [encodeHist_cons, length_pairEncode, List.length_cons]
    have := length_le_length_encodeHist h
    omega

/-- **The history translator on a history:** `bridgePre (encodeHist (logHist L)) =
⟨[], encodeLog L⟩`. -/
theorem bridgePre_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    bridgePre (encodeHist (logHist L)) =
      pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L) := by
  rw [bridgePre_eq, relabel_eq, relabelN_encodeHist dα L _]
  have h1 := length_le_length_encodeHist (logHist L)
  rw [logHist_eq, List.length_map] at h1
  rw [logHist_eq]
  omega

/-- The emitted piece is polynomial-time. -/
theorem relabelEmit_poly : PolyTimeComputable relabelEmit :=
  (polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (((polyTimeComputable_const []).pairEncode polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_const []))).congr fun w => by
    rw [relabelEmit_eq]
    by_cases h : w = []
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]
      rfl

/-- **The history translator is polynomial-time** (`Complexity.polyTimeComputable_iterateEmit`
with the step `pairSndD`, `|x| + 1` rounds and the orbit bound `|x|`). -/
theorem bridgePre_poly : PolyTimeComputable bridgePre := by
  have horbit : ∀ (x : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval x.length →
      (pairSndD^[i] x).length ≤ PolyExpr.var.eval x.length := by
    intro x i _
    clear * -
    rw [PolyExpr.eval_var]
    induction i with
    | zero => exact le_rfl
    | succ i ih => rw [Function.iterate_succ_apply']; exact (length_pairSndD_le _).trans ih
  have h := polyTimeComputable_iterateEmit polyTimeComputable_pairSndD relabelEmit_poly .var .var
    horbit
  refine ((polyTimeComputable_const []).pairEncode h).congr fun x => ?_
  rw [bridgePre_eq, relabel_eq, relabelN_eq, PolyExpr.eval_var]

/-! ### The move translator -/

/-- **The move translator:** a canonical query word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`,
the output word `⟨[true], [true]⟩` becomes `[true, true]`, and every other word `[true, false]`. -/
def bridgePost (w : List Bool) : List Bool :=
  if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
    pairEncode [false] (pairSndD (pairSndD w))
  else if w = pairEncode [true] [true] then [true, true] else [true, false]

/-- The defining equation of `bridgePost`. -/
theorem bridgePost_eq (w : List Bool) :
    bridgePost w =
      if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
        pairEncode [false] (pairSndD (pairSndD w))
      else if w = pairEncode [true] [true] then [true, true] else [true, false] :=
  rfl

/-- **The move translator is polynomial-time** (`eq_poly` for the two tests). -/
theorem bridgePost_poly : PolyTimeComputable bridgePost := by
  have hx := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have h1 := eq_poly polyTimeComputable_id ((polyTimeComputable_const [false]).pairEncode
    ((polyTimeComputable_const []).pairEncode hx))
  have h2 := eq_poly polyTimeComputable_id (polyTimeComputable_const (pairEncode [true] [true]))
  refine (polyTimeComputable_ite h1 ((polyTimeComputable_const [false]).pairEncode hx)
    (polyTimeComputable_ite h2 (polyTimeComputable_const [true, true])
      (polyTimeComputable_const [true, false]))).congr fun w => ?_
  rw [bridgePost_eq]
  simp only [id_eq, decide_eq_true_eq]

/-- **The translated move is the decoded move.** For every word `w`, either `decodeBitMove`
reads the query `x` (to the only oracle) and `decodeOracleMove` reads the query `x` off
`bridgePost w`, or `decodeBitMove` reads an output `a` and `decodeOracleMove` the verdict `a 0`.

**Proof sketch.** Three cases on `w`. A word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`: if
`|x| = ℓ₁` both decoders read the query (`decodeBitMove_query`,
`decodeOracleMove_pairEncode_ofFn`); otherwise both read the default, the all-`false` output and
the verdict `false` (`decodeBitMove_of_not_canonical`,
`decodeOracleMove_pairEncode_false_of_length_ne`). The word `⟨[true], [true]⟩` reads the output
`1` on both sides (`decodeBitMove_ret`, `decodeOracleMove_true_two`). Every other word becomes
`[true, false]`, the verdict `false`; `decodeBitMove` reads either the output `0` (the word
`⟨[true], [false]⟩`) or the default (`decodeBitMove_of_not_canonical`); its query words are all
of the first form, since `1^i = []` for `i : Fin 1`. -/
theorem bridgePost_spec (ℓ₁ ℓ₂ : ℕ) (w : List Bool) :
    (∃ x : Fin ℓ₁ → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .query 0 x ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .query x) ∨
    (∃ a : Fin 1 → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .ret a ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .ret (a 0)) := by
  by_cases hq : w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w)))
  · rw [bridgePost_eq, if_pos hq]
    set xw := pairSndD (pairSndD w)
    by_cases hx : xw.length = ℓ₁
    · obtain ⟨x, hxe⟩ := exists_ofFn_eq hx
      refine Or.inl ⟨x, ?_, ?_⟩
      · rw [hq, ← hxe]
        exact decodeBitMove_query (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 0 x
      · rw [← hxe]
        exact decodeOracleMove_pairEncode_ofFn ℓ₁ x
    · refine Or.inr ⟨zeroBits 1, ?_, ?_⟩
      · refine decodeBitMove_of_not_canonical (fun i x h => hx ?_) (fun a h => ?_)
        · rw [hq, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero] at h
          have h' := congrArg (fun v => pairSndD (pairSndD v)) h
          simp only [pairSndD_pairEncode] at h'
          rw [h', List.length_ofFn]
        · rw [hq] at h
          have h' := congrArg pairFstD h
          simp only [pairFstD_pairEncode] at h'
          exact absurd h' (by decide)
      · rw [decodeOracleMove_pairEncode_false_of_length_ne ℓ₁ hx, zeroBits_apply]
  · by_cases hr : w = pairEncode [true] [true]
    · refine Or.inr ⟨fun _ => true, ?_, ?_⟩
      · rw [hr]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => true)
      · rw [bridgePost_eq, if_neg hq, if_pos hr]
        exact decodeOracleMove_true_two ℓ₁ true
    · rw [bridgePost_eq, if_neg hq, if_neg hr, decodeOracleMove_true_two]
      by_cases hf : w = pairEncode [true] [false]
      · refine Or.inr ⟨fun _ => false, ?_, rfl⟩
        rw [hf]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => false)
      · refine Or.inr ⟨zeroBits 1, ?_, by rw [zeroBits_apply]⟩
        refine decodeBitMove_of_not_canonical (fun i x h => hq ?_) (fun a h => ?_)
        · rw [h, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero, pairSndD_pairEncode,
            pairSndD_pairEncode]
        · have ha : List.ofFn a = [a 0] := by rw [List.ofFn_succ, List.ofFn_zero]
          rw [ha] at h
          cases h0 : a 0
          · rw [h0] at h; exact hf h
          · rw [h0] at h; exact hr h

/-! ### Evaluation -/

/-- **The two computations evaluate alike.** For a string function `D` (a machine with fixed coins),
the ch. 2–4 tree of the next-move function `h ↦ decodeOracleMove ℓ₁ (bridgePost (D (bridgePre
(encodeHist h))))` from the history of a log `L`, evaluated against `f`, is bit `0` of the
`bitCodec` computation of `L ↦ decodeBitMove (D ⟨[], encodeLog L⟩)` from `L`, evaluated against
`f` at the only oracle; for every budget.

**Proof sketch.** Induction on the budget, generalizing the log. The history translates to the
log (`bridgePre_encodeHist`), so both next moves come from the same word, and `bridgePost_spec`
gives corresponding moves. An output `a` gives the leaf `a 0` against the leaf `a`
(`buildTree_*_of_ret`, `buildComp_*_of_ret`). A query with the budget spent gives the verdict
`false` against `zeroBits 1`, whose bit `0` is `false`. A query `x` within budget asks `f x` on
both sides (`QueryTree.eval_query`, `OracleComp.evalFn_query`), and the continuations agree by
induction, since the history of `L ++ [⟨0, x, f x⟩]` is that of `L` followed by `(x, f x)`. -/
theorem eval_buildTree_bridge (ℓ₁ ℓ₂ : ℕ) (D : List Bool → List Bool)
    (f : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)) :
    ∀ (q : ℕ) (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))),
      (buildTree (fun h => decodeOracleMove ℓ₁ (bridgePost (D (bridgePre (encodeHist h))))) q
          (logHist L)).eval f =
        (buildComp (fun L => decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1
            (D (pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))))
          (zeroBits 1) q L).evalFn (fun _ => f) 0 := by
  intro q
  induction q with
  | zero =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_zero_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_query hb, QueryTree.eval_ret, OracleComp.evalFn_pure, zeroBits_apply]
    · rw [buildTree_zero_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]
  | succ q ih =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_succ_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_query hb, QueryTree.eval_query, OracleComp.evalFn_query]
      have hh : logHist L ++ [(x, f x)] = logHist (L ++ [⟨0, x, f x⟩]) := by
        rw [logHist_eq, logHist_eq, List.map_append, List.map_singleton]
      rw [hh]
      exact ih (L ++ [⟨0, x, f x⟩])
    · rw [buildTree_succ_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]

end TCSlib.Cryptography.Games.EffFill
