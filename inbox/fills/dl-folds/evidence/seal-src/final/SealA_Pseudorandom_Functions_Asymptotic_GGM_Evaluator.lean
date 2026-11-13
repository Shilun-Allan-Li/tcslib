/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.ReductionSupport
import TCSlib.Cryptography.Pseudorandom.Functions.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the GGM evaluator

The evaluator follows a path in the GGM tree on a string state containing the
current label and the remaining input. The bit-string identities connect this
implementation to the finite GGM construction.

## Main definitions

* `TCSlib.Cryptography.selHalf` selects a half of the next label.
* `TCSlib.Cryptography.ggmStep` and `TCSlib.Cryptography.ggmEval` run the tree walk.

## Main results

* `TCSlib.Cryptography.ggmEval_poly` and `TCSlib.Cryptography.ggmEval_ofFn` give
  polynomial running time and agreement with the finite evaluator.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8, Theorem 97.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, Construction 3.3.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! Seal A (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean`, with every seal candidate of its
full TCSlib import closure (396 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockDone _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ## Bit-string identities -/

/-- Every bit of a `q·ℓ`-bit string is a bit of one of its blocks:
`w k = FunFamily.blocks q ℓ w k.divNat k.modNat` (read off `FunFamily.blocks_symm_apply`). -/
theorem eq_blocks_divNat_modNat {q ℓ : ℕ} (w : Fin (q * ℓ) → Bool) (k : Fin (q * ℓ)) :
    w k = FunFamily.blocks q ℓ w k.divNat k.modNat :=
  calc w k = (FunFamily.blocks q ℓ).symm (FunFamily.blocks q ℓ w) k := by rw [Equiv.symm_apply_apply]
    _ = FunFamily.blocks q ℓ w k.divNat k.modNat := FunFamily.blocks_symm_apply q ℓ _ k

/-- Block `k` of the encoding of a `q`-tuple of `ℓ`-bit strings (positions `ℓk, …, ℓk + ℓ − 1`)
is the encoding of the `k`-th component, read through `FunFamily.blocks` (the block window
`FunFamily.ofFn_blocks`, read backwards). -/
theorem drop_take_ofFn_blocks (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) {k : ℕ} (hk : k < q) :
    ((List.ofFn w).drop (ℓ * k)).take ℓ = List.ofFn (FunFamily.blocks q ℓ w ⟨k, hk⟩) := by
  rw [Nat.mul_comm ℓ k, FunFamily.ofFn_blocks]

/-- The encoding of the `i`-bit prefix `prefixAt x i` (`i ≤ n`) is the first `i` bits of the
encoding of `x`. -/
theorem ofFn_prefixAt {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i ≤ n) :
    List.ofFn (prefixAt x i) = (List.ofFn x).take i := by
  rw [take_ofFn_castLE hi]
  congr 1
  funext k
  have hk : (k : ℕ) < n := lt_of_lt_of_le k.isLt hi
  simp only [prefixAt_apply, hk, dite_true]
  rfl

/-- The first `n` bits of the encoding of a `2n`-bit string encode the first component of
`splitHalves`. -/
theorem take_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).take n = List.ofFn (splitHalves z).1 := by
  refine (take_ofFn_castLE (by omega) z).trans ?_
  exact congrArg List.ofFn (funext fun k => (splitHalves_apply_fst z k).symm)

/-- The last `n` bits of the encoding of a `2n`-bit string encode the second component of
`splitHalves`. -/
theorem drop_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).drop n = List.ofFn (splitHalves z).2 := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_drop, List.getElem_ofFn]
  rw [splitHalves_apply_snd]

/-- **Half selection on strings:** the first (`b = false`) or the last (`b = true`) `|u|` bits
of the word `v` — `g_b(x)` of [PS10, Theorem 97.3] read off the string `g(x) = g₀(x) ‖ g₁(x)`
with the reference length `|u| = n`. -/
def selHalf (b : Bool) (u v : List Bool) : List Bool :=
  if b then (v.drop u.length).take u.length else v.take u.length

/-- Half selection on the encoding of a `2n`-bit string (reference length `n`) is the
encoding of `pairSel b (splitHalves z)`. -/
theorem selHalf_ofFn {n : ℕ} (b : Bool) {u : List Bool} (hu : u.length = n)
    (z : Fin (2 * n) → Bool) :
    selHalf b u (List.ofFn z) = List.ofFn (pairSel b (splitHalves z)) := by
  cases b
  · simp only [selHalf, pairSel_false, Bool.false_eq_true, if_false, hu, take_ofFn_splitHalves]
  · simp only [selHalf, pairSel_true, if_true, hu, drop_ofFn_splitHalves]
    exact List.take_of_length_le (le_of_eq List.length_ofFn)

/-- Half selection is at most as long as the reference word. -/
theorem length_selHalf_le (b : Bool) (u v : List Bool) : (selHalf b u v).length ≤ u.length := by
  unfold selHalf
  split_ifs <;> exact List.length_take_le _ _

/-- Half selection is polynomial-time in its three polynomial-time arguments (the typed cuts
`takeLen_poly`/`dropLen_poly` and `Complexity.polyTimeComputable_ite`). -/
theorem selHalf_poly {p : List Bool → Bool} {u v : List Bool → List Bool}
    (hp : PolyTimeComputable fun w => [p w]) (hu : PolyTimeComputable u)
    (hv : PolyTimeComputable v) : PolyTimeComputable fun w => selHalf (p w) (u w) (v w) :=
  polyTimeComputable_ite hp (takeLen_poly hu (dropLen_poly hu hv)) (takeLen_poly hu hv)

/-! ## The GGM evaluator -/

/-- **One step of the walk down the GGM tree** on the state word `⟨y, rest⟩` (current label
`y`, remaining input bits `rest`): if `rest` is empty, stay; otherwise replace `y` by the half
of `E y` selected by the head bit of `rest` (`selHalf`, reference length `|y|`) and drop that
bit. `E` is the evaluator of the length-doubling generator. -/
def ggmStep (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  if pairSndD w = [] then w
  else pairEncode (selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)))
    (pairSndD w).tail

/-- The walk down the tree from the label `y` along the bits `bs`:
`walk G' y [b₁, …, b_k] = G'_{b_k}(⋯ G'_{b₁}(y) ⋯)`. -/
def walk {S : Type} (G' : S → S × S) (y : S) (bs : List Bool) : S :=
  bs.foldl (fun y b => pairSel b (G' y)) y

/-- `ggmFrom G' x i y` is the walk from `y` along the bits of `x` from position `i` on
(strong induction on `n − i`, `ggmFrom_of_lt`, `ggmFrom_of_le`). -/
theorem ggmFrom_eq_walk {S : Type} (G' : S → S × S) {n : ℕ} (x : Fin n → Bool) :
    ∀ (i : ℕ) (y : S), ggmFrom G' x i y = walk G' y ((List.ofFn x).drop i)
  | i, y => by
    by_cases h : i < n
    · rw [ggmFrom_of_lt G' x h, ggmFrom_eq_walk G' x (i + 1)]
      have hd : (List.ofFn x).drop i = x ⟨i, h⟩ :: (List.ofFn x).drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_ofFn]
      rw [hd, walk, walk, List.foldl_cons]
    · rw [ggmFrom_of_le G' x (not_lt.1 h), List.drop_of_length_le (by simpa using not_lt.1 h)]
      rfl
termination_by i => n - i

/-- The GGM step never lengthens a word. -/
theorem length_ggmStep_le (E : List Bool → List Bool) (w : List Bool) :
    (ggmStep E w).length ≤ w.length := by
  unfold ggmStep
  split_ifs with h
  · exact le_rfl
  · obtain ⟨a, b, hw⟩ : ∃ a b, w = pairEncode a b := by
      cases hd : pairDecode w with
      | none => exact absurd (pairSndD_of_pairDecode_eq_none hd) h
      | some ab => exact ⟨ab.1, ab.2, eq_pairEncode_of_pairDecode w ab.1 ab.2 hd⟩
    subst hw
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at h ⊢
    rw [length_pairEncode, length_pairEncode, List.length_tail]
    have h1 := length_selHalf_le (b.headD false) a (E a)
    have h2 : 0 < b.length := List.length_pos_of_ne_nil h
    omega

/-- The orbit of the GGM step stays within the input length. -/
theorem length_ggmStep_iterate_le (E : List Bool → List Bool) (w : List Bool) (k : ℕ) :
    ((ggmStep E)^[k] w).length ≤ w.length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (length_ggmStep_le E _).trans ih

/-- The GGM step is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
of `rest`, `selHalf_poly`, `polyTimeComputable_headD`, `Complexity.polyTimeComputable_tail`). -/
theorem ggmStep_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmStep E) := by
  have hsel : PolyTimeComputable fun w =>
      selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)) :=
    selHalf_poly (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)
      polyTimeComputable_pairFstD (hE.comp polyTimeComputable_pairFstD)
  have htest : PolyTimeComputable fun w => [decide (pairSndD w = [])] :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairSndD
  convert polyTimeComputable_ite htest polyTimeComputable_id
    (hsel.pairEncode
        ((polyTimeComputable_tail.congr fun _ => List.drop_one).comp
            polyTimeComputable_pairSndD)) using 1
  funext w
  simp [ggmStep]

/-- **Closed form of the GGM step's orbit on encoded data:** from `⟨s, bs⟩` with `s` an
`n`-bit label, after `k` steps the state is `⟨walk s (bs.take k), bs.drop k⟩`.

**Proof sketch.** Induction on `k`. On an empty `rest` the step is the identity and the walk
is trivial. On `b :: bs` the step replaces the label by the half of `E (ofFn s) = ofFn (G s)`
selected by `b`, which is `ofFn (pairSel b (splitHalves (G s)))` by `selHalf_ofFn`, and drops
`b`; the induction hypothesis from the new label and `bs` finishes. -/
theorem ggmStep_iterate {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s)) :
    ∀ (k : ℕ) (y : Fin n → Bool) (bs : List Bool),
      (ggmStep E)^[k] (pairEncode (List.ofFn y) bs) =
        pairEncode (List.ofFn (walk (splitHalves ∘ G) y (bs.take k))) (bs.drop k)
  | 0, y, bs => by simp [walk]
  | k + 1, y, bs => by
    rw [Function.iterate_succ_apply]
    cases bs with
    | nil =>
      have h0 : ggmStep E (pairEncode (List.ofFn y) []) = pairEncode (List.ofFn y) [] := by
        simp [ggmStep]
      rw [h0, ggmStep_iterate hG k y []]
      simp [walk]
    | cons b bs =>
      have h1 : ggmStep E (pairEncode (List.ofFn y) (b :: bs)) =
          pairEncode (List.ofFn (pairSel b (splitHalves (G y)))) bs := by
        simp only [ggmStep, pairSndD_pairEncode, pairFstD_pairEncode, List.headD_cons,
          List.tail_cons, hG]
        rw [if_neg (List.cons_ne_nil _ _), selHalf_ofFn b List.length_ofFn]
      rw [h1, ggmStep_iterate hG k]
      simp [walk, List.take_succ_cons, List.drop_succ_cons, List.foldl_cons]

/-- **The GGM evaluator** (Claim-97.c): on `⟨s, x⟩` iterate the GGM step `|⟨s, x⟩|` times
(at least `|x|`, after which the step is the identity) and read the label. -/
def ggmEval (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairFstD ((ggmStep E)^[w.length] w)

/-- The GGM evaluator is polynomial-time (`Complexity.polyTimeComputable_iterate` with
`R = P = var`, the orbit staying within the input length). -/
theorem ggmEval_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmEval E) := by
  have h := polyTimeComputable_iterate (ggmStep_poly hE) .var .var
    (fun x i _ => by rw [PolyExpr.eval_var]; exact length_ggmStep_iterate_le E x i)
  simp only [PolyExpr.eval_var] at h
  exact polyTimeComputable_pairFstD.comp h

/-- The GGM evaluator on `⟨s, bs⟩` with an `n`-bit label `s` and an arbitrary bit list `bs`
computes the walk from `s` along `bs` (`ggmStep_iterate`; the word is at least as long as
`bs`, so all bits are consumed). -/
theorem ggmEval_ofFn_walk {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (y : Fin n → Bool) (bs : List Bool) :
    ggmEval E (pairEncode (List.ofFn y) bs) = List.ofFn (walk (splitHalves ∘ G) y bs) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode,
    List.take_of_length_le (by rw [length_pairEncode]; omega)]

/-- **The GGM evaluator computes the GGM family:** on `⟨s, x⟩` with `s, x` `n`-bit strings it
returns the encoding of `ggmBits G s x = g_{x_n}(⋯ g_{x_1}(s) ⋯)` (`ggmStep_iterate`,
`ggmFrom_eq_walk`). -/
theorem ggmEval_ofFn {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (s x : Fin n → Bool) :
    ggmEval E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (ggmBits G s x) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode]
  congr 1
  rw [List.take_of_length_le (by rw [length_pairEncode]; simp)]
  rw [ggmBits_def, ggm_apply, ggmFrom_eq_walk, List.drop_zero]

end TCSlib.Cryptography
