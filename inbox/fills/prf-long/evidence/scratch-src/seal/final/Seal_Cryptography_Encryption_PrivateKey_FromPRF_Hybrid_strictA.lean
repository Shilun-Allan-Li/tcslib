import Lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.HardcoreBit.Basic
import Mathlib.Algebra.Ring.BooleanRing

set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "Complexity.PolyBound\nComplexity.PolyExpr._sizeOf_1\nComplexity.PolyExpr._sizeOf_inst\nComplexity.PolyExpr.eval._sunfold\nComplexity.PolyExpr.eval._unsafe_rec\nComplexity.PolyExpr.eval.match_1\nComplexity.PolyExpr.normal\nComplexity.PolyExpr.subst\nComplexity.PolyExpr.subst._sunfold\nComplexity.PolyExpr.subst._unsafe_rec\nComplexity.PolyExpr.subst.match_1\nComplexity.PolyTimeComputable\nComplexity.TimeConstructible\nComplexity.instDecidableEqPolyExpr\nComplexity.instDecidableEqPolyExpr.decEq\nComplexity.instDecidableEqPolyExpr.decEq._sunfold\nComplexity.instDecidableEqPolyExpr.decEq._unsafe_rec\nComplexity.instDecidableEqPolyExpr.decEq.match_1\nComplexity.instReprPolyExpr\nComplexity.instReprPolyExpr.repr\nComplexity.instReprPolyExpr.repr._sunfold\nComplexity.instReprPolyExpr.repr._unsafe_rec\nComplexity.instReprPolyExpr.repr.match_1\nComplexity.pairFstD\nComplexity.pairMapSnd\nComplexity.pairMapSnd.match_1\nComplexity.pairSndD\nComplexity.polyTimeComputable_unary.match_1_1\nTCSlib.Cryptography.Games.OracleComp.AllOutputs\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_inst\nTCSlib.Cryptography.Games.OracleComp.bind\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\nTCSlib.Cryptography.Games.OracleComp.call\nTCSlib.Cryptography.Games.OracleComp.instMonad\nTCSlib.Cryptography.Games.OracleComp.liftLeft\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\nTCSlib.Cryptography.Games.OracleComp.liftRight\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_inst\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\nTCSlib.Cryptography.HardcoreBit.PushesUniform\nTCSlib.Cryptography.Negligible\nTCSlib.Cryptography.Noticeable\nTCSlib.Cryptography.OracleAdversary.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy._sunfold\nTCSlib.Cryptography.QueryTree.BoundedBy._unsafe_rec\nTCSlib.Cryptography.QueryTree.BoundedBy.match_1\nTCSlib.Cryptography.QueryTree.eval\nTCSlib.Cryptography.QueryTree.eval._sunfold\nTCSlib.Cryptography.QueryTree.eval._unsafe_rec\nTCSlib.Cryptography.QueryTree.eval.match_1\nTCSlib.Cryptography.QueryTree.evalLazy\nTCSlib.Cryptography.QueryTree.evalLazy._sunfold\nTCSlib.Cryptography.QueryTree.evalLazy._unsafe_rec\nTCSlib.Cryptography.QueryTree.evalLazy.match_1\nTCSlib.Cryptography.QueryTree.induct\nTCSlib.Cryptography.QueryTree.induct._sunfold\nTCSlib.Cryptography.QueryTree.induct._unsafe_rec\nTCSlib.Cryptography.QueryTree.induct.match_1\nTCSlib.Cryptography.QueryTree.noteQuery\nTCSlib.Cryptography.QueryTree.simulate\nTCSlib.Cryptography.QueryTree.simulate._sunfold\nTCSlib.Cryptography.QueryTree.simulate._unsafe_rec\nTCSlib.Cryptography.acceptProb\nTCSlib.Cryptography.distAdv\nTCSlib.Cryptography.extendStream\nTCSlib.Cryptography.invProb\nTCSlib.Cryptography.lazyDist\nTCSlib.Cryptography.oracleDist\nTCSlib.Cryptography.predProb\nTCSlib.Cryptography.prfAdv\nTCSlib.Cryptography.randomFunction\nTCSlib.Cryptography.uexp\nTCSlib.Cryptography.uprob\nTCSlib.InformationTheory.FinDist.HasMinEntropy\nTCSlib.InformationTheory.FinDist._sizeOf_1\nTCSlib.InformationTheory.FinDist._sizeOf_inst\nTCSlib.InformationTheory.FinDist.collision\nTCSlib.InformationTheory.FinDist.instCoeFunForallReal\nTCSlib.InformationTheory.FinDist.map\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\nTCSlib.InformationTheory.FinDist.probTrue\nTCSlib.InformationTheory.FinDist.prod\nTCSlib.InformationTheory.FinDist.uniform\nTCSlib.InformationTheory.statDist\nTuring.Action._sizeOf_1\nTuring.Action._sizeOf_inst\nTuring.Action.apply\nTuring.Action.apply.match_1\nTuring.Action.mapState\nTuring.Action.mk._flat_ctor\nTuring.Cfg._sizeOf_1\nTuring.Cfg._sizeOf_inst\nTuring.Cfg.ext.match_1\nTuring.Cfg.init\nTuring.Cfg.inputSymbol\nTuring.Cfg.mapState\nTuring.Cfg.mk._flat_ctor\nTuring.Cfg.ofWords\nTuring.Cfg.select\nTuring.Cfg.workTapeSymbols\nTuring.CodeTM._sizeOf_1\nTuring.CodeTM._sizeOf_inst\nTuring.CodeTM.mk._flat_ctor\nTuring.CodeTM.serialize\nTuring.CodeTM.toFinTM\nTuring.EffectiveMachineCode._sizeOf_1\nTuring.EffectiveMachineCode._sizeOf_inst\nTuring.EffectiveMachineCode.mk._flat_ctor\nTuring.FinTM.Computes\nTuring.FinTM.ComputesFunInTime\nTuring.FinTM.ComputesFunInTimeVia\nTuring.FinTM.ComputesInTime\nTuring.FinTM.VirtualTag\nTuring.FinTM._sizeOf_1\nTuring.FinTM._sizeOf_inst\nTuring.FinTM.appendBitTM\nTuring.FinTM.branchTM\nTuring.FinTM.branchTM.match_1\nTuring.FinTM.bufferTape\nTuring.FinTM.bufferedCompTM\nTuring.FinTM.bufferedCompTM.match_1\nTuring.FinTM.bufferedFirstCfg\nTuring.FinTM.bufferedScanCfg\nTuring.FinTM.bufferedSecondCfg\nTuring.FinTM.callEntry\nTuring.FinTM.callExit\nTuring.FinTM.callTM\nTuring.FinTM.callTM.match_1\nTuring.FinTM.condTM\nTuring.FinTM.condTM.match_1\nTuring.FinTM.constTM\nTuring.FinTM.controlAction\nTuring.FinTM.emitAction\nTuring.FinTM.idTM\nTuring.FinTM.idTM.match_1\nTuring.FinTM.ifEqTM\nTuring.FinTM.ifEqTM.match_1\nTuring.FinTM.incFixedTM\nTuring.FinTM.incFixedTM.match_1\nTuring.FinTM.incFixedTM.match_3\nTuring.FinTM.indexedVisit\nTuring.FinTM.leftAction\nTuring.FinTM.leftCfg\nTuring.FinTM.lengthBitsTM\nTuring.FinTM.lengthBitsTM.match_1\nTuring.FinTM.mk._flat_ctor\nTuring.FinTM.pairExtractTM\nTuring.FinTM.pairExtractTM.match_1\nTuring.FinTM.pairExtractTM.match_3\nTuring.FinTM.pairExtractTM.match_5\nTuring.FinTM.pairLenCheckTM\nTuring.FinTM.pairValidTM\nTuring.FinTM.pairValidTM.match_1\nTuring.FinTM.polyBitsTM\nTuring.FinTM.polyUnaryTM\nTuring.FinTM.polyUnaryTM.match_1\nTuring.FinTM.prependTM\nTuring.FinTM.prependTM.match_1\nTuring.FinTM.redirectTM\nTuring.FinTM.redirectTM.match_1\nTuring.FinTM.redirectTM.match_3\nTuring.FinTM.rewind_scan.match_1\nTuring.FinTM.rightAction\nTuring.FinTM.rightCfg\nTuring.FinTM.splitSolveTM\nTuring.FinTM.splitSolveWithTM\nTuring.FinTM.stripLastTM\nTuring.FinTM.stripLastTM_computes.match_1\nTuring.FinTM.sweepAct\nTuring.FinTM.sweepCfg\nTuring.FinTM.sweepFold\nTuring.FinTM.sweepFold._sunfold\nTuring.FinTM.sweepFold._unsafe_rec\nTuring.FinTM.sweepFold.match_1\nTuring.FinTM.sweepRevCfg\nTuring.FinTM.sweepTape\nTuring.FinTM.tapeBlocks\nTuring.FinTM.timedCondTM\nTuring.FinTM.timedCondTM.match_1\nTuring.FinTM.toCodeTM\nTuring.FinTM.toCodeTM.match_1\nTuring.FinTM.unaryTokenTM\nTuring.FinTM.unaryTokenTM.match_1\nTuring.FinTM.virtualMove\nTuring.FinTM.virtualNextTag\nTuring.FinTM.virtualNextTag.match_1\nTuring.MachineCode._sizeOf_1\nTuring.MachineCode._sizeOf_inst\nTuring.MachineCode.mk._flat_ctor\nTuring.MultiTapeTM.AgreeOn\nTuring.MultiTapeTM.ComputableInTimeAndSpace\nTuring.MultiTapeTM.ComputesFunInTimeAndSpace\nTuring.MultiTapeTM.ComputesInTimeAndSpace\nTuring.MultiTapeTM.DecidableInTimeAndSpace\nTuring.MultiTapeTM._sizeOf_1\nTuring.MultiTapeTM._sizeOf_inst\nTuring.MultiTapeTM.haltsAtStep\nTuring.MultiTapeTM.indicator\nTuring.MultiTapeTM.initCfg\nTuring.MultiTapeTM.mk._flat_ctor\nTuring.MultiTapeTM.outputSymbol\nTuring.MultiTapeTM.relabelState\nTuring.MultiTapeTM.runFrom\nTuring.MultiTapeTM.spaceUsed\nTuring.MultiTapeTM.spaceUsedByTape\nTuring.MultiTapeTM.step\nTuring.MultiTapeTM.step.match_1\nTuring.MultiTapeTM.visitedByTapeHead\nTuring.actionBits\nTuring.captureAction\nTuring.captureAction.match_1\nTuring.captureCfg\nTuring.dbl\nTuring.embedEmitCfg\nTuring.embedEmitRetTM\nTuring.embedEmitTM\nTuring.embedSilentCfg\nTuring.embedSilentRetTM\nTuring.embedSilentRetTM.match_1\nTuring.embedSilentTM\nTuring.emitAction\nTuring.emitCfg\nTuring.incFixed\nTuring.incFixed._sunfold\nTuring.incFixed._unsafe_rec\nTuring.incFixed.match_1\nTuring.instInhabitedCfg\nTuring.instInhabitedCfg.default\nTuring.moveInputPos\nTuring.optBoolBits\nTuring.optBoolBits.match_1\nTuring.optOptBoolBits\nTuring.optOptBoolBits.match_1\nTuring.optStateBits\nTuring.optStateBits.match_1\nTuring.pairDecode\nTuring.pairDecode._sunfold\nTuring.pairDecode._unsafe_rec\nTuring.pairDecode.match_1\nTuring.pairDiagTM\nTuring.pairDiagTM.match_1\nTuring.pairDiagTM.match_3\nTuring.pairEncode\nTuring.signBits\nTuring.signBits.match_1\nTuring.solveSplit\nTuring.solveSplitWith\nTuring.spaceUsedOfCfgs\nTuring.splitAtLastTrue\nTuring.splitAtLastTrue.match_1\nTuring.stateWord\nTuring.unaryFin\nTuring.unaryTokenSplit\nTuring.unaryTokenSplit._sunfold\nTuring.unaryTokenSplit._unsafe_rec\nTuring.unaryTokenSplit.match_1\nTuring.visitedOfCfgs\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.pairMapSnd.match_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.polyTimeComputable_unary.match_1_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterBump\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCfg\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterTape\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.FinTM.lengthBitsTM.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.MultiTapeTM.step.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.eval.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.subst.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Convention.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnAction\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedSlot\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.callTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallBankFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallCleared\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEmbeddedCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallIdleTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallInterval\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLayout\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightScan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSlots\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSpan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackMid\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopForwardCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyDispatch\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyImage\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyPadded\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodySource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopControlAction\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCopyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCaptured\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelSource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHost_bound\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReady\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.List.filter.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.Action.apply.match_1.splitter"
  let want : List String := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← Lean.getEnv
  let mut byName : Std.HashMap String Lean.Name := {}
  for (n, _) in env.constants.toList do
    byName := byName.insert n.toString n
  let mut count : Nat := 0
  for s in want do
    let some n := byName[s]? | throwError "SEAL-HARNESS unknown constant {s}"
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if false then
      unless st == .irreducible do throwError "SEAL-VERIFY not irreducible: {s}"
    else
      unless st == .irreducible do
        Lean.Elab.Command.elabCommand
          (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    count := count + 1
  Lean.logInfo m!"SEAL-INSTALL final/Cryptography_Encryption_PrivateKey_FromPRF_Hybrid/strict-A part 1: {count}"

set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCopyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyMove\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyUnaryTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPrefixCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2LeftIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2OneIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2RightIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2SmallIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2Words\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterSplitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extractCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairValidTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.polyUnaryTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.prependTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.rawStripTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.scanCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBank\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitLoop_result.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPos\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareReady\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreClean\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRewindTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitSafe\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitScratch\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitStep\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.stripCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.unaryTokenTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.splitAtLastTrue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.unaryTokenSplit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectAction\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedBranchCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedCondTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedControlCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedPadTM\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedReadyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.captureAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.controlCfg\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.idTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.ifEqTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Deterministic.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.FinTM.toCodeTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDecode.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagCfg\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Finite.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBit\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBuffer\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCell\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arDecode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arIndex\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arMoveCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPending\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReadCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReady\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpaceBlock\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpacePhase\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTail\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTape\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arWriteCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGSpan\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGWindow.mk._flat_ctor\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCost\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCross\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgLeftRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgRetract\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepBoundary\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepSymbol\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit.match_1\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.virtualNextTag.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Sweep.0.Turing.FinTM.sweepFold.match_1.splitter\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.combine\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.mergeTable"
  let want : List String := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← Lean.getEnv
  let mut byName : Std.HashMap String Lean.Name := {}
  for (n, _) in env.constants.toList do
    byName := byName.insert n.toString n
  let mut count : Nat := 0
  for s in want do
    let some n := byName[s]? | throwError "SEAL-HARNESS unknown constant {s}"
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if false then
      unless st == .irreducible do throwError "SEAL-VERIFY not irreducible: {s}"
    else
      unless st == .irreducible do
        Lean.Elab.Command.elabCommand
          (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    count := count + 1
  Lean.logInfo m!"SEAL-INSTALL final/Cryptography_Encryption_PrivateKey_FromPRF_Hybrid/strict-A part 2: {count}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The finite PRF encryption hybrid

The outer switches use PRF advantage. The inner switches replace random-function
answers at sampled points by independent pads, with a loss bounded by the probability
of repeated points. The two independent-pad experiments agree by perfect secrecy.

## Main definitions

* `chainTree` asks a fixed tuple of oracle queries.
* `prfEncReal` and `otpEnc` sample the ciphertext tuples in the real and independent-pad experiments.
* `multiMsgAdv` runs a tuple distinguisher after querying the oracle at the sampled points.
* `prfEncRealOut`, `otpEncOut` and `multiMsgAdvOut` are the same at output width `l` (ruling B3);
  the `n`-bit ones are their cases `l = n` (`prfEncReal_eq_prfEncRealOut`, …).

## Main results

* `prfAdv_multiMsgAdv` identifies the outer switch with a PRF advantage.
* `distAdv_prfEncReal_random_otp_le` bounds the inner switch by the collision probability.
* `acceptProb_otpEnc` equates the two independent-pad experiments.
* `distAdv_prfEncReal_le` combines the switches [PS10, Theorem 99.2, proof].
* `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`, `acceptProb_otpEncOut` and
  `distAdv_prfEncRealOut_le` are the same at output width `l`; the four results above are their
  cases `l = n`.

**Deviation.** The vector has `q + 1` points, giving collision term `C(q + 1, 2) / 2^n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Query chains -/

/-- The query tree that asks the fixed tuple of queries `xs : Fin k → I` in order and then
outputs `f` applied to the tuple of answers: `k` `query` nodes in a chain. -/
def chainTree {I O α : Type} : ∀ (k : ℕ), (Fin k → I) → ((Fin k → O) → α) → QueryTree I O α
  | 0, _, f => .ret (f Fin.elim0)
  | k + 1, xs, f => .query (xs 0) fun o => chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-- Running a query chain against the oracle `g` outputs `f` of the tuple of answers
`g (xs j)`. -/
theorem eval_chainTree {I O α : Type} (g : I → O) :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α),
      (chainTree k xs f).eval g = f fun j => g (xs j)
  | 0, xs, f => by
    simp only [chainTree, QueryTree.eval_ret]
    congr
    funext j
    exact j.elim0
  | k + 1, xs, f => by
    simp only [chainTree, QueryTree.eval_query]
    rw [eval_chainTree g k]
    congr
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.tail_def]

/-- A chain of `k` queries makes at most `k` queries. -/
theorem boundedBy_chainTree {I O α : Type} :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α), (chainTree k xs f).BoundedBy k
  | 0, _, _ => by
    rw [chainTree]
    exact QueryTree.boundedBy_ret _ _
  | k + 1, xs, f => by
    rw [chainTree, QueryTree.boundedBy_query_succ]
    exact fun o => boundedBy_chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-! ### The hybrids of [PS10, Theorem 99.2], concrete -/

section Concrete

variable {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ]

variable {l : ℕ}

/-! #### The hybrids at output width `l`

The concrete hybrids for a keyed family `F : K → {0,1}^n → {0,1}^l` with `l`-bit outputs (ruling
B3): the points stay `n`-bit strings, only the answers, messages and pads have `l` bits. The
`n`-bit hybrids below are their cases `l = n` (`prfEncReal_eq_prfEncRealOut`, …). -/

/-- **The real hybrid at output width `l`** ([PS10, Theorem 99.2, proof, `H¹` and `H²`, with
`ℓ`-bit outputs]): the ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the
points `z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^l` and messages
`m : Fin (q+1) → {0,1}^l`: `prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))`. -/
def prfEncRealOut (F : K → (Fin n → Bool) → (Fin l → Bool)) (m : Fin (q + 1) → Fin l → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))

omit [Fintype K] in
/-- The real hybrid at width `l`, entrywise:
`prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))`. -/
theorem prfEncRealOut_apply (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m : Fin (q + 1) → Fin l → Bool) (z : K × (Fin (q + 1) → Fin n → Bool)) (j : Fin (q + 1)) :
    prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j)) := rfl

/-- **The one-time-pad hybrid at output width `l`** ([PS10, Theorem 99.2, proof, `H³`, with
`ℓ`-bit outputs]): the tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with `n`-bit points `r_j` and independent
uniform `l`-bit pads `p_j`, on the seeds `z = (r, p)`: `otpEncOut m z j = (z.1 j, m j + z.2 j)`. -/
def otpEncOut (m : Fin (q + 1) → Fin l → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)

/-- The one-time-pad hybrid at width `l`, entrywise: `otpEncOut m z j = (z.1 j, m j + z.2 j)`. -/
theorem otpEncOut_apply (m : Fin (q + 1) → Fin l → Bool)
    (z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool)) (j : Fin (q + 1)) :
    otpEncOut m z j = (z.1 j, m j + z.2 j) := rfl

/-- **The oracle adversary of Thm-99.2.1 at output width `l`** ([PS10, Theorem 99.2, proof, with
`ℓ`-bit outputs]): on coins `c = (r, c')` it queries its `l`-bit-output oracle at `r₀, …, r_q`
(`chainTree`), forms `(r_j, m_j ⊕ ans_j)_j` and runs `D` on it with coins `c'`:
`multiMsgAdvOut m D c = chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2`. -/
def multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin l → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2

omit [Fintype ρ] in
/-- Evaluating the hybrid adversary at width `l` against the oracle `g` runs `D` on the masked
tuple: `(multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2`
[PS10, Theorem 99.2, proof]. -/
theorem eval_multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool)
    (g : (Fin n → Bool) → Fin l → Bool) (c : (Fin (q + 1) → Fin n → Bool) × ρ) :
    (multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2 := by
  rw [multiMsgAdvOut, eval_chainTree]

omit [Fintype ρ] in
/-- `multiMsgAdvOut m D` makes at most `q + 1` queries: `(multiMsgAdvOut m D).BoundedBy (q + 1)`. -/
theorem multiMsgAdvOut_boundedBy (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    (multiMsgAdvOut m D).BoundedBy (q + 1) :=
  (OracleAdversary.boundedBy_iff _ _).2 fun c => boundedBy_chainTree (q + 1) c.1 _

/-- Running `multiMsgAdvOut m D` with the oracle `F k` for a uniform key accepts with the
probability that `D` accepts the hybrid at width `l`:
`acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D`
(reassociation of the seed space `K × (points × coins)`). -/
theorem acceptProb_oracleDist_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D := by
  rw [acceptProb_def, acceptProb_def]
  rw [← uprob_comp_equiv (Equiv.prodAssoc K (Fin (q + 1) → Fin n → Bool) ρ)]
  congr 1
  funext z
  simp only [oracleDist_apply, multiMsgAdvOut, eval_chainTree, Equiv.prodAssoc_apply]
  rfl

/-- **Thm-99.2.1 at output width `l`: the gap `H¹ → H²` is a PRF advantage** ([PS10,
Theorem 99.2, proof, with `ℓ`-bit outputs]):
`prfAdv F (multiMsgAdvOut m D) = distAdv (prfEncRealOut F m) (prfEncRealOut R m) D` with
`R = randomFunction {0,1}^n {0,1}^l` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
theorem prfAdv_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    prfAdv F (multiMsgAdvOut m D) =
      distAdv (prfEncRealOut F m)
        (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D := by
  rw [prfAdv_def, distAdv_def, distAdv_def, acceptProb_oracleDist_multiMsgAdvOut,
    acceptProb_oracleDist_multiMsgAdvOut]

/-- The ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the points
`z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^n`. With `F` the PRF this is the
hybrid `H¹` ("real encryptions"); with `F = randomFunction` (keys are function tables) it is
`H²` ("replace `f` with a truly random function `R`") of [PS10, Theorem 99.2, proof]. -/
def prfEncReal (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))

omit [Fintype K] in
/-- The real hybrid is the case `l = n` of the hybrid at width `l`:
`prfEncReal F m = prfEncRealOut F m` (`rfl`). -/
theorem prfEncReal_eq_prfEncRealOut (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool) : prfEncReal F m = prfEncRealOut F m := rfl

omit [Fintype K] in
/-- The hybrid ciphertext at position `j` contains the point `z.2 j` and the message
masked with the oracle's value at that point [PS10, Theorem 99.2, proof]. -/
theorem prfEncReal_apply (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool)
    (z : K × (Fin (q + 1) → Fin n → Bool)) (j : Fin (q + 1)) :
    prfEncReal F m z j = (z.2 j, m j + F z.1 (z.2 j)) := by
  rw [prfEncReal_eq_prfEncRealOut]
  exact prfEncRealOut_apply F m z j
/-- The ciphertext tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with independent uniform pads `p_j`: the
hybrid `H³` ("using OTP") of [PS10, Theorem 99.2, proof]; seeds `(r, p)`. -/
def otpEnc (m : Fin (q + 1) → Fin n → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)

/-- The one-time-pad hybrid is the case `l = n` of the hybrid at width `l`:
`otpEnc m = otpEncOut m` (`rfl`). -/
theorem otpEnc_eq_otpEncOut (m : Fin (q + 1) → Fin n → Bool) :
    otpEnc (n := n) m = otpEncOut m := rfl

/-- **The oracle adversary of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
otherwise (by closure under efficient operations) we contradict the pseudorandomness property"]):
on coins `(r, c)` it queries its oracle at `r₀, …, r_q` (a chain of `q + 1` queries), forms the
tuple `(r_j, m_j ⊕ ans_j)_j` and runs the distinguisher `D` on it with coins `c`. The messages
`m` are hard-wired (non-uniform advice in the machine version). -/
def multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin n → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2

omit [Fintype ρ] in
/-- The hybrid adversary is the case `l = n` of the adversary at width `l`:
`multiMsgAdv m D = multiMsgAdvOut m D` (`rfl`). -/
theorem multiMsgAdv_eq_multiMsgAdvOut (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    multiMsgAdv m D = multiMsgAdvOut m D := rfl

omit [Fintype ρ] in
/-- Evaluating the hybrid adversary on an oracle runs the tuple distinguisher on the sampled
points and the messages masked by the oracle values [PS10, Theorem 99.2, proof]. -/
theorem eval_multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool)
    (g : (Fin n → Bool) → Fin n → Bool) (c : (Fin (q + 1) → Fin n → Bool) × ρ) :
    (multiMsgAdv m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2 := by
  rw [multiMsgAdv_eq_multiMsgAdvOut]
  exact eval_multiMsgAdvOut m D g c

omit [Fintype ρ] in
/-- `multiMsgAdv m D` makes at most `q + 1` queries. -/
theorem multiMsgAdv_boundedBy (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    (multiMsgAdv m D).BoundedBy (q + 1) := by
  rw [multiMsgAdv_eq_multiMsgAdvOut]
  exact multiMsgAdvOut_boundedBy m D

/-- Running `multiMsgAdv m D` with the oracle `F k` (for a uniform key `k`) accepts with the
probability that `D` accepts the hybrid sampler `prfEncReal F m` (reassociation of the seed
space `K × (points × coins)`). -/
theorem acceptProb_oracleDist_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb F (oracleDist (multiMsgAdv m D)) = acceptProb (prfEncReal F m) D := by
  rw [multiMsgAdv_eq_multiMsgAdvOut, prfEncReal_eq_prfEncRealOut]
  exact acceptProb_oracleDist_multiMsgAdvOut F m D

/-- **Thm-99.2.1: the gap `H¹ → H²` is a PRF advantage.** The advantage of `D` between the real
encryptions `(r_j, m_j ⊕ F_k(r_j))_j` and the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` is exactly the PRF advantage of the `(q+1)`-query oracle adversary
`multiMsgAdv m D` against `F` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
theorem prfAdv_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    prfAdv F (multiMsgAdv m D) =
      distAdv (prfEncReal F m) (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D := by
  simp only [multiMsgAdv_eq_multiMsgAdvOut, prfEncReal_eq_prfEncRealOut]
  exact prfAdv_multiMsgAdvOut F m D

/-- **The collision bound** ([PS10, Theorem 99.2, proof, "`∃ i, j` such that `r_i = r_j`, but this
happens only with probability `C(q,2) · 2^{−n}`"]): `q + 1` uniform `n`-bit points fail to be
pairwise distinct with probability at most `C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** `¬ Injective r ↔ ∃ (i, j) with i < j, r i = r j`; the union bound
`uprob_exists_le` over the `C(q+1, 2)` pairs `i < j` (`Finset.card_filter` of `univ.filter (i < j)`
on `Fin (q+1) × Fin (q+1)`, `Fin.card_filter_lt`/`Nat.choose_two_right`-style counting); for
`i ≠ j` the pair `(r i, r j)` is uniform on `({0,1}^n)²` (`HardcoreBit.pushesUniform_eval_pair`),
so `uprob (r i = r j) = uprob (fun (a, b) => a = b) = 2^n / 4^n = 1 / 2^n`
(`PushesUniform.uprob_eq`, `uprob_eq_card_filter`, `Fintype.card_fun`, `Fintype.card_bool`). -/
theorem uprob_not_injective_le :
    uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  set S : Finset (Fin (q + 1) × Fin (q + 1)) := univ.filter fun p => p.1 < p.2 with hS
  -- a collision is a pair `i < j` with `r i = r j`
  have h1 : uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      uprob (fun r : Fin (q + 1) → Fin n → Bool => ∃ p ∈ S, r p.1 = r p.2) := by
    refine uprob_mono fun r hr => ?_
    rw [Function.not_injective_iff] at hr
    obtain ⟨i, j, hij, hne⟩ := hr
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨(i, j), by simp [S, h], hij⟩
    · exact ⟨(j, i), by simp [S, h], hij.symm⟩
  -- each pair `i < j` collides with probability `2^{-n}`
  have h3 : ∀ p ∈ S, uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) = 1 / 2 ^ n := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [S] using hp
    have h : uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) =
        uprob (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2) :=
      (HardcoreBit.pushesUniform_eval_pair (γ := Fin n → Bool) (ne_of_lt hlt)).uprob_eq
        (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2)
    rw [h, MultiMsg.uprob_eq_pair, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp
  -- the union bound over the `C(q+1, 2)` pairs
  have h2 := uprob_exists_le S (fun p (r : Fin (q + 1) → Fin n → Bool) => r p.1 = r p.2)
  rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hS,
    MultiMsg.card_filter_lt_pairs, mul_one_div] at h2
  exact h1.trans h2

/-- **A uniform table read at distinct points is uniform**: for an injective tuple of points
`r : Fin (q+1) → I`, the map `R ↦ (R (r j))_j` pushes the uniform distribution on tables
`I → O` forward to the uniform distribution on `Fin (q+1) → O` (the generalization of
`HardcoreBit.pushesUniform_eval_pair` from two points to `q + 1` points).

**Proof sketch.** For an empty `O` both averages are over empty types. Otherwise this is the
restriction along the injective `r` (`HardcoreBit.pushesUniform_restrict`). -/
theorem pushesUniform_comp_injective {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    {r : Fin (q + 1) → I} (hr : Function.Injective r) :
    HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j)) := by
  classical
  rcases isEmpty_or_nonempty O with hO | hO
  · -- no tables and no tuples: both averages are over empty types
    refine (HardcoreBit.pushesUniform_iff _).2 fun F => ?_
    haveI : IsEmpty (I → O) := ⟨fun R => hO.false (R (r 0))⟩
    haveI : IsEmpty (Fin (q + 1) → O) := ⟨fun f => hO.false (f 0)⟩
    simp only [uexp_def, univ_eq_empty, sum_empty, zero_div]
  · exact HardcoreBit.pushesUniform_restrict hr

/-- **Thm-99.2.2 at output width `l`: the gap `H² → H³` is at most the collision probability**
([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
`∃ i, j` such that `r_i = r_j`", with `ℓ`-bit outputs]): with `R = randomFunction {0,1}^n {0,1}^l`,
`distAdv (prfEncRealOut R m) (otpEncOut m) D ≤ C(q+1, 2) / 2^n`. The bound concerns the `n`-bit
points only; it does not depend on `l`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Write both acceptance probabilities as averages over the points `r`
(`uprob_prod` after reassociating the seeds): `a(r) := Pr_R[D((r_j, m_j ⊕ R(r_j))_j) = 1]` and
`b(r) := Pr_p[D((r_j, m_j ⊕ p_j)_j) = 1]`. When `r` is injective, `(R(r_j))_j` is uniform on
`({0,1}^l)^{q+1}` (`pushesUniform_comp_injective`, `PushesUniform.uprob_eq`), so `a(r) = b(r)`;
otherwise `|a(r) − b(r)| ≤ 1`. Hence `|E_r a − E_r b| ≤ uprob (¬ Injective)`
(`MultiMsg.abs_uexp_sub_le_uprob`), and `uprob_not_injective_le` bounds it. -/
theorem distAdv_prfEncRealOut_random_otp_le (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) (otpEncOut m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  -- the acceptance probabilities conditioned on the points `r`
  let a : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : ((Fin n → Bool) → (Fin l → Bool)) × ρ =>
      D (fun j => (r j, m j + w.1 (r j))) w.2 = true
  let b : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : (Fin (q + 1) → Fin l → Bool) × ρ => D (fun j => (r j, m j + w.1 j)) w.2 = true
  have ha : acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D =
      uexp a := by
    rw [acceptProb_def, show randomFunction (Fin n → Bool) (Fin l → Bool) = id from
      funext fun f => randomFunction_apply _ _ f]
    exact (uprob_comp_equiv ((Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      ((Fin n → Bool) → (Fin l → Bool)) ρ).symm.trans
        ((Equiv.prodComm _ _).prodCongr (Equiv.refl ρ))) _).symm.trans
      (by rw [uprob_prod]; rfl)
  have hb : acceptProb (otpEncOut m) D = uexp b := by
    rw [acceptProb_def]
    exact (uprob_comp_equiv (Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      (Fin (q + 1) → Fin l → Bool) ρ).symm _).symm.trans (by rw [uprob_prod]; rfl)
  -- at injective points the table values are fresh uniform pads
  have hab : ∀ r : Fin (q + 1) → Fin n → Bool, Function.Injective r → a r = b r := by
    intro r hr
    exact ((pushesUniform_comp_injective (O := Fin l → Bool) hr).prodMap
      (HardcoreBit.pushesUniform_id (Ω := ρ))).uprob_eq
      (fun v : (Fin (q + 1) → Fin l → Bool) × ρ => D (fun j => (r j, m j + v.1 j)) v.2 = true)
  rw [distAdv_def, ha, hb]
  exact (MultiMsg.abs_uexp_sub_le_uprob a b (fun r => ¬ Function.Injective r)
    (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩)
    (fun r hr => hab r (not_not.mp hr))).trans uprob_not_injective_le

/-- **Thm-99.2.3 at output width `l`: `H³ = H⁴` by the perfect secrecy of the one-time pad**
([PS10, Theorem 99.2, proof, with `ℓ`-bit outputs]): for independent uniform `l`-bit pads,
`acceptProb (otpEncOut m) D = acceptProb (otpEncOut m') D` for all messages `m`, `m'`.

**Proof sketch.** The map `(r, p) ↦ (r, p ⊕ (m ⊕ m'))` is a bijection of the seed space
(`Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))`) carrying the sampler for `m'` to the
sampler for `m` (in the Boolean group `x + x = 0`); relabel by it (`acceptProb_comp_equiv`). -/
theorem acceptProb_otpEncOut (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    acceptProb (otpEncOut (n := n) m) D = acceptProb (otpEncOut m') D := by
  have key : ∀ z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool),
      otpEncOut m' ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z) =
        otpEncOut m z := by
    intro z
    funext j
    simp only [otpEncOut, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight,
      Prod.map_fst, Prod.map_snd, id_eq, Pi.add_apply]
    refine Prod.ext rfl ?_
    funext i
    simp only [Pi.add_apply]
    cases m j i <;> cases m' j i <;> cases z.2 j i <;> rfl
  calc acceptProb (otpEncOut m) D
      = acceptProb (fun z => otpEncOut m'
          ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z)) D := by
        congr 1
        funext z
        exact (key z).symm
    _ = acceptProb (otpEncOut m') D := acceptProb_comp_equiv _ (otpEncOut m') D

/-- **[PS10, Theorem 99.2], concrete form, at output width `l`: the six-hybrid bound** (with
`ℓ`-bit outputs). For a keyed family `F : K → {0,1}^n → {0,1}^l`, message vectors
`m, m' ∈ ({0,1}^l)^{q+1}` and any distinguisher `D` of ciphertext tuples,
`distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤ prfAdv F (multiMsgAdvOut m D) +
prfAdv F (multiMsgAdvOut m' D) + 2 · C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Hybrids `H¹ = prfEncRealOut F m`, `H² = prfEncRealOut R m`, `H³ = otpEncOut m`,
`H⁴ = otpEncOut m'`, `H⁵ = prfEncRealOut R m'`, `H⁶ = prfEncRealOut F m'`: `|H¹ − H²|` and
`|H⁵ − H⁶|` are the two PRF advantages (`prfAdv_multiMsgAdvOut`), `|H² − H³|` and `|H⁴ − H⁵|`
are at most the collision bound (`distAdv_prfEncRealOut_random_otp_le`), `H³ = H⁴`
(`acceptProb_otpEncOut`); the triangle inequality (`abs_sub_le`, three times) finishes. -/
theorem distAdv_prfEncRealOut_le (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤
      prfAdv F (multiMsgAdvOut m D) + prfAdv F (multiMsgAdvOut m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
  have h12 := prfAdv_multiMsgAdvOut F m D
  have h56 := prfAdv_multiMsgAdvOut F m' D
  have h23 := distAdv_prfEncRealOut_random_otp_le m D
  have h45 := distAdv_prfEncRealOut_random_otp_le m' D
  have h34 := acceptProb_otpEncOut m m' D
  simp only [distAdv_def] at h12 h56 h23 h45 ⊢
  rw [h12, h56, abs_sub_comm (acceptProb (prfEncRealOut F m') D)]
  rw [abs_sub_comm (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m')
    D)] at h45
  have t1 := abs_sub_le (acceptProb (prfEncRealOut F m) D)
    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D)
    (acceptProb (prfEncRealOut F m') D)
  have t2 := abs_sub_le
    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D)
    (acceptProb (otpEncOut m) D) (acceptProb (prfEncRealOut F m') D)
  have t3 := abs_sub_le (acceptProb (otpEncOut m') D)
    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m') D)
    (acceptProb (prfEncRealOut F m') D)
  rw [← h34] at t3 h45
  linarith

/-- **Thm-99.2.2: the gap `H² → H³` is at most the collision probability**
([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
`∃ i, j` such that `r_i = r_j`"]): the advantage of `D` between the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` and the one-time-pad encryptions `(r_j, m_j ⊕ p_j)_j` is at most
`C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** The case `l = n` of `distAdv_prfEncRealOut_random_otp_le`
(`prfEncReal_eq_prfEncRealOut`, `otpEnc_eq_otpEncOut`). -/
theorem distAdv_prfEncReal_random_otp_le (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) (otpEnc m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  rw [prfEncReal_eq_prfEncRealOut, otpEnc_eq_otpEncOut]
  exact distAdv_prfEncRealOut_random_otp_le m D

/-- **Thm-99.2.3: `H³ = H⁴` by the perfect secrecy of the one-time pad** ([PS10, Theorem 99.2,
proof, "`H³` and `H⁴` are identical by the perfect secrecy of the OTP"], the vector version of
Claim-92.a): for independent uniform pads `p_j`, the tuples `(r_j, m_j ⊕ p_j)_j` and
`(r_j, m'_j ⊕ p_j)_j` are identically distributed, so every distinguisher accepts them with the
same probability.

**Proof sketch.** The case `l = n` of `acceptProb_otpEncOut` (`otpEnc_eq_otpEncOut`). -/
theorem acceptProb_otpEnc (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb (otpEnc m) D = acceptProb (otpEnc m') D := by
  rw [otpEnc_eq_otpEncOut, otpEnc_eq_otpEncOut]
  exact acceptProb_otpEncOut m m' D

/-- **[PS10, Theorem 99.2], concrete form: the six-hybrid bound.** For a keyed family
`F : K → {0,1}^n → {0,1}^n`, message vectors `m, m' ∈ ({0,1}^n)^{q+1}` and any distinguisher
`D` of ciphertext tuples, the advantage of `D` between the real encryptions of `m` and of `m'`
is at most `prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) / 2^n`, where `A_m D` is the
`(q+1)`-query oracle adversary `multiMsgAdv m D`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** The case `l = n` of `distAdv_prfEncRealOut_le` (`prfEncReal_eq_prfEncRealOut`,
`multiMsgAdv_eq_multiMsgAdvOut`). -/
theorem distAdv_prfEncReal_le (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal F m) (prfEncReal F m') D ≤
      prfAdv F (multiMsgAdv m D) + prfAdv F (multiMsgAdv m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
  simp only [prfEncReal_eq_prfEncRealOut, multiMsgAdv_eq_multiMsgAdvOut]
  exact distAdv_prfEncRealOut_le F m m' D

end Concrete

end TCSlib.Cryptography


set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "Complexity.PolyBound\nComplexity.PolyExpr._sizeOf_1\nComplexity.PolyExpr._sizeOf_inst\nComplexity.PolyExpr.eval._sunfold\nComplexity.PolyExpr.eval._unsafe_rec\nComplexity.PolyExpr.eval.match_1\nComplexity.PolyExpr.normal\nComplexity.PolyExpr.subst\nComplexity.PolyExpr.subst._sunfold\nComplexity.PolyExpr.subst._unsafe_rec\nComplexity.PolyExpr.subst.match_1\nComplexity.PolyTimeComputable\nComplexity.TimeConstructible\nComplexity.instDecidableEqPolyExpr\nComplexity.instDecidableEqPolyExpr.decEq\nComplexity.instDecidableEqPolyExpr.decEq._sunfold\nComplexity.instDecidableEqPolyExpr.decEq._unsafe_rec\nComplexity.instDecidableEqPolyExpr.decEq.match_1\nComplexity.instReprPolyExpr\nComplexity.instReprPolyExpr.repr\nComplexity.instReprPolyExpr.repr._sunfold\nComplexity.instReprPolyExpr.repr._unsafe_rec\nComplexity.instReprPolyExpr.repr.match_1\nComplexity.pairFstD\nComplexity.pairMapSnd\nComplexity.pairMapSnd.match_1\nComplexity.pairSndD\nComplexity.polyTimeComputable_unary.match_1_1\nTCSlib.Cryptography.Games.OracleComp.AllOutputs\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_inst\nTCSlib.Cryptography.Games.OracleComp.bind\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\nTCSlib.Cryptography.Games.OracleComp.call\nTCSlib.Cryptography.Games.OracleComp.instMonad\nTCSlib.Cryptography.Games.OracleComp.liftLeft\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\nTCSlib.Cryptography.Games.OracleComp.liftRight\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_inst\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\nTCSlib.Cryptography.HardcoreBit.PushesUniform\nTCSlib.Cryptography.Negligible\nTCSlib.Cryptography.Noticeable\nTCSlib.Cryptography.OracleAdversary.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy._sunfold\nTCSlib.Cryptography.QueryTree.BoundedBy._unsafe_rec\nTCSlib.Cryptography.QueryTree.BoundedBy.match_1\nTCSlib.Cryptography.QueryTree.eval\nTCSlib.Cryptography.QueryTree.eval._sunfold\nTCSlib.Cryptography.QueryTree.eval._unsafe_rec\nTCSlib.Cryptography.QueryTree.eval.match_1\nTCSlib.Cryptography.QueryTree.evalLazy\nTCSlib.Cryptography.QueryTree.evalLazy._sunfold\nTCSlib.Cryptography.QueryTree.evalLazy._unsafe_rec\nTCSlib.Cryptography.QueryTree.evalLazy.match_1\nTCSlib.Cryptography.QueryTree.induct\nTCSlib.Cryptography.QueryTree.induct._sunfold\nTCSlib.Cryptography.QueryTree.induct._unsafe_rec\nTCSlib.Cryptography.QueryTree.induct.match_1\nTCSlib.Cryptography.QueryTree.noteQuery\nTCSlib.Cryptography.QueryTree.simulate\nTCSlib.Cryptography.QueryTree.simulate._sunfold\nTCSlib.Cryptography.QueryTree.simulate._unsafe_rec\nTCSlib.Cryptography.acceptProb\nTCSlib.Cryptography.distAdv\nTCSlib.Cryptography.extendStream\nTCSlib.Cryptography.invProb\nTCSlib.Cryptography.lazyDist\nTCSlib.Cryptography.oracleDist\nTCSlib.Cryptography.predProb\nTCSlib.Cryptography.prfAdv\nTCSlib.Cryptography.randomFunction\nTCSlib.Cryptography.uexp\nTCSlib.Cryptography.uprob\nTCSlib.InformationTheory.FinDist.HasMinEntropy\nTCSlib.InformationTheory.FinDist._sizeOf_1\nTCSlib.InformationTheory.FinDist._sizeOf_inst\nTCSlib.InformationTheory.FinDist.collision\nTCSlib.InformationTheory.FinDist.instCoeFunForallReal\nTCSlib.InformationTheory.FinDist.map\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\nTCSlib.InformationTheory.FinDist.probTrue\nTCSlib.InformationTheory.FinDist.prod\nTCSlib.InformationTheory.FinDist.uniform\nTCSlib.InformationTheory.statDist\nTuring.Action._sizeOf_1\nTuring.Action._sizeOf_inst\nTuring.Action.apply\nTuring.Action.apply.match_1\nTuring.Action.mapState\nTuring.Action.mk._flat_ctor\nTuring.Cfg._sizeOf_1\nTuring.Cfg._sizeOf_inst\nTuring.Cfg.ext.match_1\nTuring.Cfg.init\nTuring.Cfg.inputSymbol\nTuring.Cfg.mapState\nTuring.Cfg.mk._flat_ctor\nTuring.Cfg.ofWords\nTuring.Cfg.select\nTuring.Cfg.workTapeSymbols\nTuring.CodeTM._sizeOf_1\nTuring.CodeTM._sizeOf_inst\nTuring.CodeTM.mk._flat_ctor\nTuring.CodeTM.serialize\nTuring.CodeTM.toFinTM\nTuring.EffectiveMachineCode._sizeOf_1\nTuring.EffectiveMachineCode._sizeOf_inst\nTuring.EffectiveMachineCode.mk._flat_ctor\nTuring.FinTM.Computes\nTuring.FinTM.ComputesFunInTime\nTuring.FinTM.ComputesFunInTimeVia\nTuring.FinTM.ComputesInTime\nTuring.FinTM.VirtualTag\nTuring.FinTM._sizeOf_1\nTuring.FinTM._sizeOf_inst\nTuring.FinTM.appendBitTM\nTuring.FinTM.branchTM\nTuring.FinTM.branchTM.match_1\nTuring.FinTM.bufferTape\nTuring.FinTM.bufferedCompTM\nTuring.FinTM.bufferedCompTM.match_1\nTuring.FinTM.bufferedFirstCfg\nTuring.FinTM.bufferedScanCfg\nTuring.FinTM.bufferedSecondCfg\nTuring.FinTM.callEntry\nTuring.FinTM.callExit\nTuring.FinTM.callTM\nTuring.FinTM.callTM.match_1\nTuring.FinTM.condTM\nTuring.FinTM.condTM.match_1\nTuring.FinTM.constTM\nTuring.FinTM.controlAction\nTuring.FinTM.emitAction\nTuring.FinTM.idTM\nTuring.FinTM.idTM.match_1\nTuring.FinTM.ifEqTM\nTuring.FinTM.ifEqTM.match_1\nTuring.FinTM.incFixedTM\nTuring.FinTM.incFixedTM.match_1\nTuring.FinTM.incFixedTM.match_3\nTuring.FinTM.indexedVisit\nTuring.FinTM.leftAction\nTuring.FinTM.leftCfg\nTuring.FinTM.lengthBitsTM\nTuring.FinTM.lengthBitsTM.match_1\nTuring.FinTM.mk._flat_ctor\nTuring.FinTM.pairExtractTM\nTuring.FinTM.pairExtractTM.match_1\nTuring.FinTM.pairExtractTM.match_3\nTuring.FinTM.pairExtractTM.match_5\nTuring.FinTM.pairLenCheckTM\nTuring.FinTM.pairValidTM\nTuring.FinTM.pairValidTM.match_1\nTuring.FinTM.polyBitsTM\nTuring.FinTM.polyUnaryTM\nTuring.FinTM.polyUnaryTM.match_1\nTuring.FinTM.prependTM\nTuring.FinTM.prependTM.match_1\nTuring.FinTM.redirectTM\nTuring.FinTM.redirectTM.match_1\nTuring.FinTM.redirectTM.match_3\nTuring.FinTM.rewind_scan.match_1\nTuring.FinTM.rightAction\nTuring.FinTM.rightCfg\nTuring.FinTM.splitSolveTM\nTuring.FinTM.splitSolveWithTM\nTuring.FinTM.stripLastTM\nTuring.FinTM.stripLastTM_computes.match_1\nTuring.FinTM.sweepAct\nTuring.FinTM.sweepCfg\nTuring.FinTM.sweepFold\nTuring.FinTM.sweepFold._sunfold\nTuring.FinTM.sweepFold._unsafe_rec\nTuring.FinTM.sweepFold.match_1\nTuring.FinTM.sweepRevCfg\nTuring.FinTM.sweepTape\nTuring.FinTM.tapeBlocks\nTuring.FinTM.timedCondTM\nTuring.FinTM.timedCondTM.match_1\nTuring.FinTM.toCodeTM\nTuring.FinTM.toCodeTM.match_1\nTuring.FinTM.unaryTokenTM\nTuring.FinTM.unaryTokenTM.match_1\nTuring.FinTM.virtualMove\nTuring.FinTM.virtualNextTag\nTuring.FinTM.virtualNextTag.match_1\nTuring.MachineCode._sizeOf_1\nTuring.MachineCode._sizeOf_inst\nTuring.MachineCode.mk._flat_ctor\nTuring.MultiTapeTM.AgreeOn\nTuring.MultiTapeTM.ComputableInTimeAndSpace\nTuring.MultiTapeTM.ComputesFunInTimeAndSpace\nTuring.MultiTapeTM.ComputesInTimeAndSpace\nTuring.MultiTapeTM.DecidableInTimeAndSpace\nTuring.MultiTapeTM._sizeOf_1\nTuring.MultiTapeTM._sizeOf_inst\nTuring.MultiTapeTM.haltsAtStep\nTuring.MultiTapeTM.indicator\nTuring.MultiTapeTM.initCfg\nTuring.MultiTapeTM.mk._flat_ctor\nTuring.MultiTapeTM.outputSymbol\nTuring.MultiTapeTM.relabelState\nTuring.MultiTapeTM.runFrom\nTuring.MultiTapeTM.spaceUsed\nTuring.MultiTapeTM.spaceUsedByTape\nTuring.MultiTapeTM.step\nTuring.MultiTapeTM.step.match_1\nTuring.MultiTapeTM.visitedByTapeHead\nTuring.actionBits\nTuring.captureAction\nTuring.captureAction.match_1\nTuring.captureCfg\nTuring.dbl\nTuring.embedEmitCfg\nTuring.embedEmitRetTM\nTuring.embedEmitTM\nTuring.embedSilentCfg\nTuring.embedSilentRetTM\nTuring.embedSilentRetTM.match_1\nTuring.embedSilentTM\nTuring.emitAction\nTuring.emitCfg\nTuring.incFixed\nTuring.incFixed._sunfold\nTuring.incFixed._unsafe_rec\nTuring.incFixed.match_1\nTuring.instInhabitedCfg\nTuring.instInhabitedCfg.default\nTuring.moveInputPos\nTuring.optBoolBits\nTuring.optBoolBits.match_1\nTuring.optOptBoolBits\nTuring.optOptBoolBits.match_1\nTuring.optStateBits\nTuring.optStateBits.match_1\nTuring.pairDecode\nTuring.pairDecode._sunfold\nTuring.pairDecode._unsafe_rec\nTuring.pairDecode.match_1\nTuring.pairDiagTM\nTuring.pairDiagTM.match_1\nTuring.pairDiagTM.match_3\nTuring.pairEncode\nTuring.signBits\nTuring.signBits.match_1\nTuring.solveSplit\nTuring.solveSplitWith\nTuring.spaceUsedOfCfgs\nTuring.splitAtLastTrue\nTuring.splitAtLastTrue.match_1\nTuring.stateWord\nTuring.unaryFin\nTuring.unaryTokenSplit\nTuring.unaryTokenSplit._sunfold\nTuring.unaryTokenSplit._unsafe_rec\nTuring.unaryTokenSplit.match_1\nTuring.visitedOfCfgs\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.pairMapSnd.match_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.polyTimeComputable_unary.match_1_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterBump\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCfg\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterTape\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.FinTM.lengthBitsTM.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.MultiTapeTM.step.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.eval.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.subst.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Convention.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnAction\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedSlot\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.callTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallBankFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallCleared\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEmbeddedCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallIdleTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallInterval\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLayout\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightScan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSlots\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSpan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackMid\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopForwardCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyDispatch\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyImage\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyPadded\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodySource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopControlAction\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCopyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCaptured\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelSource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHost_bound\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReady\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.List.filter.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.Action.apply.match_1.splitter"
  let want : List String := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← Lean.getEnv
  let mut byName : Std.HashMap String Lean.Name := {}
  for (n, _) in env.constants.toList do
    byName := byName.insert n.toString n
  let mut count : Nat := 0
  for s in want do
    let some n := byName[s]? | throwError "SEAL-HARNESS unknown constant {s}"
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if true then
      unless st == .irreducible do throwError "SEAL-VERIFY not irreducible: {s}"
    else
      unless st == .irreducible do
        Lean.Elab.Command.elabCommand
          (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    count := count + 1
  Lean.logInfo m!"SEAL-VERIFY final/Cryptography_Encryption_PrivateKey_FromPRF_Hybrid/strict-A part 1: {count}"

set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCopyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyMove\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyUnaryTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPrefixCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2LeftIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2OneIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2RightIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2SmallIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2Words\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterSplitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extractCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairValidTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.polyUnaryTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.prependTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.rawStripTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.scanCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBank\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitLoop_result.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPos\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareReady\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreClean\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRewindTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitSafe\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitScratch\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitStep\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.stripCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.unaryTokenTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.splitAtLastTrue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.unaryTokenSplit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectAction\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedBranchCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedCondTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedControlCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedPadTM\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedReadyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.captureAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.controlCfg\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.idTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.ifEqTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Deterministic.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.FinTM.toCodeTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDecode.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagCfg\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Finite.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBit\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBuffer\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCell\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arDecode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arIndex\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arMoveCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPending\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReadCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReady\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpaceBlock\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpacePhase\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTail\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTape\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arWriteCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGSpan\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGWindow.mk._flat_ctor\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCost\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCross\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgLeftRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgRetract\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepBoundary\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepSymbol\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit.match_1\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.virtualNextTag.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Sweep.0.Turing.FinTM.sweepFold.match_1.splitter\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.combine\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.mergeTable"
  let want : List String := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← Lean.getEnv
  let mut byName : Std.HashMap String Lean.Name := {}
  for (n, _) in env.constants.toList do
    byName := byName.insert n.toString n
  let mut count : Nat := 0
  for s in want do
    let some n := byName[s]? | throwError "SEAL-HARNESS unknown constant {s}"
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if true then
      unless st == .irreducible do throwError "SEAL-VERIFY not irreducible: {s}"
    else
      unless st == .irreducible do
        Lean.Elab.Command.elabCommand
          (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    count := count + 1
  Lean.logInfo m!"SEAL-VERIFY final/Cryptography_Encryption_PrivateKey_FromPRF_Hybrid/strict-A part 2: {count}"
