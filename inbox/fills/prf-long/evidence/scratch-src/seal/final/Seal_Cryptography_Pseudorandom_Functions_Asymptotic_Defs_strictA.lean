import Lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling

set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "Complexity.NUPPT.Computes\nComplexity.NUPPT.Uniform\nComplexity.NUPPT._sizeOf_1\nComplexity.NUPPT._sizeOf_inst\nComplexity.NUPPT.advInput\nComplexity.NUPPT.adviceLen\nComplexity.NUPPT.coinLen\nComplexity.NUPPT.coinsCongr\nComplexity.NUPPT.coinsEquivPoly\nComplexity.NUPPT.coinsEquiv_ofPolyTime\nComplexity.NUPPT.coinsEquiv_ofPolyTimeUniform\nComplexity.NUPPT.distinguisher\nComplexity.NUPPT.distinguisherL\nComplexity.NUPPT.inverter\nComplexity.NUPPT.inverterLit\nComplexity.NUPPT.mk._flat_ctor\nComplexity.NUPPT.ofPolyTime\nComplexity.NUPPT.ofPolyTimeUniform\nComplexity.NUPPT.output\nComplexity.NUPPT.predictor\nComplexity.NUPPT.runAt\nComplexity.NUPPT.runAtL\nComplexity.NUPPT.runLit\nComplexity.NUPPT.timeBound\nComplexity.PPT\nComplexity.PPT.ofPolyTime\nComplexity.PPT.toNUPPT\nComplexity.PolyBound\nComplexity.PolyExpr._sizeOf_1\nComplexity.PolyExpr._sizeOf_inst\nComplexity.PolyExpr.eval._sunfold\nComplexity.PolyExpr.eval._unsafe_rec\nComplexity.PolyExpr.eval.match_1\nComplexity.PolyExpr.normal\nComplexity.PolyExpr.subst\nComplexity.PolyExpr.subst._sunfold\nComplexity.PolyExpr.subst._unsafe_rec\nComplexity.PolyExpr.subst.match_1\nComplexity.PolyTimeComputable\nComplexity.TimeConstructible\nComplexity.instDecidableEqPolyExpr\nComplexity.instDecidableEqPolyExpr.decEq\nComplexity.instDecidableEqPolyExpr.decEq._sunfold\nComplexity.instDecidableEqPolyExpr.decEq._unsafe_rec\nComplexity.instDecidableEqPolyExpr.decEq.match_1\nComplexity.instReprPolyExpr\nComplexity.instReprPolyExpr.repr\nComplexity.instReprPolyExpr.repr._sunfold\nComplexity.instReprPolyExpr.repr._unsafe_rec\nComplexity.instReprPolyExpr.repr.match_1\nComplexity.pairFstD\nComplexity.pairMapSnd\nComplexity.pairMapSnd.match_1\nComplexity.pairSndD\nComplexity.polyTimeComputable_unary.match_1_1\nTCSlib.Cryptography.FunFamily.blocks\nTCSlib.Cryptography.Games.OracleComp.AllOutputs\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_inst\nTCSlib.Cryptography.Games.OracleComp.bind\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\nTCSlib.Cryptography.Games.OracleComp.call\nTCSlib.Cryptography.Games.OracleComp.instMonad\nTCSlib.Cryptography.Games.OracleComp.liftLeft\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\nTCSlib.Cryptography.Games.OracleComp.liftRight\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_inst\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\nTCSlib.Cryptography.HardcoreBit.PushesUniform\nTCSlib.Cryptography.Negligible\nTCSlib.Cryptography.Noticeable\nTCSlib.Cryptography.OracleAdversary.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy._sunfold\nTCSlib.Cryptography.QueryTree.BoundedBy._unsafe_rec\nTCSlib.Cryptography.QueryTree.BoundedBy.match_1\nTCSlib.Cryptography.QueryTree.eval\nTCSlib.Cryptography.QueryTree.eval._sunfold\nTCSlib.Cryptography.QueryTree.eval._unsafe_rec\nTCSlib.Cryptography.QueryTree.eval.match_1\nTCSlib.Cryptography.QueryTree.evalLazy\nTCSlib.Cryptography.QueryTree.evalLazy._sunfold\nTCSlib.Cryptography.QueryTree.evalLazy._unsafe_rec\nTCSlib.Cryptography.QueryTree.evalLazy.match_1\nTCSlib.Cryptography.QueryTree.induct\nTCSlib.Cryptography.QueryTree.induct._sunfold\nTCSlib.Cryptography.QueryTree.induct._unsafe_rec\nTCSlib.Cryptography.QueryTree.induct.match_1\nTCSlib.Cryptography.QueryTree.noteQuery\nTCSlib.Cryptography.QueryTree.simulate\nTCSlib.Cryptography.QueryTree.simulate._sunfold\nTCSlib.Cryptography.QueryTree.simulate._unsafe_rec\nTCSlib.Cryptography.acceptProb\nTCSlib.Cryptography.blocksEquivX\nTCSlib.Cryptography.coinBlock\nTCSlib.Cryptography.coinBlock_flatten.match_1_1\nTCSlib.Cryptography.decodeFin\nTCSlib.Cryptography.distAdv\nTCSlib.Cryptography.extendStream\nTCSlib.Cryptography.invProb\nTCSlib.Cryptography.invProbOpt\nTCSlib.Cryptography.lazyDist\nTCSlib.Cryptography.oracleDist\nTCSlib.Cryptography.padFin\nTCSlib.Cryptography.predProb\nTCSlib.Cryptography.prfAdv\nTCSlib.Cryptography.randomFunction\nTCSlib.Cryptography.uexp\nTCSlib.Cryptography.uprob\nTCSlib.Cryptography.xorPerm\nTCSlib.InformationTheory.FinDist.HasMinEntropy\nTCSlib.InformationTheory.FinDist._sizeOf_1\nTCSlib.InformationTheory.FinDist._sizeOf_inst\nTCSlib.InformationTheory.FinDist.collision\nTCSlib.InformationTheory.FinDist.instCoeFunForallReal\nTCSlib.InformationTheory.FinDist.map\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\nTCSlib.InformationTheory.FinDist.probTrue\nTCSlib.InformationTheory.FinDist.prod\nTCSlib.InformationTheory.FinDist.uniform\nTCSlib.InformationTheory.statDist\nTuring.Action._sizeOf_1\nTuring.Action._sizeOf_inst\nTuring.Action.apply\nTuring.Action.apply.match_1\nTuring.Action.mapState\nTuring.Action.mk._flat_ctor\nTuring.Cfg._sizeOf_1\nTuring.Cfg._sizeOf_inst\nTuring.Cfg.ext.match_1\nTuring.Cfg.init\nTuring.Cfg.inputSymbol\nTuring.Cfg.mapState\nTuring.Cfg.mk._flat_ctor\nTuring.Cfg.ofWords\nTuring.Cfg.select\nTuring.Cfg.workTapeSymbols\nTuring.CodeTM._sizeOf_1\nTuring.CodeTM._sizeOf_inst\nTuring.CodeTM.mk._flat_ctor\nTuring.CodeTM.serialize\nTuring.CodeTM.toFinTM\nTuring.EffectiveMachineCode._sizeOf_1\nTuring.EffectiveMachineCode._sizeOf_inst\nTuring.EffectiveMachineCode.mk._flat_ctor\nTuring.FinTM.Computes\nTuring.FinTM.ComputesFunInTime\nTuring.FinTM.ComputesFunInTimeVia\nTuring.FinTM.ComputesInTime\nTuring.FinTM.VirtualTag\nTuring.FinTM._sizeOf_1\nTuring.FinTM._sizeOf_inst\nTuring.FinTM.appendBitTM\nTuring.FinTM.branchTM\nTuring.FinTM.branchTM.match_1\nTuring.FinTM.bufferTape\nTuring.FinTM.bufferedCompTM\nTuring.FinTM.bufferedCompTM.match_1\nTuring.FinTM.bufferedFirstCfg\nTuring.FinTM.bufferedScanCfg\nTuring.FinTM.bufferedSecondCfg\nTuring.FinTM.callEntry\nTuring.FinTM.callExit\nTuring.FinTM.callTM\nTuring.FinTM.callTM.match_1\nTuring.FinTM.condTM\nTuring.FinTM.condTM.match_1\nTuring.FinTM.constTM\nTuring.FinTM.controlAction\nTuring.FinTM.emitAction\nTuring.FinTM.idTM\nTuring.FinTM.idTM.match_1\nTuring.FinTM.ifEqTM\nTuring.FinTM.ifEqTM.match_1\nTuring.FinTM.incFixedTM\nTuring.FinTM.incFixedTM.match_1\nTuring.FinTM.incFixedTM.match_3\nTuring.FinTM.indexedVisit\nTuring.FinTM.leftAction\nTuring.FinTM.leftCfg\nTuring.FinTM.lengthBitsTM\nTuring.FinTM.lengthBitsTM.match_1\nTuring.FinTM.mk._flat_ctor\nTuring.FinTM.pairExtractTM\nTuring.FinTM.pairExtractTM.match_1\nTuring.FinTM.pairExtractTM.match_3\nTuring.FinTM.pairExtractTM.match_5\nTuring.FinTM.pairLenCheckTM\nTuring.FinTM.pairValidTM\nTuring.FinTM.pairValidTM.match_1\nTuring.FinTM.polyBitsTM\nTuring.FinTM.polyUnaryTM\nTuring.FinTM.polyUnaryTM.match_1\nTuring.FinTM.prependTM\nTuring.FinTM.prependTM.match_1\nTuring.FinTM.redirectTM\nTuring.FinTM.redirectTM.match_1\nTuring.FinTM.redirectTM.match_3\nTuring.FinTM.rewind_scan.match_1\nTuring.FinTM.rightAction\nTuring.FinTM.rightCfg\nTuring.FinTM.splitSolveTM\nTuring.FinTM.splitSolveWithTM\nTuring.FinTM.stripLastTM\nTuring.FinTM.stripLastTM_computes.match_1\nTuring.FinTM.sweepAct\nTuring.FinTM.sweepCfg\nTuring.FinTM.sweepFold\nTuring.FinTM.sweepFold._sunfold\nTuring.FinTM.sweepFold._unsafe_rec\nTuring.FinTM.sweepFold.match_1\nTuring.FinTM.sweepRevCfg\nTuring.FinTM.sweepTape\nTuring.FinTM.tapeBlocks\nTuring.FinTM.timedCondTM\nTuring.FinTM.timedCondTM.match_1\nTuring.FinTM.toCodeTM\nTuring.FinTM.toCodeTM.match_1\nTuring.FinTM.unaryTokenTM\nTuring.FinTM.unaryTokenTM.match_1\nTuring.FinTM.virtualMove\nTuring.FinTM.virtualNextTag\nTuring.FinTM.virtualNextTag.match_1\nTuring.MachineCode._sizeOf_1\nTuring.MachineCode._sizeOf_inst\nTuring.MachineCode.mk._flat_ctor\nTuring.MultiTapeTM.AgreeOn\nTuring.MultiTapeTM.ComputableInTimeAndSpace\nTuring.MultiTapeTM.ComputesFunInTimeAndSpace\nTuring.MultiTapeTM.ComputesInTimeAndSpace\nTuring.MultiTapeTM.DecidableInTimeAndSpace\nTuring.MultiTapeTM._sizeOf_1\nTuring.MultiTapeTM._sizeOf_inst\nTuring.MultiTapeTM.haltsAtStep\nTuring.MultiTapeTM.indicator\nTuring.MultiTapeTM.initCfg\nTuring.MultiTapeTM.mk._flat_ctor\nTuring.MultiTapeTM.outputSymbol\nTuring.MultiTapeTM.relabelState\nTuring.MultiTapeTM.runFrom\nTuring.MultiTapeTM.spaceUsed\nTuring.MultiTapeTM.spaceUsedByTape\nTuring.MultiTapeTM.step\nTuring.MultiTapeTM.step.match_1\nTuring.MultiTapeTM.visitedByTapeHead\nTuring.actionBits\nTuring.captureAction\nTuring.captureAction.match_1\nTuring.captureCfg\nTuring.dbl\nTuring.embedEmitCfg\nTuring.embedEmitRetTM\nTuring.embedEmitTM\nTuring.embedSilentCfg\nTuring.embedSilentRetTM\nTuring.embedSilentRetTM.match_1\nTuring.embedSilentTM\nTuring.emitAction\nTuring.emitCfg\nTuring.incFixed\nTuring.incFixed._sunfold\nTuring.incFixed._unsafe_rec\nTuring.incFixed.match_1\nTuring.instInhabitedCfg\nTuring.instInhabitedCfg.default\nTuring.moveInputPos\nTuring.optBoolBits\nTuring.optBoolBits.match_1\nTuring.optOptBoolBits\nTuring.optOptBoolBits.match_1\nTuring.optStateBits\nTuring.optStateBits.match_1\nTuring.pairDecode\nTuring.pairDecode._sunfold\nTuring.pairDecode._unsafe_rec\nTuring.pairDecode.match_1\nTuring.pairDiagTM\nTuring.pairDiagTM.match_1\nTuring.pairDiagTM.match_3\nTuring.pairEncode\nTuring.signBits\nTuring.signBits.match_1\nTuring.solveSplit\nTuring.solveSplitWith\nTuring.spaceUsedOfCfgs\nTuring.splitAtLastTrue\nTuring.splitAtLastTrue.match_1\nTuring.stateWord\nTuring.unaryFin\nTuring.unaryTokenSplit\nTuring.unaryTokenSplit._sunfold\nTuring.unaryTokenSplit._unsafe_rec\nTuring.unaryTokenSplit.match_1\nTuring.visitedOfCfgs\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.pairMapSnd.match_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.polyTimeComputable_unary.match_1_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterBump\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCfg\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterTape\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.FinTM.lengthBitsTM.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.MultiTapeTM.step.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.eval.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.subst.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Convention.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnAction\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedSlot\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.callTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallBankFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallCleared\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEmbeddedCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallIdleTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallInterval\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLayout\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightScan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSlots\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSpan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackMid\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopForwardCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyDispatch\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyImage\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyPadded\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodySource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1.splitter"
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
  Lean.logInfo m!"SEAL-INSTALL final/Cryptography_Pseudorandom_Functions_Asymptotic_Defs/strict-A part 1: {count}"

set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopControlAction\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCopyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCaptured\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelSource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHost_bound\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReady\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.List.filter.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCopyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyMove\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyUnaryTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPrefixCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2LeftIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2OneIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2RightIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2SmallIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2Words\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterSplitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extractCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairValidTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.polyUnaryTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.prependTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.rawStripTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.scanCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBank\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitLoop_result.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPos\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareReady\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreClean\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRewindTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitSafe\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitScratch\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitStep\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.stripCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.unaryTokenTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.splitAtLastTrue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.unaryTokenSplit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectAction\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedBranchCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedCondTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedControlCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedPadTM\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedReadyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.captureAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.controlCfg\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.idTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.ifEqTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Deterministic.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.FinTM.toCodeTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDecode.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagCfg\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Finite.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBit\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBuffer\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCell\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arDecode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arIndex\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arMoveCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPending\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReadCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReady\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpaceBlock\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpacePhase\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTail\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTape\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arWriteCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGSpan\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGWindow.mk._flat_ctor\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCost\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCross\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgLeftRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgRetract\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepBoundary\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepSymbol\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit.match_1\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.virtualNextTag.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Sweep.0.Turing.FinTM.sweepFold.match_1.splitter\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.combine\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.mergeTable"
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
  Lean.logInfo m!"SEAL-INSTALL final/Cryptography_Pseudorandom_Functions_Asymptotic_Defs/strict-A part 2: {count}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic oracle indistinguishability and pseudorandom functions

An oracle ensemble samples functions at each parameter. The next-query machine
sees the encoded history, uses one coin tape for the interaction, and runs within
an explicit query budget. The pseudorandom function contract combines an efficient
evaluator with indistinguishability from the random oracle [PS10, Definitions 96.1
and 96.2].

The concrete adversaries, random functions, and lazy runs come from [Gar26, §3.4].
The decoder treats malformed moves as rejection. A query after the budget is spent
also gives verdict `false` (foundation decision D7 of `PassShelatChapter2-4Plan.md`).

## Main definitions

* `TCSlib.Cryptography.OracleEnsemble` samples functions from finite seed types.
  `OracleEnsemble.random` uses the function table and `OracleEnsemble.keyed` uses a key.
* `TCSlib.Cryptography.OracleMove`, `decodeOracleMove`, and `encodeHist` specify the
  interface for a next-query machine. `buildTree` and `Complexity.NUPPT.toOracleAdversary`
  turn such a machine into a bounded query tree.
* `TCSlib.Cryptography.OracleEnsemble.Indist` gives the oracle indistinguishability
  condition. `TCSlib.Cryptography.PRF` packages that condition with efficient evaluation.

## Main results

* `TCSlib.Cryptography.acceptProb_random_eq_lazy` equates the two descriptions of a
  random function, by its table and by lazy sampling [PS10, §3.8.1].
* `Complexity.NUPPT.toOracleAdversary_boundedBy` gives the query bound.
* `TCSlib.Cryptography.OracleEnsemble.indist_iff` expresses the contract through
  negligible advantage. `TCSlib.Cryptography.oracle_hybrid_lemma` gives the
  finite hybrid bound for oracle ensembles.
* `TCSlib.Cryptography.prfAdv_toOracleAdversary` and `PRF.negligible_prfAdv`
  connect the PRF contract to the concrete advantage.
* `TCSlib.Cryptography.prfAdv_toOracleAdversary_out` and
  `OracleEnsemble.Indist.negligible_prfAdv` do so at `ℓ₂(n)`-bit outputs (ruling B3); the two
  `n`-bit results are their cases `ℓ₂ = var`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8.1 and §3.8.2, Definitions 96.1 and 96.2.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (Definitions 3.6–3.9).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Oracle ensembles and random functions [PS10, §3.8.1, Definition 96.1] -/

/-- An **oracle ensemble** [PS10, Definition 96.1]: for every parameter `n` a probability
distribution over functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, given (D6/D7) as the pushforward
of the uniform distribution on a finite seed type `σ n` along a sampler `O n`. For the
random-function ensemble the seed is the function table itself (exponentially long, which is
immaterial at the concrete level); for a keyed family the seed is the key.

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- The seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- The sampler: the oracle determined by a seed. -/
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

attribute [instance] OracleEnsemble.fintype

/-- **The random function ensemble** `RF_n` [PS10, §3.8.1, combinatorial description]: the
uniform distribution on functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, sampled by its function
table (the "long array" of the text; `randomFunction I O = id`). The text's count
`2^{n 2^n}` of random functions is `Fintype.card_fun`. -/
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂ where
  σ n := (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
  O _ := randomFunction _ _

/-- **A keyed family as an oracle ensemble**: `{s ← U_n : f_s}` for a family
`F n : {0,1}^n → {0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}` (the first clause of the pseudorandomness
condition of [PS10, Definition 96.2]); the seed is the `n`-bit key. -/
def OracleEnsemble.keyed {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    OracleEnsemble ℓ₁ ℓ₂ where
  σ n := Fin n → Bool
  O n := F n

/-- Unfolding: the random-function ensemble samples by the identity on tables. -/
@[simp] theorem OracleEnsemble.random_O (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (R : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    (OracleEnsemble.random ℓ₁ ℓ₂).O n R = R :=
  randomFunction_apply _ _ R

/-- Unfolding: the keyed ensemble samples by `F n`. -/
@[simp] theorem OracleEnsemble.keyed_O {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (OracleEnsemble.keyed F).O n s = F n s := rfl

/-- Acceptance against the random oracle ensemble is acceptance against a uniform function
table, with the same oracle adversary and its coins. -/
theorem OracleEnsemble.acceptProb_random_eq {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (randomFunction (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) (oracleDist A) :=
  rfl

/-- **The two descriptions of a random function agree** [PS10, §3.8.1, "both of the above
descriptions of a random function give rise to identical distributions"] (Claim-95.b): for an
oracle adversary making at most `q` queries, the probability of accepting with the function
table `RF_n` as oracle equals the probability of accepting when every *new* query is answered
by a fresh uniform value and repeated queries by the recorded answer (the computational
description, `QueryTree.evalLazy` with `q` fresh values `extendStream W`).

**Proof sketch.** Both sides are averages over the adversary's coins `r` (Fubini,
`uprob_prod` after swapping the factors with `uprob_prod_comm`); for each fixed `r` the two
inner probabilities agree by the concrete lazy-sampling theorem `QueryTree.uprob_evalLazy`
applied to the tree `A r`. -/
theorem acceptProb_random_eq_lazy {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) {q : ℕ}
    (hA : A.BoundedBy q) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (fun W : Fin q → (Fin (ℓ₂.eval n) → Bool) => extendStream W) (lazyDist A) := by
  rw [acceptProb_def, acceptProb_def,
    uprob_prod_comm (fun R (r : ρ) => oracleDist A ((OracleEnsemble.random ℓ₁ ℓ₂).O n R) r = true),
    uprob_prod_comm (fun W (r : ρ) => lazyDist A (extendStream W) r = true),
    uprob_prod, uprob_prod]
  congr 1
  funext r
  simp only [OracleEnsemble.random_O, oracleDist_apply, lazyDist_apply]
  exact (QueryTree.uprob_evalLazy (· = true) ((OracleAdversary.boundedBy_iff A q).1 hA r)).symm

/-! ### Next-query machines as oracle adversaries (D7) -/

/-- A move of a next-query oracle machine: either the next query `x ∈ {0,1}^{ℓ₁}` or the
final verdict `b`. -/
inductive OracleMove (ℓ₁ : ℕ)
  /-- Ask the oracle at `x`. -/
  | query (x : Fin ℓ₁ → Bool)
  /-- Stop with the verdict `b`. -/
  | ret (b : Bool)

/-- Decoding of a machine output as a move: `⟨[false], x⟩` with `x` an `ℓ₁`-bit string is the
query `x`; the two-bit string `[true, b]` is the verdict `b`; any other output is the verdict
`false` (D7: ill-formed outputs count as rejection). -/
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁ :=
  match pairDecode w, w with
  | some ([false], x), _ => match decodeFin ℓ₁ x with
    | some x => .query x
    | none => .ret false
  | _, [true, b] => .ret b
  | _, _ => .ret false

/-- The two-bit word `[true, b]` is not a pair: its decoding would start with a doubled bit
(at least four bits) or with the separator `01`. -/
theorem pairDecode_true_two (b : Bool) : pairDecode [true, b] = none := by
  cases h : pairDecode [true, b] with
  | none => rfl
  | some p =>
    obtain ⟨u, v⟩ := p
    have hz := eq_pairEncode_of_pairDecode _ u v h
    rw [pairEncode_eq] at hz
    cases u with
    | nil => simp at hz
    | cons x u =>
      have hl := congrArg List.length hz
      simp only [List.length_cons, List.length_append, List.flatMap_cons, List.length_nil] at hl
      omega

/-- Decoding a pair `⟨[false], x⟩`: the query `x` when `x` has `ℓ₁` bits, else the verdict
`false`: `decodeOracleMove ℓ₁ (pairEncode [false] x) =
match decodeFin ℓ₁ x with | some y => .query y | none => .ret false`. -/
theorem decodeOracleMove_pairEncode_false (ℓ₁ : ℕ) (x : List Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] x) =
      match decodeFin ℓ₁ x with
      | some y => .query y
      | none => .ret false := by
  unfold decodeOracleMove
  rw [pairDecode_pairEncode, pairEncode_eq]
  rfl

/-- Decoding the two-bit word `[true, b]`: the verdict `b`,
`decodeOracleMove ℓ₁ [true, b] = .ret b`. -/
theorem decodeOracleMove_true_two (ℓ₁ : ℕ) (b : Bool) :
    decodeOracleMove ℓ₁ [true, b] = .ret b := by
  unfold decodeOracleMove
  rw [pairDecode_true_two]

/-- Decoding a well-formed query word: for every `ℓ₁`-bit string `x` (`ℓ₁ = 0` included),
`decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x`. -/
theorem decodeOracleMove_pairEncode_ofFn (ℓ₁ : ℕ) (x : Fin ℓ₁ → Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x := by
  rw [decodeOracleMove_pairEncode_false, decodeFin_ofFn]

/-- Decoding a query-shaped word of the wrong length: if `|x| ≠ ℓ₁` then
`decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false`. -/
theorem decodeOracleMove_pairEncode_false_of_length_ne (ℓ₁ : ℕ) {x : List Bool}
    (hx : x.length ≠ ℓ₁) : decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false := by
  rw [decodeOracleMove_pairEncode_false]
  cases h : decodeFin ℓ₁ x with
  | none => rfl
  | some y => exact absurd (length_eq_of_decodeFin_eq_some h) hx

/-- **The malformed branch**: a word that is neither a query-shaped pair `⟨[false], x⟩` (for any
string `x`) nor a two-bit verdict word `[true, b]` decodes to the verdict `false`:
`decodeOracleMove ℓ₁ w = .ret false`. Together with `decodeOracleMove_pairEncode_ofFn`,
`decodeOracleMove_pairEncode_false_of_length_ne` and `decodeOracleMove_true_two` this covers every
word, for every `ℓ₁`.

**Proof sketch.** Along the match of `decodeOracleMove`: a decoding
`pairDecode w = some ([false], x)` gives `w = ⟨[false], x⟩` (`eq_pairEncode_of_pairDecode`),
excluded; the word `[true, b]` is excluded; the remaining branch is `.ret false`. -/
theorem decodeOracleMove_of_ne (ℓ₁ : ℕ) {w : List Bool} (hq : ∀ x, w ≠ pairEncode [false] x)
    (hv : ∀ b, w ≠ [true, b]) : decodeOracleMove ℓ₁ w = .ret false := by
  unfold decodeOracleMove
  split
  · rename_i w' o w'' x hx
    exact absurd (eq_pairEncode_of_pairDecode w' _ _ hx) (hq x)
  · rename_i o w' b hp
    exact absurd rfl (hv b)
  · rfl

/-- The encoding of the history of (query, answer) pairs handed to a next-query machine: the
nested pair `⟨⟨x₁, y₁⟩, ⟨⟨x₂, y₂⟩, ⟨…, []⟩⟩⟩`. -/
def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- The empty history is encoded as the empty string: `encodeHist [] = []`. -/
theorem encodeHist_nil {ℓ₁ ℓ₂ : ℕ} :
    encodeHist ([] : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) = [] :=
  rfl

/-- A history is encoded pair by pair:
`encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h)`. -/
theorem encodeHist_cons {ℓ₁ ℓ₂ : ℕ} (p : (Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))
    (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
  rfl

/-- The query tree of a next-query function `next` (the machine's move on a history) with the
query budget `q`, started from the history `hist`: a verdict stops; a query within budget
becomes a `query` node whose continuation appends the answer to the history; a query when the
budget is exhausted is the forced verdict `false` (D7). -/
def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match next hist with
    | .ret b => .ret b
    | .query _ => .ret false
  | q + 1, hist => match next hist with
    | .ret b => .ret b
    | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))

section BuildTree

variable {ℓ₁ ℓ₂ : ℕ} {next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁}
  {hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))}

/-- With the budget spent, a verdict stops the tree: `buildTree next 0 hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_zero_of_ret {b : Bool} (h : next hist = .ret b) :
    buildTree next 0 hist = .ret b := by
  rw [buildTree, h]

/-- With the budget spent, a query gives the forced verdict `false`:
`buildTree next 0 hist = ret false` when `next hist = query x`. -/
theorem buildTree_zero_of_query {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next 0 hist = .ret false := by
  rw [buildTree, h]

/-- Within budget, a verdict stops the tree: `buildTree next (q + 1) hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_succ_of_ret {q : ℕ} {b : Bool} (h : next hist = .ret b) :
    buildTree next (q + 1) hist = .ret b := by
  rw [buildTree, h]

/-- Within budget, a query becomes a query node whose continuation appends the answer:
`buildTree next (q + 1) hist = query x (fun o => buildTree next q (hist ++ [(x, o)]))` when
`next hist = query x`. -/
theorem buildTree_succ_of_query {q : ℕ} {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next (q + 1) hist = .query x (fun o => buildTree next q (hist ++ [(x, o)])) := by
  rw [buildTree, h]

end BuildTree

/-- The tree built with budget `q` makes at most `q` queries, from every starting history. -/
theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      (buildTree next q hist).BoundedBy q
  | 0, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_zero_of_ret h]; exact QueryTree.boundedBy_ret b 0
    | query x => rw [buildTree_zero_of_query h]; exact QueryTree.boundedBy_ret false 0
  | q + 1, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_succ_of_ret h]; exact QueryTree.boundedBy_ret b (q + 1)
    | query x =>
      rw [buildTree_succ_of_query h]
      exact (QueryTree.boundedBy_query_succ x _ q).2
        fun o => buildTree_boundedBy next q (hist ++ [(x, o)])

/-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). The
machine `D(1^n, ·)` is run, with one random tape `r` for the whole interaction, on the
encoded history; its output is decoded as a query or a verdict. -/
def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []

/-- The tree of `D` on the coins `r` is built from the empty history, the next move being `D`'s
output on the encoded history, decoded:
`D.toOracleAdversary n ℓ₁ ℓ₂ q r =
buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []`. -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_eq (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ)
    (r : D.Coins n) :
    D.toOracleAdversary n ℓ₁ ℓ₂ q r =
      buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q [] :=
  rfl

/-- The oracle adversary of a next-query machine with budget `q` makes at most `q` queries on
every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggmBits_dist`).
Induction on the budget (`buildTree_boundedBy`). -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q :=
  (OracleAdversary.boundedBy_iff _ q).2 fun r => by
    rw [NUPPT.toOracleAdversary_eq]
    exact buildTree_boundedBy _ q []

/-! ### Oracle indistinguishability [PS10, Definition 96.1] -/

/-- **Oracle indistinguishability** [PS10, Definition 96.1]: `{O_n} ≈ {O'_n}` iff for every
non-uniform PPT oracle machine `D` (a next-query `NUPPT`) and every polynomial query budget
`q`, the function `n ↦ |Pr[F ← O_n : D^F(1^n) = 1] − Pr[F ← O'_n : D^F(1^n) = 1]|` is
negligible, where `D^F(1^n)` is the run of the query tree `D.toOracleAdversary n ℓ₁(n) ℓ₂(n) q(n)`
against `F`. (The text writes `{O'_n} ≈ {O'_n}`, a typo.)

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
def OracleEnsemble.Indist {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
    distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))

/-- Oracle ensembles are indistinguishable iff the oracle advantage is negligible for
each next-query machine and polynomial query budget. -/
theorem OracleEnsemble.indist_iff {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) :
    O.Indist O' ↔ ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
      distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) :=
  Iff.rfl

/-- **Reflexivity of oracle indistinguishability** (non-vacuity of
[PS10, Definition 96.1]): every oracle ensemble is indistinguishable from itself, the
advantage being identically `0`. -/
theorem OracleEnsemble.Indist.refl {ℓ₁ ℓ₂ : PolyExpr} (O : OracleEnsemble ℓ₁ ℓ₂) : O.Indist O := by
  intro D q
  have h : (fun n => distAdv (O.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) = fun _ => 0 := by
    funext n
    simp [distAdv_def]
  rw [h]
  exact negligible_zero

/-- **Symmetry of oracle indistinguishability**: the advantage is symmetric in the two
ensembles (`abs_sub_comm`). -/
theorem OracleEnsemble.Indist.symm {ℓ₁ ℓ₂ : PolyExpr} {O O' : OracleEnsemble ℓ₁ ℓ₂}
    (h : O.Indist O') : O'.Indist O := by
  intro D q
  have e : (fun n => distAdv (O'.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) =
      fun n => distAdv (O.O n) (O'.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) := by
    funext n
    rw [distAdv_def, distAdv_def]
    exact abs_sub_comm _ _
  rw [e]
  exact h D q

/-- **Transitivity of oracle indistinguishability** (the two-step case of the hybrid lemma
for oracles, [PS10, §3.8.2, "oracle indistinguishability satisfies … the Hybrid Lemma"]): the
advantage between `O` and `O''` is at most the sum of the advantages between `O, O'` and
`O', O''` (triangle inequality `abs_sub_le`), and sums of negligible functions are negligible
(`Negligible.add`, `Negligible.mono`). -/
theorem OracleEnsemble.Indist.trans {ℓ₁ ℓ₂ : PolyExpr} {O O' O'' : OracleEnsemble ℓ₁ ℓ₂}
    (h₁ : O.Indist O') (h₂ : O'.Indist O'') : O.Indist O'' := by
  intro D q
  refine ((h₁ D q).add (h₂ D q)).mono ⟨0, fun n _ => ?_⟩
  simp only [distAdv_def, abs_abs]
  exact (abs_sub_le _ _ _).trans (le_abs_self _)

/-- **The hybrid lemma for oracles** [PS10, §3.8.2, "oracle indistinguishability satisfies …
the Hybrid Lemma"] (Claim-96.b), at one parameter: if the oracle adversary `A` distinguishes
the oracle distributions `H 0` and `H m` with advantage `ε`, then it distinguishes some
consecutive pair `H i, H (i+1)` (`i < m`) with advantage at least `ε / m`. Apply the
finite hybrid bound `exists_hybrid_gap` to the acceptance probabilities for `oracleDist A`. -/
theorem oracle_hybrid_lemma {σ : Type*} {I O : Type} {ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (H : ℕ → σ → (I → O)) (A : OracleAdversary ρ I O) :
    ∃ i < m, distAdv (H 0) (H m) (oracleDist A) / m ≤ distAdv (H i) (H (i + 1)) (oracleDist A) := by
  simpa only [distAdv_def] using exists_hybrid_gap (fun i => acceptProb (H i) (oracleDist A)) hm

/-! ### Pseudorandom functions [PS10, Definition 96.2] -/

/-- **Pseudorandom function family** [PS10, Definition 96.2]: a family
`{f_s : {0,1}^{|s|} → {0,1}^{|s|}}` given as `F n : {0,1}^n → {0,1}^n → {0,1}^n` (key, input,
output) is pseudorandom iff (1) *easy to compute*: a polynomial-time string function computes
`f_s(x)` from the pair `⟨s, x⟩`; (2) *pseudorandom*: the keyed oracle ensemble `{s ← U_n : f_s}`
is oracle-indistinguishable from the random functions `{F ← RF_n : F}`.

**Deviation:** clause (1) is a deterministic polynomial-time evaluator on `⟨s, x⟩` instead of
a PPT computing `f_s(x)` with probability one (equivalent by `Complexity.NUPPT.Computes` and
`ofPolyTimeUniform`, as for `FunFamily.Easy`); the key length is the parameter `n`
(`{0,1}^{|s|}` with `|s| = n`). -/
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)

/-- **The PRF advantage at `ℓ₂(n)`-bit outputs** (the advantage of [PS10, Definition 96.2],
clause (2), "with `ℓ`-bit outputs"): for a keyed family `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ₂(n)}`,
the advantage of the next-query machine `D` with budget `q` between the keyed ensemble and the
random functions with `ℓ₂(n)`-bit outputs is the concrete PRF advantage of [Gar26, Definition 3.9]:
`distAdv ((keyed F).O n) ((random var ℓ₂).O n) (oracleDist D^{n,ℓ₂(n),q}) =
prfAdv (F n) D^{n,ℓ₂(n),q}` (definitional: `prfAdv F A = distAdv F (randomFunction I O)
(oracleDist A)`). -/
theorem prfAdv_toOracleAdversary_out {ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).O n)
        ((OracleEnsemble.random .var ℓ₂).O n)
        (oracleDist (D.toOracleAdversary n n (ℓ₂.eval n) q)) =
      prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) q) := by
  rw [prfAdv_def]
  rfl

/-- **Pseudorandomness at `ℓ₂(n)`-bit outputs, unfolded** ([PS10, Definition 96.2], clause (2),
"with `ℓ`-bit outputs"): if the keyed ensemble of `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ₂(n)}` is
oracle-indistinguishable from the random functions with `ℓ₂(n)`-bit outputs, then every
next-query machine `D` with every polynomial budget `q` has negligible concrete PRF advantage:
`Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n ℓ₂(n) q(n))`. This is the form in
which a consumer of an `ℓ`-output PRF (such as `SecureComputation.PRFOut`, whose clause (2) is
the hypothesis) reads it. -/
theorem OracleEnsemble.Indist.negligible_prfAdv {ℓ₂ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist
      (OracleEnsemble.random .var ℓ₂))
    (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) (q.eval n)) :=
  (congrArg Negligible (funext fun n => prfAdv_toOracleAdversary_out F D n (q.eval n))).mp
    (hF D q)

/-- The advantage of the next-query machine `D` with budget `q` between the keyed family `F`
and the random functions is the concrete PRF advantage `prfAdv` of [Gar26, Definition 3.9]
(definitional: `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`). -/
theorem prfAdv_toOracleAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).O n) ((OracleEnsemble.random .var .var).O n)
        (oracleDist (D.toOracleAdversary n n n q)) =
      prfAdv (F n) (D.toOracleAdversary n n n q) :=
  prfAdv_toOracleAdversary_out (ℓ₂ := .var) F D n q

/-- **Pseudorandomness unfolded**: for a PRF `F`, every next-query machine `D` with every
polynomial budget `q` has negligible concrete PRF advantage `prfAdv (F n) (D^{(q n)})` — the
form in which the Garg-layer reductions consume [PS10, Definition 96.2]. -/
theorem PRF.negligible_prfAdv {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) :=
  hF.pseudorandom.negligible_prfAdv D q

end TCSlib.Cryptography


set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "Complexity.NUPPT.Computes\nComplexity.NUPPT.Uniform\nComplexity.NUPPT._sizeOf_1\nComplexity.NUPPT._sizeOf_inst\nComplexity.NUPPT.advInput\nComplexity.NUPPT.adviceLen\nComplexity.NUPPT.coinLen\nComplexity.NUPPT.coinsCongr\nComplexity.NUPPT.coinsEquivPoly\nComplexity.NUPPT.coinsEquiv_ofPolyTime\nComplexity.NUPPT.coinsEquiv_ofPolyTimeUniform\nComplexity.NUPPT.distinguisher\nComplexity.NUPPT.distinguisherL\nComplexity.NUPPT.inverter\nComplexity.NUPPT.inverterLit\nComplexity.NUPPT.mk._flat_ctor\nComplexity.NUPPT.ofPolyTime\nComplexity.NUPPT.ofPolyTimeUniform\nComplexity.NUPPT.output\nComplexity.NUPPT.predictor\nComplexity.NUPPT.runAt\nComplexity.NUPPT.runAtL\nComplexity.NUPPT.runLit\nComplexity.NUPPT.timeBound\nComplexity.PPT\nComplexity.PPT.ofPolyTime\nComplexity.PPT.toNUPPT\nComplexity.PolyBound\nComplexity.PolyExpr._sizeOf_1\nComplexity.PolyExpr._sizeOf_inst\nComplexity.PolyExpr.eval._sunfold\nComplexity.PolyExpr.eval._unsafe_rec\nComplexity.PolyExpr.eval.match_1\nComplexity.PolyExpr.normal\nComplexity.PolyExpr.subst\nComplexity.PolyExpr.subst._sunfold\nComplexity.PolyExpr.subst._unsafe_rec\nComplexity.PolyExpr.subst.match_1\nComplexity.PolyTimeComputable\nComplexity.TimeConstructible\nComplexity.instDecidableEqPolyExpr\nComplexity.instDecidableEqPolyExpr.decEq\nComplexity.instDecidableEqPolyExpr.decEq._sunfold\nComplexity.instDecidableEqPolyExpr.decEq._unsafe_rec\nComplexity.instDecidableEqPolyExpr.decEq.match_1\nComplexity.instReprPolyExpr\nComplexity.instReprPolyExpr.repr\nComplexity.instReprPolyExpr.repr._sunfold\nComplexity.instReprPolyExpr.repr._unsafe_rec\nComplexity.instReprPolyExpr.repr.match_1\nComplexity.pairFstD\nComplexity.pairMapSnd\nComplexity.pairMapSnd.match_1\nComplexity.pairSndD\nComplexity.polyTimeComputable_unary.match_1_1\nTCSlib.Cryptography.FunFamily.blocks\nTCSlib.Cryptography.Games.OracleComp.AllOutputs\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\nTCSlib.Cryptography.Games.OracleComp._sizeOf_inst\nTCSlib.Cryptography.Games.OracleComp.bind\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\nTCSlib.Cryptography.Games.OracleComp.call\nTCSlib.Cryptography.Games.OracleComp.instMonad\nTCSlib.Cryptography.Games.OracleComp.liftLeft\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\nTCSlib.Cryptography.Games.OracleComp.liftRight\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_inst\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\nTCSlib.Cryptography.HardcoreBit.PushesUniform\nTCSlib.Cryptography.Negligible\nTCSlib.Cryptography.Noticeable\nTCSlib.Cryptography.OracleAdversary.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy\nTCSlib.Cryptography.QueryTree.BoundedBy._sunfold\nTCSlib.Cryptography.QueryTree.BoundedBy._unsafe_rec\nTCSlib.Cryptography.QueryTree.BoundedBy.match_1\nTCSlib.Cryptography.QueryTree.eval\nTCSlib.Cryptography.QueryTree.eval._sunfold\nTCSlib.Cryptography.QueryTree.eval._unsafe_rec\nTCSlib.Cryptography.QueryTree.eval.match_1\nTCSlib.Cryptography.QueryTree.evalLazy\nTCSlib.Cryptography.QueryTree.evalLazy._sunfold\nTCSlib.Cryptography.QueryTree.evalLazy._unsafe_rec\nTCSlib.Cryptography.QueryTree.evalLazy.match_1\nTCSlib.Cryptography.QueryTree.induct\nTCSlib.Cryptography.QueryTree.induct._sunfold\nTCSlib.Cryptography.QueryTree.induct._unsafe_rec\nTCSlib.Cryptography.QueryTree.induct.match_1\nTCSlib.Cryptography.QueryTree.noteQuery\nTCSlib.Cryptography.QueryTree.simulate\nTCSlib.Cryptography.QueryTree.simulate._sunfold\nTCSlib.Cryptography.QueryTree.simulate._unsafe_rec\nTCSlib.Cryptography.acceptProb\nTCSlib.Cryptography.blocksEquivX\nTCSlib.Cryptography.coinBlock\nTCSlib.Cryptography.coinBlock_flatten.match_1_1\nTCSlib.Cryptography.decodeFin\nTCSlib.Cryptography.distAdv\nTCSlib.Cryptography.extendStream\nTCSlib.Cryptography.invProb\nTCSlib.Cryptography.invProbOpt\nTCSlib.Cryptography.lazyDist\nTCSlib.Cryptography.oracleDist\nTCSlib.Cryptography.padFin\nTCSlib.Cryptography.predProb\nTCSlib.Cryptography.prfAdv\nTCSlib.Cryptography.randomFunction\nTCSlib.Cryptography.uexp\nTCSlib.Cryptography.uprob\nTCSlib.Cryptography.xorPerm\nTCSlib.InformationTheory.FinDist.HasMinEntropy\nTCSlib.InformationTheory.FinDist._sizeOf_1\nTCSlib.InformationTheory.FinDist._sizeOf_inst\nTCSlib.InformationTheory.FinDist.collision\nTCSlib.InformationTheory.FinDist.instCoeFunForallReal\nTCSlib.InformationTheory.FinDist.map\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\nTCSlib.InformationTheory.FinDist.probTrue\nTCSlib.InformationTheory.FinDist.prod\nTCSlib.InformationTheory.FinDist.uniform\nTCSlib.InformationTheory.statDist\nTuring.Action._sizeOf_1\nTuring.Action._sizeOf_inst\nTuring.Action.apply\nTuring.Action.apply.match_1\nTuring.Action.mapState\nTuring.Action.mk._flat_ctor\nTuring.Cfg._sizeOf_1\nTuring.Cfg._sizeOf_inst\nTuring.Cfg.ext.match_1\nTuring.Cfg.init\nTuring.Cfg.inputSymbol\nTuring.Cfg.mapState\nTuring.Cfg.mk._flat_ctor\nTuring.Cfg.ofWords\nTuring.Cfg.select\nTuring.Cfg.workTapeSymbols\nTuring.CodeTM._sizeOf_1\nTuring.CodeTM._sizeOf_inst\nTuring.CodeTM.mk._flat_ctor\nTuring.CodeTM.serialize\nTuring.CodeTM.toFinTM\nTuring.EffectiveMachineCode._sizeOf_1\nTuring.EffectiveMachineCode._sizeOf_inst\nTuring.EffectiveMachineCode.mk._flat_ctor\nTuring.FinTM.Computes\nTuring.FinTM.ComputesFunInTime\nTuring.FinTM.ComputesFunInTimeVia\nTuring.FinTM.ComputesInTime\nTuring.FinTM.VirtualTag\nTuring.FinTM._sizeOf_1\nTuring.FinTM._sizeOf_inst\nTuring.FinTM.appendBitTM\nTuring.FinTM.branchTM\nTuring.FinTM.branchTM.match_1\nTuring.FinTM.bufferTape\nTuring.FinTM.bufferedCompTM\nTuring.FinTM.bufferedCompTM.match_1\nTuring.FinTM.bufferedFirstCfg\nTuring.FinTM.bufferedScanCfg\nTuring.FinTM.bufferedSecondCfg\nTuring.FinTM.callEntry\nTuring.FinTM.callExit\nTuring.FinTM.callTM\nTuring.FinTM.callTM.match_1\nTuring.FinTM.condTM\nTuring.FinTM.condTM.match_1\nTuring.FinTM.constTM\nTuring.FinTM.controlAction\nTuring.FinTM.emitAction\nTuring.FinTM.idTM\nTuring.FinTM.idTM.match_1\nTuring.FinTM.ifEqTM\nTuring.FinTM.ifEqTM.match_1\nTuring.FinTM.incFixedTM\nTuring.FinTM.incFixedTM.match_1\nTuring.FinTM.incFixedTM.match_3\nTuring.FinTM.indexedVisit\nTuring.FinTM.leftAction\nTuring.FinTM.leftCfg\nTuring.FinTM.lengthBitsTM\nTuring.FinTM.lengthBitsTM.match_1\nTuring.FinTM.mk._flat_ctor\nTuring.FinTM.pairExtractTM\nTuring.FinTM.pairExtractTM.match_1\nTuring.FinTM.pairExtractTM.match_3\nTuring.FinTM.pairExtractTM.match_5\nTuring.FinTM.pairLenCheckTM\nTuring.FinTM.pairValidTM\nTuring.FinTM.pairValidTM.match_1\nTuring.FinTM.polyBitsTM\nTuring.FinTM.polyUnaryTM\nTuring.FinTM.polyUnaryTM.match_1\nTuring.FinTM.prependTM\nTuring.FinTM.prependTM.match_1\nTuring.FinTM.redirectTM\nTuring.FinTM.redirectTM.match_1\nTuring.FinTM.redirectTM.match_3\nTuring.FinTM.rewind_scan.match_1\nTuring.FinTM.rightAction\nTuring.FinTM.rightCfg\nTuring.FinTM.splitSolveTM\nTuring.FinTM.splitSolveWithTM\nTuring.FinTM.stripLastTM\nTuring.FinTM.stripLastTM_computes.match_1\nTuring.FinTM.sweepAct\nTuring.FinTM.sweepCfg\nTuring.FinTM.sweepFold\nTuring.FinTM.sweepFold._sunfold\nTuring.FinTM.sweepFold._unsafe_rec\nTuring.FinTM.sweepFold.match_1\nTuring.FinTM.sweepRevCfg\nTuring.FinTM.sweepTape\nTuring.FinTM.tapeBlocks\nTuring.FinTM.timedCondTM\nTuring.FinTM.timedCondTM.match_1\nTuring.FinTM.toCodeTM\nTuring.FinTM.toCodeTM.match_1\nTuring.FinTM.unaryTokenTM\nTuring.FinTM.unaryTokenTM.match_1\nTuring.FinTM.virtualMove\nTuring.FinTM.virtualNextTag\nTuring.FinTM.virtualNextTag.match_1\nTuring.MachineCode._sizeOf_1\nTuring.MachineCode._sizeOf_inst\nTuring.MachineCode.mk._flat_ctor\nTuring.MultiTapeTM.AgreeOn\nTuring.MultiTapeTM.ComputableInTimeAndSpace\nTuring.MultiTapeTM.ComputesFunInTimeAndSpace\nTuring.MultiTapeTM.ComputesInTimeAndSpace\nTuring.MultiTapeTM.DecidableInTimeAndSpace\nTuring.MultiTapeTM._sizeOf_1\nTuring.MultiTapeTM._sizeOf_inst\nTuring.MultiTapeTM.haltsAtStep\nTuring.MultiTapeTM.indicator\nTuring.MultiTapeTM.initCfg\nTuring.MultiTapeTM.mk._flat_ctor\nTuring.MultiTapeTM.outputSymbol\nTuring.MultiTapeTM.relabelState\nTuring.MultiTapeTM.runFrom\nTuring.MultiTapeTM.spaceUsed\nTuring.MultiTapeTM.spaceUsedByTape\nTuring.MultiTapeTM.step\nTuring.MultiTapeTM.step.match_1\nTuring.MultiTapeTM.visitedByTapeHead\nTuring.actionBits\nTuring.captureAction\nTuring.captureAction.match_1\nTuring.captureCfg\nTuring.dbl\nTuring.embedEmitCfg\nTuring.embedEmitRetTM\nTuring.embedEmitTM\nTuring.embedSilentCfg\nTuring.embedSilentRetTM\nTuring.embedSilentRetTM.match_1\nTuring.embedSilentTM\nTuring.emitAction\nTuring.emitCfg\nTuring.incFixed\nTuring.incFixed._sunfold\nTuring.incFixed._unsafe_rec\nTuring.incFixed.match_1\nTuring.instInhabitedCfg\nTuring.instInhabitedCfg.default\nTuring.moveInputPos\nTuring.optBoolBits\nTuring.optBoolBits.match_1\nTuring.optOptBoolBits\nTuring.optOptBoolBits.match_1\nTuring.optStateBits\nTuring.optStateBits.match_1\nTuring.pairDecode\nTuring.pairDecode._sunfold\nTuring.pairDecode._unsafe_rec\nTuring.pairDecode.match_1\nTuring.pairDiagTM\nTuring.pairDiagTM.match_1\nTuring.pairDiagTM.match_3\nTuring.pairEncode\nTuring.signBits\nTuring.signBits.match_1\nTuring.solveSplit\nTuring.solveSplitWith\nTuring.spaceUsedOfCfgs\nTuring.splitAtLastTrue\nTuring.splitAtLastTrue.match_1\nTuring.stateWord\nTuring.unaryFin\nTuring.unaryTokenSplit\nTuring.unaryTokenSplit._sunfold\nTuring.unaryTokenSplit._unsafe_rec\nTuring.unaryTokenSplit.match_1\nTuring.visitedOfCfgs\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.pairMapSnd.match_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Complexity.polyTimeComputable_unary.match_1_1.splitter\n_private.TCSlib.Complexity.ClassNP.PolyTimePairing.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterBump\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCarry.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterCfg\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._sunfold\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc._unsafe_rec\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterInc.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Complexity.counterTape\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.FinTM.lengthBitsTM.match_1.splitter\n_private.TCSlib.Complexity.ClassP.TimeConstructible.0.Turing.MultiTapeTM.step.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.eval.match_1.splitter\n_private.TCSlib.Complexity.Randomized.PolyExpr.0.Complexity.PolyExpr.subst.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Convention.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedActionCore.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnAction\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedReturnCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Embed.0.Turing.embedSlot\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.callTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallBankFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearCfg.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallClearTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallCleared\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEmbeddedCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallEvalTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFinishTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallHi._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallIdleTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallInterval\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLayout\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallLo.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallPairSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightScan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallRightTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSlots\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallSpan\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackMid\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTrackTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleEmbedding\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emCallTripleSelect\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.emLoopForwardCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyDispatch\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyImage\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyPadded\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodySource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopBorrowPos.match_1.splitter"
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
  Lean.logInfo m!"SEAL-VERIFY final/Cryptography_Pseudorandom_Functions_Asymptotic_Defs/strict-A part 1: {count}"

set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCall\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopControlAction\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopCopyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopDebit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFrame\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCaptured\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopFuelSource\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHostM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHost_bound\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReady\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopReplayTM\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopValue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopWrite.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_find_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loop_rewind_bounded.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.List.filter.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.CatalogPolyControl.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.EmitterP2State.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.SplitBodyState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.anyTrueTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyControlFintype.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCopyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._sunfold\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyCost._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyMove\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyTape\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPolyUnaryTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.catalogPrefixCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterCompareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2BodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2EraseTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2LeftIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2OneIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PairIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2PrepareTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2RightIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2SmallIndex\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2StateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterP2Words\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.emitterSplitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extractCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.extract_run.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.incFixedTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.lenCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.mapCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairCountTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairDupTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairExtractTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairMapTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.pairValidTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.polyUnaryTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.prependTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.rawStripTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.scanCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitAccept\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBank\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitBodyTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitCountCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitEmitTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitLoop_result.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPos\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareReady\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitPrepareTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreClean\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreScan\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRestoreTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitRewindTM\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitSafe\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitScratch\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.splitStep\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.stripCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.FinTM.unaryTokenTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.incFixed.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.splitAtLastTrue.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Primitives.0.Turing.unaryTokenSplit.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectAction\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectState.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.redirectTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedBranchCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedCondTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedControlCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedPadTM\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timedReadyCfg\n_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.captureAction.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.controlCfg\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.idTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Composition.0.Turing.FinTM.ifEqTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Configuration.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Deterministic.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.FinTM.toCodeTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDecode.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagCfg\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Encoding.0.Turing.pairDiagTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Finite.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBit\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arBuffer\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCell\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arCode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arDecode\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arIndex\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arMoveCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPending\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReadCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arReady\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpaceBlock\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arSpacePhase\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTail\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arTape\n_private.TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction.0.Turing.FinTM.arWriteCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGSpan\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.DGWindow.mk._flat_ctor\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_inst\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyTypeEquiv\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCost\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgCross\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgLeftRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgRetract\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dgTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepBoundary\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStart\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateDecidableEq\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepSymbol\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._sunfold\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._unsafe_rec\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit\n_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit.match_1\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.Action.apply.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.bufferedCompTM.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Simulation.0.Turing.FinTM.virtualNextTag.match_1.splitter\n_private.TCSlib.Complexity.TuringMachine.Sweep.0.Turing.FinTM.sweepFold.match_1.splitter\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.combine\n_private.TCSlib.Cryptography.Pseudorandom.Functions.LazySampling.0.TCSlib.Cryptography.QueryTree.mergeTable"
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
  Lean.logInfo m!"SEAL-VERIFY final/Cryptography_Pseudorandom_Functions_Asymptotic_Defs/strict-A part 2: {count}"
