import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.Seam
import Lean
open Lean Meta Elab Command in
elab "#simpunfold " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let st ← liftTermElabM getSimpTheorems
    let unf := st.isDeclToUnfold n
    let eqs := st.isLemma (.decl n) || st.lemmaNames.contains (.decl (n ++ `eq_1)) || st.lemmaNames.contains (.decl (n ++ `eq_def))
    logInfo m!"SIMPUNFOLD {n}: toUnfold {unf}; eqn lemma in simp set {eqs}"
#simpunfold Turing.Action.apply Turing.Cfg.Stopped Turing.Cfg.init Turing.Cfg.inputSymbol Turing.Cfg.mapState Turing.Cfg.workTapeSymbols Turing.CodeNDTM.toFinNDTM Turing.FinNDTM.AcceptsWithin Turing.FinTM.ComputesInTime Turing.FinTM.bufferTape Turing.FinTM.controlAction Turing.MultiTapeTM.initCfg Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.step Turing.NDTM.HaltsWithin Turing.NDTM.initCfg Turing.NDTM.replayTM Turing.NDTM.runWith Turing.NDTM.stepWith Turing.NDTM.withChoiceTape Turing.clockCfg Turing.copyTM Turing.embedSilentCfg Turing.embedSilentTM Turing.incFixed Turing.incrementTM Turing.moveInputPos Turing.pairEncode Turing.phaseHostTM Turing.seamCompTM₂ Turing.wordPatch 
