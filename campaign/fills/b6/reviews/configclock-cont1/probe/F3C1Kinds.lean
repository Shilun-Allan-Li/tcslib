import TCSlib.Complexity.SpaceComplexity.WindowClock
import Lean
open Lean Meta Elab Command in
elab "#kinds " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let env ← getEnv
    let some ci := env.find? n | logInfo m!"{n}: not found"
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    let red ← liftCoreM <| getReducibilityStatus n
    let proj := (env.getProjectionFnInfo? n).isSome
    let inst := isInstanceCore env n
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    logInfo m!"KIND {n}: {kind}; reducibility {repr red}; projection {proj}; instance {inst}; module {mod}"
#kinds Turing.Action Turing.Cfg Turing.Cfg.inputSymbol Turing.Cfg.workTapeSymbols Turing.FinTM Turing.FinTM.State Turing.FinTM.bufferTape Turing.FinTM.configBound Turing.FinTM.fintypeState Turing.FinTM.k Turing.MultiTapeTM Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.step Turing.MultiTapeTM.tr Turing.RecSym Turing.SweepPhase Turing.cfgRecord Turing.clearTM Turing.copyMapTM Turing.joinFields Turing.moveInputPos Turing.posWidth Turing.recordLength Turing.tapeAction Turing.wordPatch Turing.fieldsTape Turing.RecordAt Turing.skipTM Turing.skipBackTM
