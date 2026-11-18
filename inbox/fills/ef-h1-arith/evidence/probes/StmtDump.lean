import TCSlib.Cryptography.Candidates.ArithmeticDischarge
import TCSlib.Cryptography.Candidates.ExtendedEuclidMachine
import TCSlib.Cryptography.Candidates.PrimesInP

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  for m in #[`TCSlib.Cryptography.Candidates.ArithmeticDischarge, `TCSlib.Cryptography.Candidates.ExtendedEuclidMachine, `TCSlib.Cryptography.Candidates.PrimesInP] do
    let some idx := env.getModuleIdx? m | throwError "no module"
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if isPrivateName c then continue
      let some ci := env.find? c | continue
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | _ => "other"
      let ty ← liftTermElabM (ppExpr ci.type)
      logInfo m!"STMT {m} {kind} {c} : {ty}"
