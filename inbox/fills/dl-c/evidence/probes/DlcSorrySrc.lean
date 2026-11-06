import TCSlib.Cryptography.Candidates.ElGamal
open Lean Meta Elab Command

/-- The declarations in the dependency closure of `root` whose own value mentions `sorryAx`. -/
elab "#dlc_sorry_src " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut direct : Array Name := #[]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    if cs.contains ``sorryAx then direct := direct.push n
    for c in cs do
      if !seen.contains c then stack := stack.push c
  logInfo m!"{root}: direct sorry users in the closure: {direct}"

#dlc_sorry_src TCSlib.Cryptography.Candidates.elGamal_secure
