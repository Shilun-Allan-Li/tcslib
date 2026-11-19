import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity

/-! gsw-6b-u15-u17, C5 (the u12 probe for two owned modules): the axioms of every stored constant of
the owned modules (auxiliaries and the private helpers included), and a dependency trace: for every
constant that reaches `sorryAx`, the admitted declarations (TCSlib constants whose own value uses
`sorryAx` directly) it reaches it through, found by a walk over the used constants. -/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let owned : List Name := [`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity]
  let mut out : Array String := #[]
  let mut sorryConsts : Array Name := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless owned.contains mod do continue
    let axs ← liftCoreM <| collectAxioms c
    let s := (axs.map toString).qsort (· < ·)
    out := out.push s!"AX\t{mod.components.getLast!}\t{c}\t{s.toList}"
    if axs.contains ``sorryAx then sorryConsts := sorryConsts.push c
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size}"
  -- dependency trace of the constants reaching `sorryAx`
  for c in sorryConsts do
    let mut seen : NameSet := {}
    let mut stack : Array Name := #[c]
    let mut admitted : Array Name := #[]
    while !stack.isEmpty do
      let d := stack.back!
      stack := stack.pop
      if seen.contains d then continue
      seen := seen.insert d
      let some ci := env.find? d | continue
      let used := ci.getUsedConstantsAsSet
      if used.contains ``sorryAx then admitted := admitted.push d
      for u in used.toList do
        if !seen.contains u then stack := stack.push u
    IO.println s!"TRACE\t{c}\t{admitted.toList}"
  IO.println s!"SORRY-REACHING {sorryConsts.size}"
