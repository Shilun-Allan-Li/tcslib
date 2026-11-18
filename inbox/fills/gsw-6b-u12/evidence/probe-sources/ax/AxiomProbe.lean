import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching

/-! gsw-6b-u12, C5: the axioms of every stored constant of the owned module (auxiliaries and the
private helper included), and a dependency trace: for every constant that reaches `sorryAx`, the
admitted declarations (TCSlib constants whose own value uses `sorryAx` directly) it reaches it
through, found by a walk over the used constants. -/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let owned : Name := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
  let mut out : Array String := #[]
  let mut sorryConsts : Array Name := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    unless env.header.moduleNames[idx.toNat]! == owned do continue
    let axs ← liftCoreM <| collectAxioms c
    let s := (axs.map toString).qsort (· < ·)
    out := out.push s!"AX\t{c}\t{s.toList}"
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
