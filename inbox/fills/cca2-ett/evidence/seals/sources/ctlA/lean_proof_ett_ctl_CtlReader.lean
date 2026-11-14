import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
/- DLC-SEAL lean_proof_ett_ctl_CtlReader: whole-file closure seal of `lean_proof/ett/ctl/CtlReader.lean` (PolyExpr.eval open). -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL lean_proof_ett_ctl_CtlReader: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


/-! Positive control: the same facts through published readers (`ETTGame.wR_eq`,
`PolyExpr.eval_const`). Passes unsealed and under both seals. -/

theorem ctl_reader_wR (w : List Bool) :
    TCSlib.Cryptography.Composability.ETTGame.wR w = Complexity.pairFstD w :=
  TCSlib.Cryptography.Composability.ETTGame.wR_eq w

theorem ctl_reader_eval : (Complexity.PolyExpr.const 1).eval 5 = 1 :=
  Complexity.PolyExpr.eval_const 1 5
