import Lean
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer
/- DLC-SEAL lean_proof_scot_ctl_CtlReader: whole-file closure seal of `lean_proof/scot/ctl/CtlReader.lean`, variant A (PolyExpr.eval open), coe (projection coercions open). -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
  let coeOpen : Bool := true
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
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
  Lean.logInfo m!"DLC-SEAL lean_proof_scot_ctl_CtlReader: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


/-! Positive control: the same facts through published readers (`NUPPT.layout_eq`, `OT.mask_eq`,
`PolyExpr.eval_const`). Passes unsealed and under every seal. -/

theorem ctl_reader_layout (u y α r : List Bool) :
    Complexity.NUPPT.layout u y α r = Turing.pairEncode (Turing.pairEncode (Turing.pairEncode u y) α) r :=
  Complexity.NUPPT.layout_eq u y α r

open TCSlib.Cryptography.SecureComputation in
theorem ctl_reader_mask (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool)
    (n : ℕ) (i t yj : List Bool) (a : Bool) :
    OT.mask T H n i t yj a =
      List.zipWith xor (H (Turing.pairEncode i (T.inv.runAtL n (Turing.pairEncode t yj)
        (List.replicate (T.inv.coins.eval n) true)))) [a] :=
  OT.mask_eq T H n i t yj a

theorem ctl_reader_eval : (Complexity.PolyExpr.const 5).eval 3 = 5 :=
  Complexity.PolyExpr.eval_const 5 3
