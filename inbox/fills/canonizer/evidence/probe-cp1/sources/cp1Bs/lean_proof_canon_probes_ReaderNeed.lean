import Lean
import TCSlib.Complexity.TuringMachine.CodeSimulator
/- DLC-SEAL lean_proof_canon_probes_ReaderNeed: whole-file closure seal of `lean_proof/canon/probes/ReaderNeed.lean`, variant B (PolyExpr.eval sealed), strict. -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let coeOpen : Bool := false
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
  Lean.logInfo m!"DLC-SEAL lean_proof_canon_probes_ReaderNeed: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


/-! Seal probe of the fill `canonizer` (checkpoint 1): the three facts the route needs, each
closed by definitional unfolding at the issue base, where no published lemma states them.
Unsealed, all three elaborate. Under every whole-closure seal each must fail exactly once:
- `need_codeFormat` unfolds `oneTapeFormat` (and `codeDecode`) of `CodeFormat.lean`;
- `need_codeSimulator` unfolds `oneTapeMachineFormat` of `CodeSimulator.lean`;
- `need_transport` is the transport of `exists_polyCanonizer`'s specification that
  `Turing.exists_uniformMachineCode` (`Diagonalization/EXPCOM.lean`) performs by unfolding.
So each of the two readers is needed, and together they give the transport. -/

open Turing

theorem need_codeFormat (xs : List Bool) :
    oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize := rfl

theorem need_codeSimulator (α : List Bool) :
    oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
      oneTapeFormat.serialize (oneTapeFormat.decode α) := rfl

theorem need_transport :
    ∃ (C : FinTM Bool) (d : ℕ),
      C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d :=
  oneTapeMachineFormat.exists_polyCanonizer
