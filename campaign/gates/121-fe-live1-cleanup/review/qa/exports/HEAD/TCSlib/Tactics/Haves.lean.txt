import Lean

/-!
# `Haves.lean` — have hygiene and have→lemma extraction

A frontend driver, not a tactic: it elaborates one Lean file in-process, reads the
*elaborated* facts about every tactic `have` from the info trees (its type, its proof
term, where its name is used, which local hypotheses it depends on, its exact source
range), rewrites the source text, and then re-elaborates the result to verify that no
new error appeared before anything is written.  Nothing is guessed from the text:
every decision is taken on `Expr`s and `Syntax` with positions, and the only text the
tool produces is the text of the original file moved around, plus pretty-printed
types for binders that have no source text (tactic-introduced variables).

Run through `scripts/haves.py`, or directly:

```
lake env lean --run TCSlib/Tactics/Haves.lean scan    FILE
lake env lean --run TCSlib/Tactics/Haves.lean clean   FILE [--write | --out PATH] [--decl NAME ...]
                                                           [--no-unused] [--no-exact] [--no-rfl-rw] [--max-rounds N]
lake env lean --run TCSlib/Tactics/Haves.lean extract FILE --target DECL:HAVE[@LINE]:NEWNAME ...
                                                           [--write | --out PATH] [--private] [--doc TEXT]
                                                           [--keyword lemma|theorem]
```

`scan` prints one JSON object per tactic `have` (the manifest of `have2lemma/README.md`).

`clean` removes the three kinds of unnecessary `have` that mechanical proof writers
produce, each decided on the proof term:

* **unused** — the bound variable does not occur in the rest of the proof term (so not
  even `simp_all`/`omega` consumed it): the `have` is deleted;
* **have-then-exact** — the rest of the proof is literally the variable (`have h : T := p`
  followed by `exact h`): replaced by `p`'s tactics (or `exact p`), prefixed by `show T`
  when `T` is not syntactically the goal;
* **rfl-have-then-rw** — `have h : A = B := rfl` whose single use is `rw [h]` on a goal
  that is `A`: replaced by `change B` (plus `rfl` when the `rw` closed the goal).

`extract` turns a chosen `have` into a standalone declaration placed before its
theorem, with a parameter list computed from the dependency closure of the have's type
and proof (theorem-signature binders keep their source text; tactic-introduced ones are
pretty-printed), and replaces the `have`'s proof by a call to it so that every later use
of the name is untouched.  It refuses haves that depend on inaccessible (`a✝`) or
`let`-bound hypotheses rather than emitting something unreadable.

Both `clean` and `extract` write nothing unless the rewritten file re-elaborates with
no new error (`--write` replaces the file; `--out` writes beside it).
-/

open Lean Elab Meta

namespace Haves

/-! ## Elaboration -/

structure Msg where
  severity : MessageSeverity
  line : Nat
  text : String

structure ElabResult where
  input : String
  fileMap : FileMap
  commands : Array Syntax
  trees : PersistentArray InfoTree
  msgs : Array Msg

def Msg.isError (m : Msg) : Bool := m.severity matches .error

def collectMsgs (log : MessageLog) : IO (Array Msg) := do
  let mut out := #[]
  for m in log.toList do
    out := out.push { severity := m.severity, line := m.pos.line, text := (← m.data.toString) }
  return out

/-- Elaborate `input` (the contents of `path`) with info trees enabled.  The header is
processed once per process (`envCache`) so that a verification pass does not reload
Mathlib. -/
def elabFile (path : String) (input : String) (envCache : IO.Ref (Option Environment)) :
    IO ElabResult := do
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts : Options := ({} : Options).setBool `Elab.async false
  let env ← match ← envCache.get with
    | some env => pure env
    | none =>
      let (env, messages) ← processHeader header opts messages inputCtx
      if messages.hasErrors then
        for m in messages.toList do IO.eprintln s!"{← m.toString}"
        throw <| IO.userError "the file's imports could not be processed"
      envCache.set (some env)
      pure env
  let cmdState := Command.mkState env {} opts
  let cmdState := { cmdState with infoState := { enabled := true } }
  let s ← IO.processCommands inputCtx parserState cmdState
  return { input, fileMap := inputCtx.fileMap, commands := s.commands,
           trees := s.commandState.infoState.trees, msgs := ← collectMsgs s.commandState.messages }

/-! ## Info-tree and syntax navigation -/

structure TacNode where
  ctx : ContextInfo
  ti : TacticInfo
  range : String.Range

partial def collectTactics (ctx? : Option ContextInfo) (t : InfoTree) (acc : Array TacNode) :
    Array TacNode :=
  match t with
  | .context pci t => collectTactics (pci.mergeIntoOuter? ctx?) t acc
  | .node i cs =>
    let acc := match ctx?, i with
      | some ctx, .ofTacticInfo ti =>
        match ti.stx.getRange? with
        | some range => acc.push { ctx, ti, range }
        | none => acc
      | _, _ => acc
    cs.foldl (fun acc c => collectTactics ctx? c acc) acc
  | .hole _ => acc

/-- Source references to local hypotheses: every identifier the elaborator resolved to
an fvar, counted once per source position.  A `have` named here but absent from the
proof term was consumed as a hint (`nlinarith [h.le]`, `simp [h]`) that the final
certificate did not need; deleting it would still break the text. -/
partial def collectFVarRefs (t : InfoTree) (acc : Std.HashSet (FVarId × Nat)) :
    Std.HashSet (FVarId × Nat) :=
  match t with
  | .context _ t => collectFVarRefs t acc
  | .node i cs =>
    let acc := match i with
      | .ofTermInfo ti =>
        match ti.expr, ti.stx.getPos? with
        | .fvar id, some pos => acc.insert (id, pos.byteIdx)
        | _, _ => acc
      | _ => acc
    cs.foldl (fun acc c => collectFVarRefs c acc) acc
  | .hole _ => acc

def rangeEq (a b : String.Range) : Bool := a.start == b.start && a.stop == b.stop

def rangeContains (outer inner : String.Range) : Bool :=
  outer.start ≤ inner.start && inner.stop ≤ outer.stop

/-- Ancestors of the node with range `r` and kind `kind` inside `stx`, root first, the
node itself last. -/
partial def findPath (stx : Syntax) (r : String.Range) (kind : SyntaxNodeKind) :
    Option (Array Syntax) := do
  let sr ← stx.getRange?
  guard (rangeContains sr r)
  if stx.getKind == kind && rangeEq sr r then
    return #[stx]
  for c in stx.getArgs do
    if let some p := findPath c r kind then
      return #[stx] ++ p
  none

def haveKind : SyntaxNodeKind := ``Parser.Tactic.tacticHave__

/-- The pieces of a `have` tactic: `have id binders* : type := value`. -/
structure HaveStx where
  stx : Syntax
  /-- the identifier, absent for an anonymous `have : T := …` -/
  idStx? : Option Syntax
  binders : Array Syntax
  typeStx? : Option Syntax
  assignTk : Syntax
  valueStx : Syntax
  isPattern : Bool

def haveParts (stx : Syntax) : Option HaveStx := do
  guard (stx.getKind == haveKind)
  let d := stx[2][0]
  if d.getKind == ``Parser.Term.letIdDecl then
    let letId := d[0]
    let idStx? := if letId[0].isIdent then some letId[0] else none
    let optType := d[2]
    let typeStx? := if optType.getNumArgs > 0 then some optType[0][1] else none
    return { stx, idStx?, binders := d[1].getArgs, typeStx?, assignTk := d[3], valueStx := d[4],
             isPattern := false }
  else if d.getKind == ``Parser.Term.letPatDecl then
    return { stx, idStx? := none, binders := #[], typeStx? := none, assignTk := d[3],
             valueStx := d[4], isPattern := true }
  else none

/-- The tactics of `by tac₁ …` when the block is an indented sequence. -/
def byItems? (value : Syntax) : Option (Array Syntax) := do
  guard (value.getKind == ``Parser.Term.byTactic)
  let inner := value[1][0]
  let list ←
    if inner.getKind == ``Parser.Tactic.tacticSeq1Indented then some inner[0]
    else if inner.getKind == ``Parser.Tactic.tacticSeqBracketed then some inner[1]
    else none
  return list.getArgs.filter fun a => !a.isAtom && a.getKind != nullKind

/-- The enclosing tactic sequence's items and the index of `node` in them. -/
def seqSiblings (path : Array Syntax) : Option (Array Syntax × Nat) := do
  guard (path.size ≥ 3)
  let node := path.back!
  let list := path[path.size - 2]!
  let seq := path[path.size - 3]!
  guard (seq.getKind == ``Parser.Tactic.tacticSeq1Indented)
  let items := list.getArgs.filter fun a => !a.isAtom && a.getKind != nullKind
  let idx ← items.findIdx? fun a => a.getRange? == node.getRange?
  return (items, idx)

def tacticName (stx : Syntax) : String :=
  if stx.getNumArgs > 0 && stx[0].isAtom then stx[0].getAtomVal else stx.getKind.toString

/-! ## Analysis of one have -/

structure Site where
  ctx : ContextInfo
  ti : TacticInfo
  range : String.Range
  finalMctx : MetavarContext
  /-- the goal of the outermost tactic block containing this have -/
  rootGoal : MVarId
  cmd : Syntax
  path : Array Syntax
  parts : HaveStx
  decl : Name
  /-- source positions referring to each local hypothesis of this command, by fvar -/
  refs : Std.HashMap FVarId (Array Nat)

structure Dep where
  decl : LocalDecl
  ppType : String
  /-- `ppType` re-elaborates to the binder's type in the have's context -/
  roundTrips : Bool
  /-- bound by the theorem's signature (or a `variable`), not by a tactic -/
  isSig : Bool
  /-- occurs in the have's type or in the type of an explicit dependency, so an
  implicit binder would be inferred at the call site -/
  inferable : Bool

structure Analysis where
  name : Name
  ty : Expr
  v : Expr
  useCount : Nat
  /-- occurrences of the name in the source after the have -/
  textRefs : Nat
  isExact : Bool
  tyIsGoal : Bool
  isRfl : Bool
  eqLhsIsGoal : Bool
  deps : Array Dep
  letDeps : Array Name
  inaccDeps : Array Name
  /-- a `rename_i` line giving the inaccessible dependencies accessible names, to be placed
  before the have; the renamed names are already in `deps` -/
  renameLine : Option String
  auxDeps : Array Name
  needsClassical : Bool
  hasSorry : Bool
  ppTy : String
  ppGoal : String

partial def stripMData (e : Expr) : Expr :=
  e.replace fun e => match e with
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- Binder names are display only; two types that differ just there are the same goal. -/
partial def eraseBinderNames (e : Expr) : Expr :=
  match e with
  | .forallE _ t b bi => .forallE .anonymous (eraseBinderNames t) (eraseBinderNames b) bi
  | .lam _ t b bi => .lam .anonymous (eraseBinderNames t) (eraseBinderNames b) bi
  | .letE _ t v b nd => .letE .anonymous (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) nd
  | .app f a => .app (eraseBinderNames f) (eraseBinderNames a)
  | .mdata _ b => eraseBinderNames b
  | .proj n i b => .proj n i (eraseBinderNames b)
  | e => e

partial def countBVar (e : Expr) (i : Nat) : Nat :=
  match e with
  | .bvar j => if i == j then 1 else 0
  | .app f a => countBVar f i + countBVar a i
  | .lam _ t b _ => countBVar t i + countBVar b (i+1)
  | .forallE _ t b _ => countBVar t i + countBVar b (i+1)
  | .letE _ t v b _ => countBVar t i + countBVar v i + countBVar b (i+1)
  | .mdata _ b => countBVar b i
  | .proj _ _ b => countBVar b i
  | _ => 0

/-- `have h : ty := v; body` as the elaborator leaves it in the proof term. -/
def splitHave (e : Expr) : Option (Name × Expr × Expr × Expr) :=
  if e.isAppOfArity ``letFun 4 then
    match e.getAppArgs[3]! with
    | .lam n ty body _ => some (n, ty, e.getAppArgs[2]!, body)
    | _ => none
  else match e with
    | .letE n ty v body _ => some (n, ty, v, body)
    | _ => none

def fvarsOf (e : Expr) : FVarIdSet := (Lean.collectFVars {} e).fvarSet

def ppOpts (o : Options) : Options :=
  (o.setBool `pp.funBinderTypes true).setBool `pp.piBinderTypes true

def universeStar (s : String) : String :=
  if s.startsWith "Type u_" && !s.any (· == ' ') then "Type*"
  else if s.startsWith "Sort u_" && !s.any (· == ' ') then "Sort*"
  else s

/-- Parse and elaborate `text` as a type in the current context, without auto-bound
implicits and without errors turning into `sorry`. -/
def elabTypeText (text : String) : MetaM (Option Expr) := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .error _ => return none
  | .ok stx =>
    try
      let e ← withOptions (fun o => o.setBool `autoImplicit false) <|
        Term.TermElabM.run' do
          Term.withoutErrToSorry do
            let e ← Term.elabType stx
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e
      return some e
    catch _ => return none

/-- Printer settings tried in turn for a binder with no source text: plain, then with
coercion arrows spelled out (`↑S` loses its target type), then without field notation,
then fully explicit. -/
def renderLadder : List (String × (Options → Options)) := [
  ("plain", fun o => o),
  ("no-coercions", fun o => o.setBool `pp.coercions false),
  ("no-field-notation", fun o => o.setBool `pp.fieldNotation false),
  ("no-coercions-no-field-notation", fun o => (o.setBool `pp.coercions false).setBool `pp.fieldNotation false),
  ("explicit", fun o => o.setBool `pp.explicit true)]

/-- The first rendering of `ty` that re-elaborates, in this context, to `ty` itself
(or something definitionally equal), with the plain rendering as a fallback report. -/
def renderType (ty : Expr) : MetaM (String × Bool) := do
  let plain := universeStar (toString (← ppExpr ty))
  let mut best : Option String := none
  for (_, f) in renderLadder do
    let text := universeStar (toString (← withOptions f (ppExpr ty)))
    match ← elabTypeText text with
    | some e =>
      if stripMData e == stripMData ty then return (text, true)
      if best.isNone then
        if ← (try isDefEq e ty catch _ => pure false) then best := some text
    | none => pure ()
  match best with
  | some text => return (text, true)
  | none => return (plain, false)

def analyze (site : Site) : IO (Except String Analysis) := do
  let some g := site.ti.goalsBefore.head? | return .error "the have has no goal before it"
  let some gdecl := site.finalMctx.findDecl? g | return .error "goal missing from the final context"
  let some rdecl := site.finalMctx.findDecl? site.rootGoal | return .error "root goal missing"
  let sigFVars : FVarIdSet := rdecl.lctx.foldl (fun s d => s.insert d.fvarId) {}
  let ctx := { site.ctx with mctx := site.finalMctx, options := ppOpts site.ctx.options }
  ctx.runMetaM gdecl.lctx do
    let e := stripMData (← instantiateMVars (mkMVar g))
    let some (name, ty, v, body) := splitHave e
      | return .error "the proof term at this have is not a have binding (destructuring have, or an unsupported form)"
    let ty := stripMData (← instantiateMVars ty)
    let v := stripMData (← instantiateMVars v)
    let goalTy := stripMData (← instantiateMVars (← g.getType))
    let useCount := countBVar body 0
    let textRefs := Id.run do
      let some g' := site.ti.goalsAfter.head? | return 0
      let some d' := site.finalMctx.findDecl? g' | return 0
      -- references after the have itself (the binder name carries one too)
      let mut n := 0
      for d in d'.lctx do
        if !gdecl.lctx.contains d.fvarId && d.userName == name then
          for pos in (site.refs.get? d.fvarId).getD #[] do
            if pos ≥ site.range.stop.byteIdx then n := n + 1
      return n
    let isExact := body == .bvar 0
    -- "the type is the goal": syntactically, or indistinguishable in print and equal up
    -- to reducible unfolding (binder names, instance paths), in which case a `show`
    -- would only repeat the goal
    let ppTy := toString (← ppExpr ty)
    let ppGoal := toString (← ppExpr goalTy)
    let tyIsGoal ← if eraseBinderNames ty == eraseBinderNames goalTy then pure true
      else if toString (← ppExpr (eraseBinderNames ty)) == toString (← ppExpr (eraseBinderNames goalTy)) then
        withReducible (isDefEq ty goalTy)
      else pure false
    let vf := v.getAppFn
    let isRfl := vf.isConstOf ``rfl || vf.isConstOf ``Eq.refl
    let eqLhsIsGoal := match ty.eq? with
      | some (_, a, _) => a == goalTy
      | none => false
    -- dependency closure
    let lctx ← getLCtx
    let mut wanted := (fvarsOf ty).union (fvarsOf v)
    let mut changed := true
    while changed do
      changed := false
      for d in lctx do
        if wanted.contains d.fvarId then
          let s := match d.value? with
            | some val => (fvarsOf d.type).union (fvarsOf val)
            | none => fvarsOf d.type
          for f in s.toList do
            unless wanted.contains f do
              wanted := wanted.insert f
              changed := true
    -- Inaccessible dependencies (`a✝`, from a bare `intro` or a `cases`) get fresh
    -- accessible names: `rename_i` names the trailing inaccessible hypotheses of the
    -- context positionally, so one line before the have does it, and the lemma's
    -- parameters use the new names.  Instance arguments stay anonymous.
    let taken : Std.HashSet String := lctx.foldl
      (fun t d => if d.userName.hasMacroScopes then t else t.insert d.userName.toString) {}
    let mut taken := taken
    let mut renames : Array (FVarId × Name) := #[]
    let mut inaccDeps := #[]
    for d in lctx do
      if wanted.contains d.fvarId && d.userName.hasMacroScopes && !(d.binderInfo matches .instImplicit)
          && !d.isAuxDecl && !d.isImplementationDetail then
        let base := d.userName.eraseMacroScopes.toString
        let isP ← isProp d.type
        let base := if base.isEmpty || base == "x" then (if isP then "h" else "x") else base
        let mut cand := base
        let mut i := 1
        while taken.contains cand do
          cand := s!"{base}_{i}"; i := i + 1
        taken := taken.insert cand
        renames := renames.push (d.fvarId, Name.mkSimple cand)
        inaccDeps := inaccDeps.push d.userName
    let renameLine : Option String := if renames.isEmpty then none else Id.run do
      -- every inaccessible hypothesis from the first renamed one onward, `_` when kept
      let first := renames[0]!.1
      let mut names : Array String := #[]
      let mut started := false
      for d in lctx do
        if d.fvarId == first then started := true
        if started && d.userName.hasMacroScopes && !d.isAuxDecl && !d.isImplementationDetail then
          names := names.push (match renames.find? (·.1 == d.fvarId) with
            | some (_, n) => n.toString
            | none => "_")
      some ("rename_i " ++ " ".intercalate names.toList)
    let lctx := renames.foldl (fun l (f, n) => l.setUserName f n) lctx
    withLCtx lctx (← getLocalInstances) do
    let mut deps : Array Dep := #[]
    let mut letDeps := #[]
    let mut auxDeps := #[]
    for d in lctx do
      unless wanted.contains d.fvarId do continue
      if d.isAuxDecl || d.isImplementationDetail then
        auxDeps := auxDeps.push d.userName
        continue
      if d.isLet then letDeps := letDeps.push d.userName
      let (ppType, roundTrips) ← renderType d.type
      deps := deps.push { decl := d, ppType, roundTrips, isSig := sigFVars.contains d.fvarId, inferable := false }
    -- an implicit binder is inferable at the call site when it occurs in the type of
    -- the have or in the type of an explicit dependency
    let mut inferFrom := fvarsOf ty
    for dep in deps do
      if dep.decl.binderInfo matches .default then
        inferFrom := inferFrom.union (fvarsOf dep.decl.type)
    deps := deps.map fun dep => { dep with inferable := inferFrom.contains dep.decl.fvarId }
    let mentions (c : Name) := (v.find? (·.isConstOf c)).isSome || (ty.find? (·.isConstOf c)).isSome
    let needsClassical := mentions ``Classical.propDecidable
    let hasSorry := mentions ``sorryAx
    return .ok { name, ty, v, useCount, textRefs, isExact, tyIsGoal, isRfl, eqLhsIsGoal, deps, letDeps,
                 inaccDeps, renameLine, auxDeps, needsClassical, hasSorry, ppTy, ppGoal }

/-! ## Site collection -/

structure FileSites where
  er : ElabResult
  sites : Array Site
  /-- every tactic node, for lookups by range (e.g. the `rw` after a have) -/
  tactics : Array TacNode

def collectSites (er : ElabResult) : FileSites := Id.run do
  let mut sites := #[]
  let mut allTacs := #[]
  for tree in er.trees do
    let tacs := collectTactics none tree #[]
    allTacs := allTacs ++ tacs
    let refs : Std.HashMap FVarId (Array Nat) :=
      (collectFVarRefs tree {}).fold (fun m (id, pos) => m.insert id (((m.get? id).getD #[]).push pos)) {}
    let mut seen : Std.HashSet (Nat × Nat) := {}
    for tn in tacs do
      unless tn.ti.stx.getKind == haveKind do continue
      let key := (tn.range.start.byteIdx, tn.range.stop.byteIdx)
      if seen.contains key then continue
      if tn.ti.goalsBefore.isEmpty then continue
      seen := seen.insert key
      -- the outermost tactic node containing this one holds the final metavariable
      -- context of the proof
      let mut root := tn
      for other in tacs do
        if rangeContains other.range tn.range then
          if other.range.start < root.range.start
              || (other.range.start == root.range.start && other.range.stop > root.range.stop) then
            root := other
      let some cmd := er.commands.find? fun c => match c.getRange? with
          | some r => rangeContains r tn.range
          | none => false
        | continue
      let some path := findPath cmd tn.range haveKind | continue
      let some parts := haveParts tn.ti.stx | continue
      let some rootGoal := root.ti.goalsBefore.head? | continue
      sites := sites.push { ctx := tn.ctx, ti := tn.ti, range := tn.range,
                            finalMctx := root.ti.mctxAfter, rootGoal, cmd, path, parts,
                            decl := tn.ctx.parentDecl?.getD .anonymous, refs }
  return { er, sites, tactics := allTacs }

/-! ## Text helpers -/

def textOf (input : String) (r : String.Range) : String :=
  String.Pos.Raw.extract input r.start r.stop

def stxText (input : String) (stx : Syntax) : String :=
  match stx.getRange? with
  | some r => textOf input r
  | none => ""

def colOf (fm : FileMap) (pos : String.Pos.Raw) : Nat := (fm.toPosition pos).column

def lineOf (fm : FileMap) (pos : String.Pos.Raw) : Nat := (fm.toPosition pos).line

def spaces (n : Nat) : String := "".pushn ' ' n

def indentOf (l : String) : Nat := l.length - l.trimLeft.length

/-- Move a multi-line fragment: its first line is placed by the caller at column
`toCol`; every following line is shifted by the same amount the first line moved from
`fromCol`, but never below `minCol`. -/
def reindent (text : String) (fromCol toCol minCol : Nat) : String :=
  let lines := text.splitOn "\n"
  match lines with
  | [] | [_] => text
  | first :: rest =>
    let conts := rest.filter fun l => !l.trim.isEmpty
    let minCont := conts.foldl (fun m l => min m (indentOf l)) 1000000
    let shift : Int := (toCol : Int) - fromCol
    let shift := if conts.isEmpty then shift else max shift ((minCol : Int) - minCont)
    let rest := rest.map fun l =>
      if l.trim.isEmpty then "" else
      let ind := indentOf l
      let newInd := max 0 ((ind : Int) + shift)
      spaces newInd.toNat ++ l.trimLeft
    "\n".intercalate (first :: rest)

def lastLineLength (s : String) : Nat :=
  match s.splitOn "\n" |>.getLast? with
  | some l => l.length
  | none => 0

/-- An edit of the original text.  Replacements are applied from the end of the file
backwards; `mk` receives the text as it stands when the edit is applied and a function
mapping original positions to current ones, so an outer edit can read the result of
inner edits it encloses. -/
structure Edit where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  build : String → (String.Pos.Raw → String.Pos.Raw) → IO String
  label : String
  /-- tie-breaker among edits at the same position: higher applies first -/
  order : Nat := 0
  deriving Inhabited

def applyEdits (input : String) (edits : Array Edit) : IO String := do
  let sorted := edits.qsort fun a b =>
    a.start.byteIdx > b.start.byteIdx || (a.start.byteIdx == b.start.byteIdx &&
      (a.stop.byteIdx > b.stop.byteIdx || (a.stop.byteIdx == b.stop.byteIdx && a.order > b.order)))
  let mut text := input
  let mut applied : Array (String.Pos.Raw × String.Pos.Raw × Int) := #[]
  for e in sorted do
    let appliedSoFar := applied
    -- an applied edit shifts `p` when it lies before `p`; an insertion made at `p`
    -- itself does not, so a second insertion at the same point lands before it
    let mapPos : String.Pos.Raw → String.Pos.Raw := fun p =>
      let delta := appliedSoFar.foldl (fun acc (start, stop, d) =>
        if stop.byteIdx < p.byteIdx || (stop.byteIdx == p.byteIdx && start.byteIdx < stop.byteIdx) then acc + d else acc) (0 : Int)
      ⟨(((p.byteIdx : Int) + delta).toNat)⟩
    let curStop := mapPos e.stop
    let repl ← e.build text mapPos
    let before := String.Pos.Raw.extract text ⟨0⟩ e.start
    let after := String.Pos.Raw.extract text curStop ⟨text.utf8ByteSize⟩
    let delta : Int := (repl.utf8ByteSize : Int) - ((curStop.byteIdx : Int) - e.start.byteIdx)
    text := before ++ repl ++ after
    applied := applied.push (e.start, e.stop, delta)
  return text

/-! ## JSON -/

def Site.line (s : Site) (fm : FileMap) : Nat := lineOf fm s.range.start

def nestingDepth (path : Array Syntax) : Nat :=
  (path.pop.filter fun s => s.getKind == haveKind).size

def siteJson (fs : FileSites) (s : Site) (a? : Except String Analysis) (next? : Option Syntax) : Json :=
  let fm := fs.er.fileMap
  let input := fs.er.input
  let name := match s.parts.idStx? with
    | some id => id.getId.toString
    | none => if s.parts.isPattern then "⟨…⟩" else "this"
  let bodyLines : Nat := match s.parts.valueStx.getRange? with
    | some r => lineOf fm r.stop - lineOf fm r.start + 1
    | none => 0
  let single := match byItems? s.parts.valueStx with
    | some items => if items.size == 1 then toJson (tacticName items[0]!) else Json.null
    | none => Json.null
  let strs (xs : Array Name) : Json := toJson (xs.map toString)
  let base : List (String × Json) := [
    ("haveName", toJson name),
    ("anonymous", toJson (s.parts.idStx?.isNone && !s.parts.isPattern)),
    ("destructuring", toJson s.parts.isPattern),
    ("declaration", toJson s.decl.toString),
    ("line", toJson (s.line fm)), ("column", toJson (colOf fm s.range.start)),
    ("endLine", toJson (lineOf fm s.range.stop)),
    ("bodyLines", toJson bodyLines),
    ("nestingDepth", toJson (nestingDepth s.path)),
    ("typeText", match s.parts.typeStx? with | some t => toJson (stxText input t) | none => Json.null),
    ("binders", toJson (" ".intercalate (s.parts.binders.map (stxText input ·)).toList)),
    ("valueIsTerm", toJson (byItems? s.parts.valueStx).isNone),
    ("singleTacticClose", single),
    ("nextTactic", match next? with | some n => toJson (tacticName n) | none => Json.null)]
  match a? with
  | .error err => Json.mkObj (base ++ [("error", toJson err)])
  | .ok a =>
    Json.mkObj (base ++ [
      ("typeElab", toJson a.ppTy),
      ("useCount", toJson a.useCount),
      ("textRefs", toJson a.textRefs),
      ("unused", toJson (a.useCount == 0 && a.textRefs == 0)),
      ("hintOnly", toJson (a.useCount == 0 && a.textRefs > 0)),
      ("exactAfter", toJson (a.isExact && (match next? with
          | some n => n.getKind == ``Parser.Tactic.exact && n[1].isIdent && n[1].getId == a.name
          | none => false))),
      ("typeIsGoal", toJson a.tyIsGoal),
      ("goalElab", toJson a.ppGoal),
      ("rflEq", toJson (a.isRfl && a.eqLhsIsGoal)),
      ("localDeps", strs (a.deps.map (·.decl.userName))),
      ("sigDeps", strs (a.deps.filter (·.isSig) |>.map (·.decl.userName))),
      ("inaccessibleDeps", strs a.inaccDeps),
      ("letDeps", strs a.letDeps),
      ("recursiveDeps", strs a.auxDeps),
      ("needsClassical", toJson a.needsClassical),
      ("hasSorry", toJson a.hasSorry)])

/-! ## Clean -/

structure CleanOpts where
  unused : Bool := true
  exact : Bool := true
  rflRw : Bool := true
  decls : Array String := #[]

structure Change where
  kind : String
  decl : String
  haveName : String
  line : Nat
  detail : String
  deriving Inhabited

def declMatches (decl : Name) (wanted : Array String) : Bool :=
  wanted.isEmpty || wanted.any fun w => decl.toString == w || decl.toString.endsWith ("." ++ w)

def nextSibling (s : Site) : Option Syntax := do
  let (items, idx) ← seqSiblings s.path
  items[idx + 1]?

def isExactOf (stx : Syntax) (n : Name) : Bool :=
  (stx.getKind == ``Parser.Tactic.exact && stx[1].isIdent && stx[1].getId == n)
    || stx.getKind == ``Parser.Tactic.assumption

/-- The names a `have`'s own binders bind, as `intro` would take them. -/
def introNames (binders : Array Syntax) : Array String :=
  binders.flatMap fun b =>
    if b.isIdent then #[b.getId.toString]
    else if b.getKind == ``Parser.Term.hole then #["_"]
    else if b.getKind == ``Parser.Term.explicitBinder || b.getKind == ``Parser.Term.implicitBinder
        || b.getKind == ``Parser.Term.strictImplicitBinder then
      b[1].getArgs.map fun id => if id.isIdent then id.getId.toString else "_"
    else if b.getKind == ``Parser.Term.instBinder then
      #[if b[1].getNumArgs > 0 && b[1][0].isIdent then b[1][0].getId.toString else "_"]
    else #["_"]

/-- `rw [h]` with exactly that one rule, no `←`, no `at`. -/
def isRwOf (stx : Syntax) (n : Name) : Bool := Id.run do
  unless stx.getKind == ``Parser.Tactic.rwSeq do return false
  let rules := stx[2][1].getArgs.filter fun a => !a.isAtom
  unless rules.size == 1 do return false
  let rule := rules[0]!
  unless rule.getKind == ``Parser.Tactic.rwRule do return false
  unless rule[0].getNumArgs == 0 do return false
  unless rule[1].isIdent && rule[1].getId == n do return false
  return stx[3].getNumArgs == 0

def haveDisplayName (s : Site) : String :=
  match s.parts.idStx? with
  | some id => id.getId.toString
  | none => "this"

/-- `exclude`: (declaration, have, kind) of edits that failed verification in an earlier round. -/
def cleanEdits (fs : FileSites) (opts : CleanOpts) (exclude : Std.HashSet (String × String × String)) :
    IO (Array Edit × Array Change × Array Change) := do
  let input := fs.er.input
  let fm := fs.er.fileMap
  let mut edits := #[]
  let mut changes := #[]
  let mut skipped := #[]
  -- end positions of `exact …` tactics whose inlined block got a bullet in this round
  let mut bulletedStops : Array Nat := #[]
  for s in fs.sites do
    unless declMatches s.decl opts.decls do continue
    if s.parts.isPattern then continue
    let a ← match ← analyze s with
      | .ok a => pure a
      | .error _ => continue
    let name := haveDisplayName s
    let line := s.line fm
    let col := colOf fm s.range.start
    let some next := nextSibling s | continue
    let some nextR := next.getRange? | continue
    let mkChange (kind detail : String) : Change := { kind, decl := s.decl.toString, haveName := name, line, detail }
    let excluded (kind : String) := exclude.contains (s.decl.toString, name, kind)
    if opts.unused && a.useCount == 0 && a.textRefs == 0 && !excluded "unused" then
      -- delete the have up to the start of the next tactic, keeping any comment in between
      let gap := textOf input { start := s.range.stop, stop := nextR.start }
      let stop := if gap.any (· == '-') then
          fm.lineStart (lineOf fm s.range.stop + 1)
        else nextR.start
      edits := edits.push { start := s.range.start, stop, build := fun _ _ => pure "", label := s!"unused {name}" }
      changes := changes.push (mkChange "unused" s!"deleted unused `have {name}`")
    else if opts.exact && a.isExact && isExactOf next a.name
        && !(excluded "exact" && s.parts.typeStx?.isSome && (byItems? s.parts.valueStx).isNone)
        && !(excluded "exact" && s.parts.typeStx?.isNone && (byItems? s.parts.valueStx).isSome
             && s.parts.binders.isEmpty)
        && !excluded "exact-ascribed" then
      let origValue := s.parts.valueStx
      let isBlock := (byItems? origValue).isSome
      if isBlock && (byItems? origValue).get!.isEmpty then continue
      -- `have h (x : α) : P x := p; exact h` proves `∀ x, P x`: `intro x`, then `p`
      let intros := introNames s.parts.binders
      let isBlock := isBlock || !intros.isEmpty
      -- Second attempts after a failed verification: `have h := e; exact h` elaborates
      -- `e` without an expected type, which `exact (e :)` keeps; and `have h : T := by
      -- tacs; exact h` elaborates `T` on its own, which `refine (?_ : T)` keeps where
      -- `show T` would unify `T` with the goal first (and so may change what the tactics
      -- see).
      let ascribe := excluded "exact"
      let kind := if ascribe then "exact-ascribed" else "exact"
      let stop := nextR.stop
      let haveR := s.range
      -- When the have closed one of several open goals, the inlined block goes under
      -- a bullet, which is how such a block is written by hand; the block closing the
      -- last goal after bulleted siblings gets one too, so the shape stays uniform.
      let prevBulleted := match seqSiblings s.path with
        | some (items, idx) =>
          match items[idx - 1]? with
          | some prev => idx > 0 && (prev.getKind == ``cdot
              || (match prev.getRange? with
                  | some r => bulletedStops.contains r.stop.byteIdx
                  | none => false))
          | none => false
        | none => false
      let bullet := s.ti.goalsBefore.length > 1 || prevBulleted
      if bullet then bulletedStops := bulletedStops.push nextR.stop.byteIdx
      let col := if bullet then col + 2 else col
      -- a tactic block proves `T` behind `show T`; a term is ascribed, `(e : T)`
      let typeText := match s.parts.typeStx? with
        | some t => if a.tyIsGoal && intros.isEmpty then "" else
            reindent (stxText input t) (colOf fm (t.getRange?.get!.start)) (col + 5) (col + 1)
        | none => ""
      let introLine := if intros.isEmpty then "" else "intro " ++ " ".intercalate intros.toList ++ "\n" ++ spaces col
      let showLine := introLine ++
        (if isBlock && !typeText.isEmpty then
          (if ascribe then "refine (?_ : " ++ typeText ++ ")" else "show " ++ typeText) ++ "\n" ++ spaces col
         else "")
      -- the body may contain haves edited in the same round: read it from the current text
      let buildExact (cur : String) (mapPos : String.Pos.Raw → String.Pos.Raw) : IO String := do
        let body := match byItems? origValue with
          | some items =>
            let r0 := (items[0]!.getRange?).get!
            let r1 := (items.back!.getRange?).get!
            reindent (String.Pos.Raw.extract cur (mapPos r0.start) (mapPos r1.stop)) (colOf fm r0.start) col col
          | none =>
            let r := origValue.getRange?.get!
            let term := reindent (String.Pos.Raw.extract cur (mapPos r.start) (mapPos r.stop)) (colOf fm haveR.start) col (col + 1)
            if !typeText.isEmpty then s!"exact ({term} : {typeText})"
            else if ascribe then s!"exact ({term} :)"
            else "exact " ++ term
        return (if bullet then "· " else "") ++ showLine ++ body
      edits := edits.push { start := s.range.start, stop, build := buildExact, label := s!"{kind} {name}" }
      changes := changes.push (mkChange kind (if typeText.isEmpty then s!"inlined `have {name}`/`exact {name}`"
        else s!"inlined `have {name}`/`exact {name}` with its type"))
    else if opts.rflRw && a.isRfl && a.eqLhsIsGoal && a.useCount == 1 && a.textRefs == 1
        && isRwOf next a.name && !excluded "rfl-rw" then
      let some t := s.parts.typeStx? | continue
      let t := if t.getKind == ``Parser.Term.paren then t[1] else t
      unless t.getKind == ``«term_=_» do
        skipped := skipped.push (mkChange "rfl-rw" "rfl-have whose type is not written as `A = B`"); continue
      let rhs := if t[2].getKind == ``Parser.Term.paren then t[2][1] else t[2]
      let rhsText := reindent (stxText input rhs) (colOf fm (rhs.getRange?.get!.start)) (col + 7) (col + 1)
      let closed := match fs.tactics.find? fun tn => rangeEq tn.range nextR && tn.ti.stx.getKind == next.getKind with
        | some tn => tn.ti.goalsAfter.isEmpty
        | none => false
      let repl := "change " ++ rhsText ++ (if closed then "\n" ++ spaces col ++ "rfl" else "")
      edits := edits.push { start := s.range.start, stop := nextR.stop, build := fun _ _ => pure repl,
                            label := s!"rfl-rw {name}" }
      let tail := if closed then "; rfl" else ""
      changes := changes.push (mkChange "rfl-rw" s!"replaced `have {name} : A = B := rfl`/`rw [{name}]` by `change B`{tail}")
  return (edits, changes, skipped)

/-! ## Extract -/

structure Target where
  decl : String
  haveName : String
  line? : Option Nat
  newName : String

structure ExtractOpts where
  targets : Array Target
  isPrivate : Bool := false
  doc? : Option String := none
  keyword? : Option String := none

/-- Binder source text from a signature: name ↦ (binder bracket kind, type text). -/
def binderTexts (input : String) (binders : Array Syntax) : Std.HashMap String (BinderInfo × String) := Id.run do
  let mut m : Std.HashMap String (BinderInfo × String) := {}
  for b in binders do
    let k := b.getKind
    let (bi, idents, optType) :=
      if k == ``Parser.Term.explicitBinder then (BinderInfo.default, b[1].getArgs, b[2])
      else if k == ``Parser.Term.implicitBinder then (BinderInfo.implicit, b[1].getArgs, b[2])
      else if k == ``Parser.Term.strictImplicitBinder then (BinderInfo.strictImplicit, b[1].getArgs, b[2])
      else (BinderInfo.default, #[], Syntax.missing)
    if optType.getNumArgs == 0 then continue
    let ty := stxText input optType[1]
    for id in idents do
      if id.isIdent then m := m.insert id.getId.toString (bi, ty)
  return m

partial def sigBinders (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Parser.Command.declSig || stx.getKind == ``Parser.Command.optDeclSig then
    stx[0].getArgs
  else
    stx.getArgs.foldl (fun acc c => if acc.isEmpty then sigBinders c else acc) #[]

def bracket (bi : BinderInfo) (inner : String) : String :=
  match bi with
  | .default => s!"({inner})"
  | .implicit => s!"\{{inner}}"
  | .strictImplicit => s!"⦃{inner}⦄"
  | .instImplicit => s!"[{inner}]"

def binderNames (b : Syntax) : Array String :=
  if b.isIdent then #[b.getId.toString]
  else if b.getKind == ``Parser.Term.explicitBinder then
    b[1].getArgs.filterMap fun id => if id.isIdent then some id.getId.toString else none
  else #[]

def fileKeyword (input : String) : String :=
  let count (p : String) := (input.splitOn p).length - 1
  if count "\ntheorem " + count "\nprivate theorem " ≥ count "\nlemma " + count "\nprivate lemma " then "theorem" else "lemma"

def extractEdits (fs : FileSites) (opts : ExtractOpts) :
    IO (Array Edit × Array Change × Array Change) := do
  let input := fs.er.input
  let fm := fs.er.fileMap
  let keyword := opts.keyword?.getD (fileKeyword input)
  let mut edits := #[]
  let mut changes := #[]
  let mut skipped := #[]
  -- `variable` binders seen so far, by name
  let varBinders : Std.HashMap String (BinderInfo × String) := Id.run do
    let mut m : Std.HashMap String (BinderInfo × String) := {}
    for c in fs.er.commands do
      if c.getKind == ``Parser.Command.variable then
        m := m.insertMany (binderTexts input c[1].getArgs).toList
    return m
  for t in opts.targets do
    let name := t.haveName
    let candidates := fs.sites.filter fun s =>
      declMatches s.decl #[t.decl] && haveDisplayName s == name
        && (match t.line? with | some l => s.line fm == l | none => true)
    let fail (reason : String) : Change :=
      { kind := "extract", decl := t.decl, haveName := name, line := t.line?.getD 0, detail := reason }
    if candidates.isEmpty then
      skipped := skipped.push (fail "no such have (names are the have's own, `this` for anonymous; `@LINE` selects by line)")
      continue
    if candidates.size > 1 then
      skipped := skipped.push (fail s!"ambiguous: lines {candidates.map (·.line fm)}; add `@LINE`")
      continue
    let some s := candidates[0]? | continue
    let line := s.line fm
    let fail (reason : String) : Change := { fail reason with line := line }
    let a ← match ← analyze s with
      | .ok a => pure a
      | .error e => skipped := skipped.push (fail e); continue
    if s.parts.isPattern then
      skipped := skipped.push (fail "destructuring have"); continue
    unless a.letDeps.isEmpty do
      skipped := skipped.push (fail s!"depends on let-bound variables {a.letDeps}, which a lemma signature cannot carry"); continue
    unless a.auxDeps.isEmpty do
      skipped := skipped.push (fail s!"depends on the recursive call {a.auxDeps}"); continue
    let sigTexts := binderTexts input (sigBinders s.cmd)
    let bad := a.deps.filter fun d => !d.roundTrips &&
      !(d.isSig && (sigTexts.contains d.decl.userName.toString || varBinders.contains d.decl.userName.toString))
    unless bad.isEmpty do
      skipped := skipped.push (fail s!"the type of {bad.map (·.decl.userName)} does not survive pretty-printing ({bad.map (·.ppType)}); state it in the source first")
      continue
    -- parameters
    -- (binder kind, names, type text) groups; consecutive binders of one kind and type merge
    let mut groups : Array (BinderInfo × Array String × String) := #[]
    let mut args : Array String := #[]
    for d in a.deps do
      let n := d.decl.userName.toString
      let bi := d.decl.binderInfo
      let explicit := bi matches .default || (!(bi matches .instImplicit) && !d.inferable)
      let bi := if explicit then .default else bi
      let fromSource : Option (BinderInfo × String) :=
        if d.isSig then (sigTexts.get? n).orElse fun _ => varBinders.get? n else none
      let ty := match fromSource with
        | some (_, ty) => ty
        | none => d.ppType
      if bi matches .instImplicit then
        groups := groups.push (bi, #[], d.ppType)
      else
        match groups.back? with
        | some (bi', names, ty') =>
          if bi' == bi && ty' == ty && !names.isEmpty then
            groups := groups.pop.push (bi, names.push n, ty)
          else groups := groups.push (bi, #[n], ty)
        | none => groups := groups.push (bi, #[n], ty)
      if explicit then args := args.push n
    let mut params := ""
    let mut groupTexts : Array String := #[]
    for (bi, names, ty) in groups do
      let text := if names.isEmpty then bracket bi ty else bracket bi s!"{" ".intercalate names.toList} : {ty}"
      params := params ++ " " ++ text
      groupTexts := groupTexts.push text
    for b in s.parts.binders do
      params := params ++ " " ++ stxText input b
      args := args ++ binderNames b
    -- statement
    let haveCol := colOf fm s.range.start
    let typeText := match s.parts.typeStx? with
      | some t => reindent (stxText input t) (colOf fm (t.getRange?.get!.start)) 4 4
      | none => a.ppTy
    -- binder groups wrap at 96 columns, continuation lines indented by four
    let header := Id.run do
      let mut h := s!"{if opts.isPrivate then "private " else ""}{keyword} {t.newName}"
      for g in groupTexts ++ s.parts.binders.map (stxText input ·) do
        if lastLineLength h + 1 + g.length > 96 then h := h ++ "\n    " ++ g
        else h := h ++ " " ++ g
      h ++ " :"
    let stmt := if lastLineLength header + 1 + typeText.length ≤ 96 && !(typeText.any (· == '\n'))
      then header ++ " " ++ typeText else header ++ "\n    " ++ typeText
    -- proof
    let insideClassical := s.path.any fun p => p.getKind == ``Parser.Tactic.classical
    let value := s.parts.valueStx
    let valueR := value.getRange?.get!
    let proofOf (cur : String) (mapPos : String.Pos.Raw → String.Pos.Raw) : String :=
      let classicalLine := if insideClassical then "  classical\n" else ""
      match byItems? value with
      | some items =>
        let r0 := (items[0]!.getRange?).get!
        let r1 := (items.back!.getRange?).get!
        let block := reindent (String.Pos.Raw.extract cur (mapPos r0.start) (mapPos r1.stop)) (colOf fm r0.start) 2 2
        " := by\n" ++ classicalLine ++ "  " ++ block
      | none =>
        let term := reindent (String.Pos.Raw.extract cur (mapPos valueR.start) (mapPos valueR.stop)) haveCol 2 3
        if insideClassical then " := by\n  classical\n  exact " ++ term
        else if (lastLineLength stmt + term.length + 4 ≤ 100) && !(term.any (· == '\n')) then " := " ++ term
        else " :=\n  " ++ term
    let doc := opts.doc?.getD s!"Step `{name}` of the proof of `{s.decl}`, extracted as a lemma."
    let prefixes := Id.run do
      let mut ps := #[]
      let mut c := s.cmd
      while c.getKind == ``Parser.Command.in do
        ps := ps.push (stxText input c[0])
        c := c[2]
      ps
    let needsOpenClassical := a.needsClassical && !insideClassical
      && (input.splitOn "open Classical").length ≤ 1 && (input.splitOn "open scoped Classical").length ≤ 1
    let lemmaText (cur : String) (mapPos : String.Pos.Raw → String.Pos.Raw) : String :=
      let pre := "".intercalate (prefixes.map (· ++ " in\n")).toList
        ++ (if needsOpenClassical then "open scoped Classical in\n" else "")
      pre ++ s!"/-- {doc} -/\n" ++ stmt ++ proofOf cur mapPos ++ "\n\n"
    -- call site: keep the have header verbatim, replace the value
    let callArgs := " ".intercalate args.toList
    let call := t.newName ++ (if callArgs.isEmpty then "" else " " ++ callArgs)
    let headerR : String.Range := { start := s.range.start, stop := s.parts.assignTk.getRange?.get!.stop }
    let headerText := textOf input headerR
    let callText := if lastLineLength headerText + haveCol + 1 + call.length ≤ 100
      then headerText ++ " " ++ call else headerText ++ "\n" ++ spaces (haveCol + 4) ++ call
    let callText := match a.renameLine with
      | some r => r ++ "\n" ++ spaces haveCol ++ callText
      | none => callText
    -- The lemma text is built from the text as it stands when the call-site edit is
    -- applied (inner extractions already done, the value still in place) and stashed;
    -- the insertion before the command, applied later, reads the stash.  Among several
    -- lemmas of one command the inner have (smaller value end) is inserted last, so it
    -- ends up first in the file, before the lemma whose proof calls it.
    let stash ← IO.mkRef ""
    let cmdStart := s.cmd.getRange?.get!.start
    edits := edits.push { start := s.range.start, stop := s.range.stop,
                          build := fun cur mapPos => do stash.set (lemmaText cur mapPos); pure callText,
                          label := s!"callsite {name}" }
    edits := edits.push { start := cmdStart, stop := cmdStart, build := fun _ _ => stash.get,
                          label := s!"lemma {t.newName}", order := valueR.stop.byteIdx }
    changes := changes.push
      { kind := "extract", decl := s.decl.toString, haveName := name, line := line,
        detail := s!"extracted as `{t.newName}` with parameters{params}; call `{call}`"
        ++ (match a.renameLine with | some r => s!" after `{r}`" | none => "") }
  return (edits, changes, skipped)

/-! ## Verification and driver -/

def newErrors (before after : Array Msg) : Array Msg :=
  let old := before.filter (·.isError) |>.map (·.text)
  after.filter fun m => m.isError && !old.contains m.text

def newWarnings (before after : Array Msg) : Array Msg :=
  let old := before.filter (!·.isError) |>.map (·.text)
  after.filter fun m => !m.isError && !old.contains m.text && !(m.text.startsWith "declaration uses 'sorry'")

def changeJson (c : Change) : Json :=
  Json.mkObj [("kind", toJson c.kind), ("declaration", toJson c.decl), ("have", toJson c.haveName),
              ("line", toJson c.line), ("detail", toJson c.detail)]

def msgJson (m : Msg) : Json := Json.mkObj [("line", toJson m.line), ("text", toJson m.text)]

structure Args where
  cmd : String
  file : String
  write : Bool := false
  out? : Option String := none
  clean : CleanOpts := {}
  extract : ExtractOpts := { targets := #[] }
  maxRounds : Nat := 4

def parseTarget (s : String) : Except String Target := do
  let parts := s.splitOn ":"
  unless parts.length == 3 do throw s!"target `{s}` is not DECL:HAVE[@LINE]:NEWNAME"
  let decl := parts[0]!
  let hv := parts[1]!
  let newName := parts[2]!
  let (haveName, line?) := match hv.splitOn "@" with
    | [h, l] => (h, l.toNat?)
    | _ => (hv, none)
  return { decl, haveName, line?, newName }

def parseArgs (args : List String) : Except String Args := do
  match args with
  | cmd :: file :: rest =>
    let mut a : Args := { cmd, file }
    let mut rest := rest
    while !rest.isEmpty do
      match rest with
      | "--write" :: r => a := { a with write := true }; rest := r
      | "--out" :: p :: r => a := { a with out? := some p }; rest := r
      | "--decl" :: d :: r => a := { a with clean := { a.clean with decls := a.clean.decls.push d } }; rest := r
      | "--no-unused" :: r => a := { a with clean := { a.clean with unused := false } }; rest := r
      | "--no-exact" :: r => a := { a with clean := { a.clean with exact := false } }; rest := r
      | "--no-rfl-rw" :: r => a := { a with clean := { a.clean with rflRw := false } }; rest := r
      | "--max-rounds" :: n :: r => a := { a with maxRounds := n.toNat?.getD 4 }; rest := r
      | "--target" :: t :: r =>
        let t ← parseTarget t
        a := { a with extract := { a.extract with targets := a.extract.targets.push t } }; rest := r
      | "--private" :: r => a := { a with extract := { a.extract with isPrivate := true } }; rest := r
      | "--doc" :: d :: r => a := { a with extract := { a.extract with doc? := some d } }; rest := r
      | "--keyword" :: k :: r => a := { a with extract := { a.extract with keyword? := some k } }; rest := r
      | other :: _ => throw s!"unknown argument `{other}`"
      | [] => pure ()
    return a
  | _ => throw "usage: Haves.lean (scan|clean|extract) FILE [options]"

def logLine (msg : String) : IO Unit := IO.eprintln s!"[haves] {msg}"

def elabTimed (path : String) (text : String) (cache : IO.Ref (Option Environment)) (what : String) :
    IO ElabResult := do
  let t0 ← IO.monoMsNow
  let er ← elabFile path text cache
  let t1 ← IO.monoMsNow
  let errs := (er.msgs.filter (·.isError)).size
  logLine s!"{what}: elaborated in {(t1 - t0) / 1000}.{(t1 - t0) % 1000 / 100}s, {errs} error(s), {er.commands.size} commands"
  return er

/-- Apply `edits` to `cur`, verify, and return the new text when it verifies. -/
def verifyEdits (path : String) (cache : IO.Ref (Option Environment)) (base : ElabResult)
    (edits : Array Edit) (what : String) :
    IO (Except (Array Msg × Array Msg) (String × ElabResult)) := do
  let text ← applyEdits base.input edits
  let er ← elabTimed path text cache what
  let errs := newErrors base.msgs er.msgs
  if errs.isEmpty then return .ok (text, er)
  return .error (errs, newWarnings base.msgs er.msgs)

def finish (a : Args) (original : String) (final : String) (verified : Bool)
    (changes skipped : Array Change) (errs warns : Array Msg) (extra : List (String × Json)) : IO UInt32 := do
  let mut written := Json.null
  if verified && final != original then
    if a.write then
      IO.FS.writeFile a.file final
      written := toJson a.file
    else if let some out := a.out? then
      IO.FS.writeFile out final
      written := toJson out
  else if !verified && final != original then
    if let some out := a.out? then
      -- the rejected candidate, for inspection
      IO.FS.writeFile (out ++ ".failed") final
  let report := Json.mkObj ([
    ("file", toJson a.file), ("command", toJson a.cmd), ("verified", toJson verified),
    ("changed", toJson (final != original)),
    ("changes", Json.arr (changes.map changeJson)),
    ("skipped", Json.arr (skipped.map changeJson)),
    ("newErrors", Json.arr (errs.map msgJson)),
    ("newWarnings", Json.arr (warns.map msgJson)),
    ("written", written)] ++ extra)
  IO.println report.pretty
  return if verified then 0 else 1

def main (argv : List String) : IO UInt32 := do
  let a ← match parseArgs argv with
    | .ok a => pure a
    | .error e => IO.eprintln e; return 2
  initSearchPath (← findSysroot)
  let cache ← IO.mkRef (none : Option Environment)
  let input ← IO.FS.readFile a.file
  let er ← elabTimed a.file input cache "original"
  let fs := collectSites er
  match a.cmd with
  | "scan" =>
    let mut items := #[]
    for s in fs.sites do
      let r ← analyze s
      items := items.push (siteJson fs s r (nextSibling s))
    IO.println (Json.arr items).pretty
    return 0
  | "clean" =>
    let mut text := input
    let mut fs := fs
    let mut allChanges := #[]
    let mut allSkipped := #[]
    let mut round := 0
    let mut failed : Std.HashSet (String × String × String) := {}
    let revert (c : Change) (errs : Array Msg) : Change :=
      { c with detail := s!"{c.detail} -- REVERTED: {errs.map (·.text)}" }
    while round < a.maxRounds do
      round := round + 1
      let (edits, changes, skipped) ← cleanEdits fs a.clean failed
      allSkipped := allSkipped ++ skipped
      if edits.isEmpty then break
      logLine s!"round {round}: {edits.size} edit(s)"
      match ← verifyEdits a.file cache fs.er edits s!"round {round}" with
      | .ok (t, er) =>
        text := t; fs := collectSites er; allChanges := allChanges ++ changes
      | .error (errs, _) =>
        -- keep the edits that verify alone; remember the others so later rounds skip them
        logLine s!"round {round}: {errs.size} new error(s); retrying edits one at a time"
        let mut kept := #[]
        let mut keptChanges := #[]
        for i in [0:edits.size] do
          let c := changes[i]!
          if edits.size == 1 then
            failed := failed.insert (c.decl, c.haveName, c.kind)
            allSkipped := allSkipped.push (revert c errs)
            break
          match ← verifyEdits a.file cache fs.er #[edits[i]!] s!"round {round} edit {i+1}" with
          | .ok _ => kept := kept.push edits[i]!; keptChanges := keptChanges.push c
          | .error (es, _) =>
            failed := failed.insert (c.decl, c.haveName, c.kind)
            allSkipped := allSkipped.push (revert c es)
        if kept.isEmpty then continue
        match ← verifyEdits a.file cache fs.er kept s!"round {round} kept" with
        | .ok (t, er) => text := t; fs := collectSites er; allChanges := allChanges ++ keptChanges
        | .error (errs, _) =>
          for c in keptChanges do
            failed := failed.insert (c.decl, c.haveName, c.kind)
            allSkipped := allSkipped.push (revert c errs)
    -- `text` is always the last verified state
    finish a input text true allChanges allSkipped #[] #[] [("rounds", toJson round)]
  | "extract" =>
    if a.extract.targets.isEmpty then
      IO.eprintln "extract: give at least one --target DECL:HAVE[@LINE]:NEWNAME"; return 2
    let (edits, changes, skipped) ← extractEdits fs a.extract
    if edits.isEmpty then
      return ← finish a input input true #[] skipped #[] #[] []
    match ← verifyEdits a.file cache er edits "extracted" with
    | .ok (t, er') =>
      finish a input t true changes skipped #[] (newWarnings er.msgs er'.msgs) []
    | .error (errs, warns) =>
      let candidate ← applyEdits input edits
      finish a input candidate false #[] (skipped ++ changes.map fun c => { c with detail := s!"{c.detail} -- REVERTED" }) errs warns []
  | other =>
    IO.eprintln s!"unknown command `{other}` (scan|clean|extract)"; return 2

end Haves

/-- Imported modules carry `[init]` declarations (environment extensions, `norm_num`
extensions, …); the interpreter runs them only when initializer execution is enabled,
which has to happen before the first `importModules`. -/
def main (argv : List String) : IO UInt32 := do
  unsafe Lean.enableInitializersExecution
  Haves.main argv
