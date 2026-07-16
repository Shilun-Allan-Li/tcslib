/-
  ExtractHaves.lean  —  `#extract_haves TheoremName`

  After `TheoremName` has been elaborated, this command inspects the fully-typed
  proof term and prints a `private lemma` declaration for every `have` binding,
  with correct parameter lists including variables introduced by tactics
  (`funext x`, `rintro x y S`, …) that are invisible to a syntactic transformer.

  ## Usage

      theorem myThm ... := by ...

      #extract_haves myThm

  Prints one `private lemma` per `have` with a `sorry` body.
  Copy the output above the theorem, fill in the proofs, then replace the
  original `have ... := by ...` blocks with calls to the extracted lemmas.

  ## How it works

  1. Look up `TheoremName` in the environment (`ConstantInfo`).
  2. `lambdaTelescope` peels the outermost lambda chain (one per theorem param),
     placing each into the MetaM `LocalContext` as a typed `FVar`.
  3. `walk` recurses through the remaining proof body:
     · `.lam`  (from `intro`/`funext`/…)  → open via `withLocalDecl`, recurse
     · `.letE` (from `have`)               → collect params, emit lemma, recurse
     · `.mdata`                            → strip, recurse
  4. For each `.letE h T V body`, the free FVars of `T` and `V` are retrieved
     in local-context order (theorem params first, then tactic-introduced vars).
     Both regular (`cdecl`) and let-bound (`ldecl`) FVars are included so
     dependent haves list their predecessors as explicit parameters.
  5. Pretty-print while the FVars are live in the MetaM context.
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.PrettyPrinter

open Lean Meta Elab Command

namespace ExtractHaves

-- ── free-variable collection ─────────────────────────────────────────────────
-- Uses Lean.collectFVars (pure, from Lean.Util.CollectFVars) which is stable
-- across Lean versions and avoids any EmptyCollection ambiguity.

private def freeFVarSet (e : Expr) : FVarIdSet :=
  (Lean.collectFVars default e).fvarSet


-- ── helpers ──────────────────────────────────────────────────────────────────

/-- Return `LocalDecl`s for every FVar in `wanted`, in local-context order
    (oldest-first).  Includes both regular and let-bound entries. -/
private def lctxFVarsInOrder (wanted : FVarIdSet) : MetaM (Array LocalDecl) := do
  let lctx ← getLCtx
  let mut result : Array LocalDecl := #[]
  for ldecl? in lctx.decls do
    if let some d := ldecl? then
      if wanted.contains d.fvarId then
        result := result.push d
  return result

/-- Format one parameter binder. -/
private def formatBinder (d : LocalDecl) (typeStr : String) : String :=
  let n := toString d.userName
  match d.binderInfo with
  | .default        => s!"({n} : {typeStr})"
  | .implicit       => s!"\{{n} : {typeStr}}"
  | .strictImplicit => s!"⦃{n} : {typeStr}⦄"
  | .instImplicit   => s!"[{typeStr}]"


-- ── pretty-print helpers ─────────────────────────────────────────────────────

-- `ppExpr` can drop binder type annotations (e.g. `fun hs =>` instead of
-- `fun (hs : Fin 2 → hypercube n) =>`, or `∑ x,` without the range type,
-- or `1 / 2` without `(: ℝ)`).  When the output string is re-elaborated in
-- the EXTRACTED private lemma's context, these missing annotations cause
-- "typeclass instance problem is stuck" or type-mismatch errors.
-- Setting `pp.funBinderTypes := true` instructs the delaborator to always
-- include explicit types in lambda/pi/sum binders, preventing these losses.
private def ppExprFull (e : Expr) : MetaM Format :=
  withOptions (fun o =>
    (o.setBool `pp.funBinderTypes true).setBool `pp.piBinderTypes true)
  (ppExpr e)

-- For inlined proof terms (used in `exact <term>`), we need all implicit
-- arguments to be printed so the term can be re-elaborated in the output file.
-- `pp.all := true` switches off notation (producing `Nat.rawCast`, `Int.negOfNat`
-- etc.) which are internal kernel names not always accessible from user code.
-- Instead we use `pp.explicit := true` (shows @-notation for implicit args while
-- keeping all normal notation) combined with a very high `pp.maxSteps` to prevent
-- `⋯` truncation for large proof terms.  `pp.deepTerms := true` forces Lean to
-- recurse into sub-terms rather than collapsing them.
private def ppExprAllExplicit (e : Expr) : MetaM Format :=
  withOptions (fun o =>
    let o₁ := o.setBool  `pp.funBinderTypes  true
    let o₂ := o₁.setBool `pp.piBinderTypes   true
    let o₃ := o₂.setBool `pp.explicit        true
    let o₄ := o₃.setBool `pp.deepTerms       true
    o₄.setNat             `pp.maxSteps 100000000)
  (ppExpr e)

-- ── core walk ────────────────────────────────────────────────────────────────

/-- Walk a proof `Expr` (with theorem params already FVars), opening any
    remaining lambdas and collecting each `letE` (= `have`) as a snippet. -/
partial def walk (thmName : Name) (e : Expr) : MetaM (Array String) := do
  match e with

  | .lam name type body bi =>
    withLocalDecl name bi type fun fv =>
      walk thmName (body.instantiate1 fv)

  | .letE name type val body _ =>
    if name == `_inaccessible || name.isAnonymous || name == `this then
      withLetDecl name type val fun fv =>
        walk thmName (body.instantiate1 fv)
    else
      let fvars ← lctxFVarsInOrder
                    ((freeFVarSet type).union (freeFVarSet val))
      let mut paramStr := ""
      for d in fvars do
        paramStr := paramStr ++ " " ++ formatBinder d (toString (← ppExprFull d.type))
      let typeStr := toString (← ppExprFull type)
      let auxName  := thmName ++ `aux ++ name
      let snippet  :=
        s!"private lemma {auxName}{paramStr} :\n    {typeStr} := by\n  sorry"
      withLetDecl name type val fun fv => do
        let valSnippets  ← walk thmName val
        let bodySnippets ← walk thmName (body.instantiate1 fv)
        return valSnippets ++ #[snippet] ++ bodySnippets

  | .app f arg =>
    let fs ← walk thmName f
    let as ← walk thmName arg
    return fs ++ as

  | .mdata _ e => walk thmName e
  | _          => return #[]


-- ── anonymous-have type collection ──────────────────────────────────────────

/-- Collect the types of anonymous `letE` bindings (those skipped by `walk`)
    from a proof sub-expression, in depth-first encounter order.
    Does NOT recurse into the `val` of named `letE` bindings, so the result
    contains only the anonymous haves at the CURRENT scope level (not those
    nested inside named-have proofs).
    Called by `walkFull` to provide per-lemma anonymous-have type arrays for
    `inlineOneLinersStep`, which uses them to detect equation-typed `h_auto_N`
    haves that can safely be inlined via Case B/C. -/
partial def walkAnonTypes (e : Expr) : MetaM (Array String) := do
  match e with

  | .lam name type body bi =>
    withLocalDecl name bi type fun fv =>
      walkAnonTypes (body.instantiate1 fv)

  | .letE name type val body _ =>
    if name == `_inaccessible || name.isAnonymous || name == `this then
      -- Anonymous: emit type, then continue into body (not val)
      let typeStr := toString (← ppExprFull type)
      withLetDecl name type val fun fv => do
        let bodyTypes ← walkAnonTypes (body.instantiate1 fv)
        return #[typeStr] ++ bodyTypes
    else
      -- Named: skip val (belongs to inner scope), continue into body
      withLetDecl name type val fun fv =>
        walkAnonTypes (body.instantiate1 fv)

  | .app f arg =>
    let fs ← walkAnonTypes f
    let as ← walkAnonTypes arg
    return fs ++ as

  | .mdata _ e => walkAnonTypes e
  | _          => return #[]


-- ── anonymous-have inlined-term collection ──────────────────────────────

/-- For each anonymous `letE` binding in a proof body, compute the ppExpr of
    the INLINED continuation: `body.instantiate1 val`.  This is the proof term
    with the anonymous have eliminated — emitting `exact <term>` with this
    string closes the goal without needing the intermediate `have` hypothesis.
    Returns an array aligned with `walkAnonTypes` (same depth-first order). -/
partial def walkAnonInlinedTerms (e : Expr) : MetaM (Array String) := do
  match e with

  | .lam name type body bi =>
    withLocalDecl name bi type fun fv =>
      walkAnonInlinedTerms (body.instantiate1 fv)

  | .letE name type val body _ =>
    if name == `_inaccessible || name.isAnonymous || name == `this then
      -- Inline: substitute val into body, then print the result.
      -- Use pp.all := true so ALL implicit arguments are printed explicitly —
      -- otherwise the delaborator omits implicits that were inferred in MetaM
      -- but can't be re-inferred when the term is re-elaborated in the output file.
      let inlined := body.instantiate1 val
      let termStr := toString (← ppExprAllExplicit inlined)
      withLetDecl name type val fun fv => do
        let bodyTerms ← walkAnonInlinedTerms (body.instantiate1 fv)
        return #[termStr] ++ bodyTerms
    else
      -- Named: only recurse into body (val belongs to inner scope)
      withLetDecl name type val fun fv =>
        walkAnonInlinedTerms (body.instantiate1 fv)

  | .app f arg =>
    let fs ← walkAnonInlinedTerms f
    let as ← walkAnonInlinedTerms arg
    return fs ++ as

  | .mdata _ e => walkAnonInlinedTerms e
  | _          => return #[]


-- ── named-have inlined-term collection ──────────────────────────────────────

/-- For each NAMED `letE` binding in the outer proof scope (DFS order), compute
    the ppExpr of the INLINED continuation: `body.instantiate1 val`.
    This is the proof of the rest-of-theorem with this named have substituted in.
    Emitting `exact <term>` with this string closes the goal without the `have`.
    Returns Array (haveName, termStr).
    Does NOT recurse into named letE values (inner scopes are handled by walkFull).
    Used by `eliminateNamedHavesWithInlinedTerms` in ExtractHavesFile. -/
partial def walkNamedInlinedTerms (e : Expr) : MetaM (Array (String × String)) := do
  match e with

  | .lam name type body bi =>
    withLocalDecl name bi type fun fv =>
      walkNamedInlinedTerms (body.instantiate1 fv)

  | .letE name type val body _ =>
    if name == `_inaccessible || name.isAnonymous || name == `this then
      withLetDecl name type val fun fv =>
        walkNamedInlinedTerms (body.instantiate1 fv)
    else
      let inlined := body.instantiate1 val
      let termStr := toString (← ppExprAllExplicit inlined)
      withLetDecl name type val fun fv => do
        -- Only recurse into body (continuation), not val (inner scope)
        let bodyResults ← walkNamedInlinedTerms (body.instantiate1 fv)
        return #[(toString name, termStr)] ++ bodyResults

  | .app f arg =>
    let fs ← walkNamedInlinedTerms f
    let as ← walkNamedInlinedTerms arg
    return fs ++ as

  | .mdata _ e => walkNamedInlinedTerms e
  | _          => return #[]


-- ── enriched walk (used by #extract_haves_file) ───────────────────────────

/-- Like `walk`, but also collects for each named `letE`'s `val`:
    · `valAnonTypes`        — types of anonymous haves (for equation detection)
    · `valAnonInlinedTerms` — inlined continuations of anonymous haves (for
                               `exact <term>` emission to eliminate context-
                               dependent haves without needing the `have`)
    Returns `Array (snippet, valAnonTypes, valAnonInlinedTerms)`. -/
partial def walkFull (thmName : Name) (e : Expr) : MetaM (Array (String × Array String × Array String)) := do
  match e with

  | .lam name type body bi =>
    withLocalDecl name bi type fun fv =>
      walkFull thmName (body.instantiate1 fv)

  | .letE name type val body _ =>
    if name == `_inaccessible || name.isAnonymous || name == `this then
      withLetDecl name type val fun fv =>
        walkFull thmName (body.instantiate1 fv)
    else
      let fvars ← lctxFVarsInOrder
                    ((freeFVarSet type).union (freeFVarSet val))
      let mut paramStr := ""
      for d in fvars do
        paramStr := paramStr ++ " " ++ formatBinder d (toString (← ppExprFull d.type))
      let typeStr := toString (← ppExprFull type)
      let auxName  := thmName ++ `aux ++ name
      let snippet  :=
        s!"private lemma {auxName}{paramStr} :\n    {typeStr} := by\n  sorry"
      -- Collect anon types and inlined terms from THIS named have's val.
      let valAnonTypes        ← walkAnonTypes val
      let valAnonInlinedTerms ← walkAnonInlinedTerms val
      withLetDecl name type val fun fv => do
        let valResults  ← walkFull thmName val
        let bodyResults ← walkFull thmName (body.instantiate1 fv)
        return valResults ++ #[(snippet, valAnonTypes, valAnonInlinedTerms)] ++ bodyResults

  | .app f arg =>
    let fs ← walkFull thmName f
    let as ← walkFull thmName arg
    return fs ++ as

  | .mdata _ e => walkFull thmName e
  | _          => return #[]


-- ── command ──────────────────────────────────────────────────────────────────

/--
`#extract_haves TheoremName`

Inspects the elaborated proof and prints a `private lemma` for each `have`,
with correct parameter lists including tactic-introduced variables.
Proof bodies are `sorry`; copy them from the original source.
-/
elab "#extract_haves " name:ident : command => do
  let thmName ← resolveGlobalConstNoOverload name
  let ci      ← getConstInfo thmName
  let val ← match ci.value? with
    | some v => pure v
    | none   => throwError
        s!"#extract_haves: '{thmName}' has no proof value (axiom or opaque?)"
  let snippets ← liftTermElabM <| MetaM.run' do
    lambdaTelescope val fun _ body =>
      walk thmName body
  if snippets.isEmpty then
    logInfo s!"#extract_haves: no `have` blocks found in '{thmName}'"
  else
    logInfo (s!"-- Extracted from {thmName}\n" ++
             "\n\n".intercalate snippets.toList)

end ExtractHaves
