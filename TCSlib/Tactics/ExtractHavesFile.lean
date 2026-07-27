/-
  ExtractHavesFile.lean  —  `#extract_haves_file "path/to/File.lean"`  [v7]

  Reads a Lean source file (which must already be imported so its theorems
  are in the current environment), extracts every `have` block from every
  non-private theorem/lemma, and writes the refactored file next to the
  original as `File_output.lean`.

  For each `have h : T := by ...` the command:
    1. Calls `ExtractHaves.walk` on the elaborated proof term — this gives
       the correct parameter list and type for `h` using the actual tactic
       state, without any source-level guessing.
    2. Searches the source text (line-by-line) to find the matching `have h`
       block and extract the original proof body.
    3. Emits a `private lemma thmName_aux_h params : T := by <body>` before
       the theorem and replaces the `have` block with a ONE-LINER call.

  v8 changes (2026-06-29):
    · Root Cause 1: `preprocessBodyLines` Case 3 — split mid-line `have` after `;`
      (e.g. `"· funext j; have hj := term; rest"`) so `inlineOneLinersStep` can see it.
    · Root Cause 2: Preserve `have` when `simp_all +decide` is in scope — those calls
      need a local hypothesis, not just an injected term.
    · Root Cause 3: Case C injection no longer skips simp_all lines that contain `hName`
      elsewhere (e.g. `"unfold X at h; simp_all [Y]"`); old guard caused missed injection.

  Limitations (known):
    · The theorem must be in the current environment (the calling file must
      import it).  Use `#extract_haves` first to check types if unsure.
    · Deeply nested `have` DAGs with cross-references are extracted in the
      order `walk` visits them (DFS), which may not always be the right
      dependency order.  Leaf haves are always safe.
    · The call site is always ONE-LINER (`have h : T := call`); FULL
      substitution (removing the `have` entirely) is not yet implemented.
-/

import Lean
import Lean.Elab.Command
import Lean.Meta.Basic
import TCSlib.Tactics.ExtractHaves

open Lean Meta Elab Command ExtractHaves

namespace ExtractHavesFile

-- ── String / line utilities ───────────────────────────────────────────────

private def lineIndent (s : String) : Nat :=
  s.length - s.trimLeft.length

private def isBlankLine (s : String) : Bool :=
  let t := s.trim
  t.isEmpty || t.startsWith "--"

/-- First line index ≥ `start` where a non-empty line (including comments)
    has indent ≤ `base`.  Comments at ≤ base indent correctly end the block;
    only truly empty lines are skipped. -/
private def blockEnd (lines : Array String) (start base : Nat) : Nat :=
  let rec go (i : Nat) : Nat :=
    if i ≥ lines.size then lines.size
    else if !lines[i]!.trim.isEmpty && lineIndent lines[i]! ≤ base then i
    else go (i + 1)
  go start

/-- Split `s` at the first `;` that is NOT inside parentheses, brackets, or braces.
    Returns `some (before.trimRight, after.trimLeft)` or `none` if no such `;` exists.
    Tracks `()`, `[]`, `{}`, and `⟨⟩` to avoid splitting inside compound terms. -/
private def splitAtOuterSemi (s : String) : Option (String × String) := Id.run do
  let chars := s.toList.toArray
  let mut depth := 0
  for i in List.range chars.size do
    let c := chars[i]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then
      if depth > 0 then depth := depth - 1
    else if c == ';' && depth == 0 then
      let before := String.mk (chars.extract 0 i).toList
      let after  := String.mk (chars.extract (i + 1) chars.size).toList
      return some (before.trimRight, after.trimLeft)
  return none

/-- Split `s` at the first `:=` NOT inside parentheses/brackets/braces — the
    have/lemma HEADER–BODY separator. A naive `splitOn ":="` breaks on types
    containing NAMED ARGUMENTS (`(Finset.univ (α := Fin T)).filter ...`) or
    default-valued binders: the split lands INSIDE the type, truncating the
    header mid-parenthesis and producing a synthetic probe so malformed it
    fails with zero messages (observed: `potential_zero`'s `hfilt` and
    `cumLoss_succ`'s anonymous have in `Hedge.lean`). Returns
    `some (before, after)` with the `:=` itself dropped. -/
private def splitAtTopLevelAssign (s : String) : Option (String × String) := Id.run do
  let chars := s.toList.toArray
  let n := chars.size
  let mut depth := 0
  let mut i := 0
  while i < n do
    let c := chars[i]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' || c == '⦃' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' || c == '⦄' then
      if depth > 0 then depth := depth - 1
    else if c == ':' && depth == 0 && i + 1 < n && chars[i + 1]! == '=' then
      return some (String.mk (chars.extract 0 i).toList,
                   String.mk (chars.extract (i + 2) n).toList)
    i := i + 1
  return none

/-- Split `s` at the first `→` at top-level bracket depth — used to peel one
    arrow antecedent off a captured telescope (`T₁ → rest`); nested arrows
    inside parenthesized antecedents don't count. Returns
    `some (antecedent, rest)` with the arrow dropped. -/
private def splitAtTopLevelArrow (s : String) : Option (String × String) := Id.run do
  let chars := s.toList.toArray
  let n := chars.size
  let mut depth := 0
  let mut i := 0
  while i < n do
    let c := chars[i]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' || c == '⦃' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' || c == '⦄' then
      if depth > 0 then depth := depth - 1
    else if c == '→' && depth == 0 then
      return some (String.mk ((chars.extract 0 i).toList),
                   String.mk ((chars.extract (i + 1) n).toList))
    i := i + 1
  return none

/-- A copy of `lines` with comment-interior lines blanked, for SCOPE SCANNERS
    only (`enclosingOpensFor`/`...SetOptionsFor`/`...VariablesFor`,
    `setBoundNamesInPrefix`) — never for content that gets replayed or
    written. Line-start scanners otherwise ingest PROSE: `Entropy.lean` has
    docstring lines literally beginning with the word "variable" (mid-
    sentence, at the docstring's closing line), which the variable-scanner
    matched and emitted with an appended `in` — parse garbage poisoning every
    probe. Line-level approximation: a line that STARTS inside a block
    comment (docstrings included) is blanked, as are whole-line `--`
    comments; block depth is tracked by counting open/close tokens per
    line. -/
private def maskCommentLines (lines : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut depth : Nat := 0
  for l in lines do
    let startsInside := depth > 0
    let opens := (l.splitOn "/-").length - 1
    let closes := (l.splitOn "-/").length - 1
    depth := depth + opens - closes
    if startsInside || l.trimLeft.startsWith "--" then
      out := out.push ""
    else
      out := out.push l
  return out

/-- Let-replay is DISABLED for whole-file runs: even with once-per-have
    limiting and 200K-heartbeat caps on both gates, the retries pushed full
    Entropy.lean runs past 116 CPU-minutes (baseline ~60) across four
    attempts. The mechanism itself is sound (see `letDefsInPrefix`) — the
    COST STRUCTURE is wrong for the inline path, where every retry
    re-elaborates a heavyweight theorem inside the one long-running driver
    command. Its home is `#extract_haves_iter_decl`: one declaration per
    invocation on a fresh server, which SETS this ref; the whole-file
    command clears it defensively. -/
initialize letReplayEnabledRef : IO.Ref Bool ← IO.mkRef false

/-- Probe `autoImplicit` mode MUST follow the SOURCE file's own setting
    (check-context = write-context, both directions). The probes historically
    forced `autoImplicit false` unconditionally — right for the common file
    that sets it false itself (without forcing, a genuinely-missing
    identifier silently auto-generalizes and the check falsely passes), but
    WRONG for a file that RELIES on autoImplicit (Circuit.lean: no
    `variable`, `theorem toNAnd_toNOr_size_le (c : Circuit n)` auto-binds
    `n`) — there every probe dies with "Unknown identifier `n`" while the
    written output (which inherits the source's settings) compiles fine.
    Drivers set this per source file: true ⟺ the file does NOT set
    `set_option autoImplicit false` at file level. Default false = the
    historical safe behavior. -/
initialize probeAutoImplicitRef : IO.Ref Bool ← IO.mkRef false

/-- Probe/rejection logs normally publish only when the whole driver command
    COMPLETES — on a disk-tight machine whose auto-stop kills the server
    mid-decl (CircuitTreeManip, twice), that loses the exact rejection dumps
    needed to diagnose the failing class. When set (by the per-decl driver, to
    `<output>.probelog`), every probe log line is ALSO appended here, so a
    killed run still leaves the diagnosis material on disk. The `--cleanup`
    scanner deletes it with the other `_iter_output` scratch. -/
initialize probeLogPathRef : IO.Ref (Option String) ← IO.mkRef none

/-- `(name, rhs)` pairs for `set NAME (: T)? := RHS (with h)?` and tactic
    `let NAME (: T)? := RHS` lines in a replayed prefix at indent ≤
    `maxIndent` — the LET-REPLAY rung's inputs: a proof that references a
    let-bound name inside a simp/rw bracket delta-unfolds it, which an
    extracted lemma's opaque parameter cannot do ("Invalid argument: Variable
    `Z` is not a proposition or let-declaration"). The rung adds an equation
    parameter `(hZdef : Z = RHS)`, rewrites the bracket references to use it
    (same rewrite direction as the delta-unfold), and passes `rfl` at the
    callsite, where the ldecl IS transparent. -/
private def letDefsInPrefix (prefixText : String) (maxIndent : Nat) : List (String × String) :=
  let masked := (maskCommentLines (prefixText.splitOn "\n").toArray).toList
  masked.foldl (init := []) fun acc l =>
    if !l.trim.isEmpty && lineIndent l > maxIndent then acc else
    let t := l.trim
    let afterKw :=
      if t.startsWith "set " then some (t.drop 4)
      else if t.startsWith "let " then some (t.drop 4)
      else none
    match afterKw with
    | none => acc
    | some rest =>
      match splitAtTopLevelAssign rest with
      | none => acc
      | some (nameAndTy, rhs0) =>
        let nm := (match nameAndTy.splitOn " : " with
          | n :: _ => n
          | [] => nameAndTy).trim
        let rhs1 := (match splitAtOuterSemi rhs0.trimLeft with
          | some (r, _) => r
          | none => rhs0).trim
        -- `set X := RHS with h` — the `with` clause is not part of the RHS
        let rhs := (match rhs1.splitOn " with " with
          | r :: _ => r
          | [] => rhs1).trim
        if nm.length > 0 && rhs.length > 0 &&
           !nm.any (fun c => c == ' ' || c == '⟨' || c == '(' || c == ',') then
          acc ++ [(nm, rhs)]
        else acc

/-- Names bound by `set NAME (: TYPE)? := BODY (with H)?` (and tactic-mode
    `let NAME := ...`) lines in a replayed tactic prefix, deduped, in REVERSE
    source order (later definitions first — the safe order to `clear_value`
    them, since a later definition's body may mention an earlier one).

    Why probes need these: `set` introduces a local DEFINITION (an ldecl),
    which `extract_goal` cannot render as a theorem parameter. It either
    appears as a `let x := ...;` inside the captured RETURN TYPE — after which
    every remaining binder, including the reverted have itself, degrades to an
    unnamed arrow, defeating `parseRevertedSignature` — or is referenced
    without being bound at all (assembled lemma fails "Unknown identifier
    `x`"). Both observed on `Hedge.lean` (every PROBE_FAILED theorem there
    uses `set`). Probes therefore RETRY with `clear_value x ...` inserted,
    stripping the ldecls' values so they become opaque fvars that capture as
    ordinary `(x : τ)` groups — which the real callsite context can supply,
    since `x` exists there. Proofs that relied on the definition being
    TRANSPARENT (rather than on `set ... with h` equations, which survive as
    ordinary hypotheses) fail that probe too and gracefully stay inline. -/
private def setBoundNamesInPrefix (prefixText : String) (maxIndent : Nat) : List String :=
  let masked := (maskCommentLines (prefixText.splitOn "\n").toArray).toList
  -- Only lines at indent ≤ the target have's own indent are still IN SCOPE
  -- at the probe point: a `set F := ...`/`let F := ...` nested inside an
  -- EARLIER have's by-block is gone by then, and `clear_value F` on a
  -- non-existent/non-ldecl name kills the whole probe variant ("Variable `F`
  -- is not a proposition or let-declaration", observed on Entropy.lean).
  let names := masked.foldl (init := []) fun acc l =>
    if !l.trim.isEmpty && lineIndent l > maxIndent then acc else
    let t := l.trim
    let afterKw :=
      if t.startsWith "set " then some (t.drop 4)
      else if t.startsWith "let " then some (t.drop 4)
      else none
    match afterKw with
    | none => acc
    | some rest =>
      match rest.splitOn " := " with
      | nameAndTy :: _ :: _ =>
        let nm := (match nameAndTy.splitOn " : " with
          | n :: _ => n
          | [] => nameAndTy).trim
        -- a single plain identifier only — no destructuring patterns
        if nm.length > 0 &&
           !nm.any (fun c => c == ' ' || c == '⟨' || c == '⟩' || c == '(' ||
                             c == ')' || c == ',') then
          acc ++ [nm]
        else acc
      | [nameOnly] =>
        -- match-lambda ldecl: `let NAME : TYPE` with `| pat => ...` arms on
        -- the FOLLOWING lines — no ` := ` on the let line, but the ldecl is
        -- just as real, and just as capture-defeating (SATTo3SAT's
        -- `let ml : Literal V → ...`: everything after it in context printed
        -- as an anonymous let-telescope, 0/4). Require the ` : ` ascription
        -- so `let` continuation text never matches.
        match nameOnly.splitOn " : " with
        | nm0 :: _ :: _ =>
          let nm := nm0.trim
          if nm.length > 0 &&
             !nm.any (fun c => c == ' ' || c == '⟨' || c == '⟩' || c == '(' ||
                               c == ')' || c == ',') then
            acc ++ [nm]
          else acc
        | _ => acc
      | _ => acc
  names.eraseDups.reverse

/-- Find the best `have name` line in `lines[from..]`.
    Collects ALL tactic-mode occurrences, then picks by topology:
    · One occurrence              → return it.
    · Multiple, same indent       → SEQUENTIAL haves → return the FIRST (forward order).
    · Multiple, different indents → NESTED haves    → return the LAST (innermost/deepest).
    Falls back to last term-mode when no tactic-mode exists.

    Sequential case: `walk` visits haves in forward source order, so snip[0] belongs to
    the FIRST tactic-mode occurrence; returning first here keeps sig and body aligned.
    Nested case: `walk` visits inner before outer (post-order DFS), so the innermost
    have must match when no prior inner one-liner has displaced it. -/
private def findHaveLine (lines : Array String) (name : String) (from_ : Nat) : Option Nat :=
  let hasTacticInBlock (start base : Nat) : Bool := Id.run do
    let mut j := start
    while j < lines.size do
      let lj := lines[j]!
      if !lj.trim.isEmpty && lineIndent lj ≤ base then return false
      if (lj.splitOn ":= by").length ≥ 2 then return true
      j := j + 1
    return false
  Id.run do
    let mut tacticOccs : Array Nat := #[]
    let mut termOccs   : Array Nat := #[]
    let mut i := from_
    while i < lines.size do
      let l := lines[i]!
      let t := l.trimLeft
      -- A `have` may share its source line with a `·` bullet (`"· have h : T := ..."`);
      -- strip the bullet before matching so bullet-attached haves are still found.
      let tCore := if t.startsWith "· " then t.drop 2 else t
      let isHeader := tCore.startsWith ("have " ++ name ++ " :") || tCore.startsWith ("have " ++ name ++ ":")
      let isTactic :=
        if (t.splitOn ":= by").length ≥ 2 then true
        else if isHeader then hasTacticInBlock (i + 1) (lineIndent l)
        else false
      let isTermMode := isHeader && !isTactic && (t.splitOn ":=").length ≥ 2
      if isHeader && isTactic  then tacticOccs := tacticOccs.push i
      if isHeader && isTermMode then termOccs  := termOccs.push i
      i := i + 1
    -- No tactic-mode: fall back to last term-mode.
    if tacticOccs.isEmpty then
      return if termOccs.isEmpty then none else some termOccs[termOccs.size - 1]!
    -- Single tactic-mode: unambiguous.
    if tacticOccs.size == 1 then
      return some tacticOccs[0]!
    -- Multiple tactic-mode occurrences: distinguish sequential vs nested by indent.
    -- Sequential (same indent): `walk` visits in forward source order → return FIRST.
    -- Nested (different indents): `walk` visits inner before outer → return LAST (innermost).
    let indent0 := lineIndent lines[tacticOccs[0]!]!
    let allSameIndent := tacticOccs.all fun idx => lineIndent lines[idx]! == indent0
    return if allSameIndent then some tacticOccs[0]! else some tacticOccs[tacticOccs.size - 1]!

/-- Extract the proof body text from a have block starting at `haveIdx`.
    Returns (bodyText, endIdx).
    The body is everything after `:= by` (or `:=`), de-indented. -/
private def extractHaveBody (lines : Array String) (haveIdx : Nat) : String × Nat :=
  let haveLine := lines[haveIdx]!
  let bulletIndent := lineIndent haveLine
  -- A `have` sharing its line with a `·` bullet has its actual content starting 2
  -- columns past the bullet; sibling tactics after it are aligned to THAT column
  -- (not the bullet's column), so scope must be measured from the content column
  -- or a sibling tactic would be mistaken for part of this have's proof body.
  let base := if haveLine.trimLeft.startsWith "· " then bulletIndent + 2 else bulletIndent
  let endIdx  := blockEnd lines (haveIdx + 1) base
  -- Collect all lines of the block (including the have header)
  let block   := (lines.extract haveIdx endIdx).toList
  let joined  := "\n".intercalate block
  -- Split on ":= by" to extract only what comes after the FIRST occurrence,
  -- while preserving any nested ":= by" occurrences intact.
  let afterBy :=
    match joined.splitOn ":= by" with
    | _ :: rest => ":= by".intercalate rest  -- rejoin remaining parts with ":= by"
    | []        => ""
  -- If not found, try plain ":=" (term-mode proof) — at TOP LEVEL only: a
  -- `:=` can sit inside the have's TYPE (named arguments like `(α := Fin T)`),
  -- and splitting there would hand back the tail of the type as the "body".
  let rawBody :=
    if afterBy.isEmpty then
      match splitAtTopLevelAssign joined with
      | some (_, rest) =>
        let afterEq := rest.trimLeft
        -- For term-mode, stop at the first outer semicolon so that same-line
        -- continuation tactics ("have h := term; rw at h; exact h") are not
        -- included in the body — they stay in the theorem and handle the binding.
        match splitAtOuterSemi afterEq with
        | some (termPart, _) => termPart
        | none               => afterEq
      | none => ""
    else afterBy
  -- De-indent: remove the common leading indent from non-blank lines
  let bodyLines  := rawBody.splitOn "\n"
  let nonBlank   := bodyLines.filter fun l => !l.trim.isEmpty
  let minIndent  := nonBlank.foldl (fun acc l => Nat.min acc (lineIndent l)) 1000
  let deindented := bodyLines.map fun l =>
    if l.length > minIndent && !l.trim.isEmpty then
      l.drop minIndent
    else l.trim
  ("\n".intercalate deindented |>.trim, endIdx)

-- ── Parsing the walk output ───────────────────────────────────────────────

structure HaveEntry where
  haveName             : String         -- e.g. "h_fx"
  sig                  : String         -- "private lemma thmName_aux_h_fx {n} (f) ... : T"
  valAnonTypes         : Array String   -- types of anonymous haves in the proof body (from walkFull)
  valAnonInlinedTerms  : Array String   -- inlined continuations for anonymous haves (from walkFull)

/-- Parse one snippet (from `walkFull`) together with its anonymous-have arrays.
    Snippet format: "private lemma Foo.aux.bar {params} :\n    T := by\n  sorry"
    We want:  haveName = "bar",  sig = "private lemma Foo_aux_bar {params} : T"
    `anonTypes` are the types of anonymous haves in this lemma's proof body.
    `anonInlinedTerms` are the inlined continuations for those anonymous haves —
    used to emit `exact <term>` when simp_all context-dependence prevents inlining. -/
private def parseSnippet (snippet : String) (anonTypes : Array String := #[]) (anonInlinedTerms : Array String := #[]) : Option HaveEntry := do
  let body := snippet.trim
  -- Must start with "private lemma "
  if !body.startsWith "private lemma " then failure
  let afterPL := body.drop "private lemma ".length
  -- Lemma name ends at first space / '{' / '(' / '\n'
  let nameStop := afterPL.find (fun c => c == ' ' || c == '{' || c == '(' || c == '\n')
  let dotName  := String.Pos.Raw.extract afterPL ⟨0⟩ nameStop   -- e.g. "Foo.aux.bar"
  -- Split on ".aux." to recover have name
  let parts := dotName.splitOn ".aux."
  let haveName ← if parts.length == 2 then some parts[1]! else none
  let thmDotPart := parts[0]!
  -- Build underscore-style external name
  let extName := thmDotPart ++ "_aux_" ++ haveName
  -- Signature = everything before ":= by\n  sorry" — strip that suffix
  let sigBody :=
    match body.splitOn ":= by" with
    | [before, _] => before.trimRight
    | _           => body.trimRight
  -- Replace Lean dot-name with underscore name in the signature line
  let sig := sigBody.replace dotName extName
  return { haveName, sig, valAnonTypes := anonTypes, valAnonInlinedTerms := anonInlinedTerms }

-- ── Theorem finder ────────────────────────────────────────────────────────

structure ThmSpan where
  name        : String   -- short (unqualified) name, for source-level searching
  fullName    : String   -- fully qualified with namespaces, for env lookup
  headerStart : Nat      -- first line of the theorem declaration
  bodyStart   : Nat      -- first line after `:= by`
  bodyEnd     : Nat      -- first line after the body (exclusive)

/-- Scan source lines to find all non-private theorem/lemma declarations
    that have a `:= by` proof.  Tracks `namespace` declarations so that
    `fullName` matches the constant name in the Lean environment. -/
private def findTheorems (lines : Array String) : Array ThmSpan := Id.run do
  let isDecl (l : String) : Option String :=
    let tryPfx (pfx : String) : Option String :=
      if l.startsWith pfx then
        let rest := l.drop pfx.length
        let nameEnd := rest.find (fun c => c == ' ' || c == '{' || c == '(' || c == ':')
        some (String.Pos.Raw.extract rest ⟨0⟩ nameEnd)
      else none
    (["theorem ", "lemma "] : List String).findSome? tryPfx
  let mut nsStack  : Array String := #[]   -- current namespace stack
  let mut result   : Array ThmSpan := #[]
  let mut i := 0
  while i < lines.size do
    let l  := lines[i]!
    let lt := l.trim
    -- Track namespace boundaries (sections don't affect names)
    if lt.startsWith "namespace " then
      nsStack := nsStack.push (lt.drop "namespace ".length |>.takeWhile (· != ' '))
    else if lt.startsWith "end " then
      -- Pop only if the end-name matches the top of the namespace stack
      let endName := (lt.drop "end ".length).trim
      if let some top := nsStack.back? then
        if top == endName then nsStack := nsStack.pop
    -- Skip private and indented (nested) declarations
    if !l.startsWith "private " && !l.startsWith "  " then
      if let some name := isDecl l then
        let ns       := ".".intercalate nsStack.toList
        let fullName := if ns.isEmpty then name else ns ++ "." ++ name
        -- Scan forward to find `:= by`
        let mut j     := i
        let mut found := false
        while j < lines.size && !found do
          if (lines[j]!.splitOn ":= by").length ≥ 2 then
            found := true
          else
            j := j + 1
            if j < lines.size && !isBlankLine lines[j]! && lineIndent lines[j]! == 0 && j > i then
              j := lines.size  -- next top-level decl without `:= by`
        if found then
          let bodyStart := j + 1
          let bodyEnd   := blockEnd lines bodyStart 0
          result := result.push { name, fullName, headerStart := i, bodyStart, bodyEnd }
          i := bodyEnd
          continue
    i := i + 1
  result

/-- Like `findTheorems`, but ALSO includes `private` declarations, and only
    returns `(bodyStart, bodyEnd)` bounds (no namespace/`fullName` tracking needed
    for this use). Used by `#extract_haves_iter_to`'s final cleanup pass so an
    EXTRACTED private lemma's own body (which `findTheorems` would skip, since it
    explicitly excludes `private`) still gets the have-inlining treatment — e.g.
    a call to a SIBLING extracted lemma sitting inside it. -/
private def findAllDeclSpans (lines : Array String) : Array (Nat × Nat) := Id.run do
  let isDecl (l : String) : Bool :=
    (["theorem ", "lemma ", "private theorem ", "private lemma "] : List String).any l.startsWith
  let mut result : Array (Nat × Nat) := #[]
  let mut i := 0
  while i < lines.size do
    let l := lines[i]!
    if !l.startsWith "  " && isDecl l then
      let mut j := i
      let mut found := false
      while j < lines.size && !found do
        if (lines[j]!.splitOn ":= by").length ≥ 2 then
          found := true
        else
          j := j + 1
          if j < lines.size && !isBlankLine lines[j]! && lineIndent lines[j]! == 0 && j > i then
            j := lines.size
      if found then
        let bodyStart := j + 1
        let bodyEnd := blockEnd lines bodyStart 0
        result := result.push (bodyStart, bodyEnd)
        i := bodyEnd
        continue
    i := i + 1
  return result

-- ── One-liner inlining ────────────────────────────────────────────────────

/-- True if `c` is a Lean identifier character. -/
private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Replace every standalone occurrence of `name` in `line` with `replacement`.
    "Standalone" = not adjacent to identifier characters on either side.
    Implemented with an imperative loop to avoid termination annotations. -/
private def replaceWord (line name replacement : String) : String := Id.run do
  if name.isEmpty then return line
  let chars := line.toList.toArray
  let nArr  := name.toList.toArray
  let rArr  := replacement.toList.toArray
  let n     := nArr.size
  let mut out : Array Char := #[]
  let mut i := 0
  while i < chars.size do
    -- Try to match `name` starting at position i (only if enough chars remain)
    let matched :=
      i + n ≤ chars.size &&
      (List.range n).all (fun k => chars[i + k]! == nArr[k]!)
    if matched then
      let prevOk := i == 0 || !isIdentChar chars[i - 1]!
      let nextOk := i + n ≥ chars.size || !isIdentChar chars[i + n]!
      if prevOk && nextOk then
        out := out ++ rArr
        i := i + n
      else
        out := out.push chars[i]!
        i := i + 1
    else
      out := out.push chars[i]!
      i := i + 1
  return String.mk out.toList

/-- True if `line` contains `name` as a standalone word. -/
private def containsWord (line name : String) : Bool := Id.run do
  if name.isEmpty then return false
  let chars := line.toList.toArray
  let nArr  := name.toList.toArray
  let n     := nArr.size
  for i in List.range chars.size do
    let matched :=
      i + n ≤ chars.size &&
      (List.range n).all (fun k => chars[i + k]! == nArr[k]!)
    if matched then
      let prevOk := i == 0 || !isIdentChar chars[i - 1]!
      let nextOk := i + n ≥ chars.size || !isIdentChar chars[i + n]!
      if prevOk && nextOk then return true
  return false

/-- True if `name` appears in a position that cannot be inlined:
    `tac at name`, `specialize name …`, `rcases name …`. -/
private def isNonInlineableUse (line name : String) : Bool :=
  let hasAtUse : Bool :=
    let parts := line.splitOn (" at " ++ name)
    if parts.length < 2 then false
    else
      let after := parts[1]!
      after.isEmpty || !isIdentChar after.front
  let lt := line.trimLeft
  hasAtUse || lt.startsWith ("specialize " ++ name) || lt.startsWith ("rcases " ++ name)

/-- True if `line` uses all local hypotheses as simp rules (`simp_all` or `simp [*]`).
    Note: these may appear after a `·` or `;` on the same line, so we check
    for the substring anywhere in `line`. -/
private def usesSimpAllOrStar (line : String) : Bool :=
  (line.splitOn "simp_all").length ≥ 2 ||
  ((line.splitOn "simp").length ≥ 2 &&
   ((line.splitOn "[*]").length ≥ 2 || (line.splitOn "[ *]").length ≥ 2))

/-- True if `line` contains a tactic that absorbs local hypotheses but cannot
    accept an explicit term injection (unlike `simp_all`). -/
private def hasAbsorbingTactic (line : String) : Bool :=
  (line.splitOn "aesop").length ≥ 2

/-- True if `line` contains `simp_all` with the `+decide` flag.
    `simp_all +decide` uses local `have` hypotheses for forward reasoning
    (not just as rewrite rules), so a `let` binding or an injected term
    expression cannot substitute for a `have` hypothesis in these calls. -/
private def hasSimpAllPlusDecide (line : String) : Bool :=
  (line.splitOn "simp_all").length ≥ 2 &&
  (line.splitOn "+decide").length ≥ 2

/-- True if `line` has a `rw [...] at` call BEFORE a `simp_all` call (separated by `;`
    or `<;>`).  When `rw [...] at *` precedes `simp_all`, Lean rewrites local hypotheses
    (including the `have h` we want to remove) before `simp_all` uses them.  Removing
    `h` from context breaks this: the unmodified term we inject is not the rewritten
    form that `simp_all` expected, so it makes no progress.
    Detection: the line contains `rw`, ` at `, and `simp_all`. -/
private def hasRwAtBeforeSimpAll (line : String) : Bool :=
  (line.splitOn "simp_all").length ≥ 2 &&
  (line.splitOn " at ").length ≥ 2 &&
  ((line.splitOn " rw ").length ≥ 2 || line.trimLeft.startsWith "rw " ||
   (line.splitOn "\trw ").length ≥ 2)

/-- Inject `repl` into every `simp_all` and `simp [*]` / `simp [ *]` call in `line`.
    · For `simp_all [l1, l2]`: becomes `simp_all [l1, l2, repl]`.
    · For `simp_all` (no bracket): becomes `simp_all [repl]` (inserted before `;` or EOL).
    · For `simp [*, ...]` / `simp [ *, ...]`: inserts `, repl` before the `]`. -/
private def injectIntoSimpCalls (line repl : String) : String :=
  -- 1. Process every `simp_all` occurrence.
  let after1 : String :=
    let parts := line.splitOn "simp_all"
    if parts.length < 2 then line
    else
      let injectSeg (seg : String) : String :=
        -- `seg` is the text immediately after the `simp_all` keyword.
        if (seg.splitOn "[").length ≥ 2 then
          -- Has a bracket: insert `, repl` before the first `]`.
          let split2 := seg.splitOn "]"
          if split2.length ≥ 2 then
            split2[0]! ++ ", " ++ repl ++ "]" ++ "]".intercalate (split2.drop 1)
          else seg
        else
          -- No bracket: add `[repl]` after options and before the next `;` or EOL.
          let semiParts := seg.splitOn ";"
          if semiParts.length ≥ 2 then
            semiParts[0]!.trimRight ++ " [" ++ repl ++ "]" ++
            ";" ++ ";".intercalate (semiParts.drop 1)
          else
            seg.trimRight ++ " [" ++ repl ++ "]"
      -- Prepend "simp_all" to each injected segment, then fold to concatenate.
      -- (String.intercalate with a single-element list returns that element without
      -- the separator, which would drop the "simp_all" keyword itself.)
      (parts.drop 1).foldl (fun acc seg => acc ++ "simp_all" ++ injectSeg seg) parts[0]!
  -- 2. Inject into `simp [ *]` and `simp [*]` (wildcard-star forms).
  -- Note: `String.intercalate` is called on the *separator* string, not the list.
  let after2 := ("[ *, " ++ repl ++ "]").intercalate (after1.splitOn "[ *]")
  ("[*, " ++ repl ++ "]").intercalate (after2.splitOn "[*]")

/-- If `line` matches `[·] rw [X] at *; simp_all [Y]`, transforms it to
    `[·] simp_all [X, Y]`.
    Rationale: `rw [...] at *` does NOT rewrite `let`-binding types in Lean 4,
    so after converting a `have h` to `let h`, passing `h` explicitly to
    `simp_all` uses the ORIGINAL (pre-rw) type.  By merging the rw lemma into
    `simp_all` we let simp apply it iteratively (to fixpoint), which achieves
    the same simplification without needing `rw` to update `h` in-place. -/
private def absorbRwIntoSimpAll (line : String) : String :=
  let lt     := line.trimLeft
  let indent := String.mk (line.toList.takeWhile Char.isWhitespace)
  let bullet := if lt.startsWith "· " then "· " else ""
  let core   := lt.drop bullet.length
  -- Pattern: `rw [X] at *; rest` where rest contains simp_all
  if !(core.startsWith "rw [" || core.startsWith "rw [ ") then line
  else
    let parts := core.splitOn "] at *; "
    if parts.length < 2 then line
    else
      -- Extract X from "rw [X" (everything after the first `[`)
      let rwLemma :=
        match parts[0]!.splitOn "[" with
        | _ :: xs => ("[".intercalate xs).trim
        | _       => ""
      let rest := "] at *; ".intercalate (parts.drop 1)
      if rwLemma.isEmpty then line
      else
        let merged := injectIntoSimpCalls rest.trimLeft rwLemma
        indent ++ bullet ++ merged

/-- If `line` contains `; have name := term` (no `:= by`) after a `;` at
    outer bracket depth — i.e., a named term-mode `have` appears mid-line —
    return `(before.trimRight, haveAndRest.trimLeft)`.
    Returns `none` if no such split point exists. -/
private def findMidLineHave (line : String) (allowAnon : Bool := false) : Option (String × String) := Id.run do
  let chars := line.toList.toArray
  let mut depth := 0
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then
      if depth > 0 then depth := depth - 1
    else if c == ';' && depth == 0 && i > 0 then
      let rest := (String.mk (chars.extract (i + 1) chars.size).toList).trimLeft
      if rest.startsWith "have " then
        let afterHave := rest.drop "have ".length
        -- Named have (not anonymous `have :=`) and term-mode (no `:= by`).
        -- `allowAnon` (the ITER pipeline's splitter) also takes anonymous
        -- ones — `nameAnonymousHaves` names them on the next scan, and the
        -- scoped `this`-rename keeps their consumers intact (observed
        -- survivor: `intro h; have := norm_char_s s x; rw [...] at this;
        -- exact ... this.symm` in ZkFourier.lean).
        if (allowAnon || (!afterHave.startsWith ":=" && !afterHave.startsWith ":")) &&
           (rest.splitOn ":=").length ≥ 2 && (rest.splitOn ":= by").length < 2 then
          let before := String.mk (chars.extract 0 i).toList
          return some (before.trimRight, rest)
    i := i + 1
  return none

/-- Pre-process body lines before inlining:
    1. `"ind · have h := term"` (named have with a leading `·`) is split into
       `"ind ·"` and `"ind   have h := term"` so `inlineOneLinersStep` can
       see the `have` directly.
    2. `"ind have := term ; rest"` (anonymous have, with or without `·` prefix) is
       transformed to:
       - an `"ind -- auto-named: rename 'h_auto_N'"` comment line
       - `"ind have h_auto_N := term"` (synthetic name)
       - `"ind rest"` if `rest` is non-empty (same-line continuation split at `;`)
       In subsequent lines, `this` is renamed to `h_auto_N` (Lean's implicit name
       for the most recently introduced anonymous `have`) until a sibling `·` bullet
       at a lower-or-equal indent resets the alias.
    3. `"ind · pre; have h := term; rest"` (named term-mode `have` mid-line after `;`)
       is split into `"ind · pre"` and `"ind   have h := term"` (and `"ind   rest"`
       if non-empty) so `inlineOneLinersStep` can see the `have`. -/
private def preprocessBodyLines (lines : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut anonCount : Nat := 0
  let mut thisAlias : Option (String × Nat) := none  -- (alias-name, have-indent)
  for _i in List.range lines.size do
    let rawLine := lines[_i]!
    let rawLt   := rawLine.trimLeft
    let rawIndN := rawLine.length - rawLt.length
    -- Reset alias when we encounter a `·` bullet STRICTLY ABOVE the have's indent level.
    -- Same-indent bullets are sub-goal branches that come AFTER the `have :=` and are
    -- still in scope; only a bullet at a LOWER indent exits the scope entirely.
    match thisAlias with
    | some (_, haveIndN) =>
      if rawLt.startsWith "· " && rawIndN < haveIndN then thisAlias := none
    | none => ()
    -- Apply pending `this` → alias renaming
    let l := match thisAlias with
      | none           => rawLine
      | some (alias, _) => replaceWord rawLine "this" alias
    let lt       := l.trimLeft
    let indentN  := l.length - lt.length
    let indentStr := String.mk (l.toList.takeWhile Char.isWhitespace)
    -- Case 1: `"· have h := term"` (named have with bullet, not anonymous)
    if lt.startsWith "· " &&
       (lt.drop 2).startsWith "have " &&
       !((lt.drop 2 |>.drop "have ".length).startsWith ":=") then
      out := out.push (indentStr ++ "·")
      out := out.push (indentStr ++ "  " ++ lt.drop 2)
    -- Case 2: `"have := term"` or `"· have := term"` (anonymous have)
    else if lt.startsWith "have :=" ||
            (lt.startsWith "· " && (lt.drop 2).startsWith "have :=") then
      let hasBullet := lt.startsWith "· "
      let haveRaw   := if hasBullet then lt.drop 2 else lt
      anonCount := anonCount + 1
      let autoName  := "h_auto_" ++ toString anonCount
      -- Prepend the synthetic name after `have `
      let renamed   := "have " ++ autoName ++ " " ++ haveRaw.drop "have ".length
      let comment   := "-- auto-named: rename '" ++ autoName ++ "'"
      -- The indent where `h_auto_N` lives (used to scope `this` renaming)
      let haveIndN  := if hasBullet then indentN + 2 else indentN
      if hasBullet then
        out := out.push (indentStr ++ "·")
        let inner := indentStr ++ "  "
        out := out.push (inner ++ comment)
        match splitAtOuterSemi renamed with
        | none => out := out.push (inner ++ renamed)
        | some (hp, rp) =>
          out := out.push (inner ++ hp)
          if !rp.isEmpty then out := out.push (inner ++ rp)
      else
        out := out.push (indentStr ++ comment)
        match splitAtOuterSemi renamed with
        | none => out := out.push (indentStr ++ renamed)
        | some (hp, rp) =>
          out := out.push (indentStr ++ hp)
          if !rp.isEmpty then out := out.push (indentStr ++ rp)
      thisAlias := some (autoName, haveIndN)
    -- Case 3: named term-mode `have` appearing mid-line after `;`
    -- e.g. `"· funext j; have hj := term; rest"` → separate lines
    else
      match findMidLineHave l with
      | some (before, haveAndRest) =>
        out := out.push before
        -- If the prefix contains a bullet `· `, the `have` goes one level deeper
        let hasBulletInBefore := before.trimLeft.startsWith "· "
        let innerIndent := if hasBulletInBefore then indentStr ++ "  " else indentStr
        match splitAtOuterSemi haveAndRest with
        | some (hp, rp) =>
          out := out.push (innerIndent ++ hp)
          if !rp.isEmpty then out := out.push (innerIndent ++ rp)
        | none =>
          out := out.push (innerIndent ++ haveAndRest)
      | none =>
        out := out.push l
  out

/-- Find and inline ONE `have h := term` (no `:= by`) one-liner.
    Strategy:
    · Compute the scope of `h`: lines in `restArr` up to (but not including)
      the first line where indent < have-indent AND trimmed starts with `·`.
      This prevents injecting the term into sibling proof branches where `h`
      is out of scope.
    · Case A – explicit uses exist and all are inlineable:
        Replace each explicit use with `(term)` and inject `(term)` into every
        `simp_all` / `simp [*]` line in scope (those calls relied on `h` being
        a local hypothesis).  Then remove the `have h` line.
    · Case C – fallback: convert `have h` → `let h` and inject `h` by name into
        every simp_all / simp[*] in scope.  The `let` stays in local context so
        subsequent `simp [*]` calls can still use it via `*` expansion.
    Returns the updated array on success, `none` if nothing changed. -/
private def inlineOneLinersStep (lines : Array String) (anonTypes : Array String := #[]) : Option (Array String) := Id.run do
  for i in List.range lines.size do
    let l  := lines[i]!
    let lt := l.trimLeft
    -- Match `have h ...` where the proof is a term (no `:= by`)
    if lt.startsWith "have " &&
       (lt.splitOn ":=").length ≥ 2 &&
       (lt.splitOn ":= by").length < 2 then
      -- Extract the have name (everything before the first space / `:` / `=`)
      let afterHave := lt.drop "have ".length
      let nameStop  := afterHave.find (fun c => c == ' ' || c == ':' || c == '=')
      let hName     := String.Pos.Raw.extract afterHave ⟨0⟩ nameStop
      -- Extract the term (everything after the first `:=`)
      let termPart :=
        match lt.splitOn ":=" with
        | _ :: rest => (":=".intercalate rest).trim
        | _         => ""
      if !hName.isEmpty && !termPart.isEmpty then
        let restArr := lines.extract (i + 1) lines.size
        -- ── Scope: stop at the first out-of-scope branch boundary ────────────
        -- A `·` bullet whose indent is strictly less than `have_indent` starts
        -- a sibling proof branch where `h` is no longer in the local context.
        let have_indent := lineIndent l
        let scopeEnd := (List.range restArr.size).find? fun j =>
          let rl := restArr[j]!
          let rt := rl.trimLeft
          lineIndent rl < have_indent &&
          (rt.startsWith "· " || rt == "·" || rt.startsWith "·\n")
        let inScopeSize := match scopeEnd with | none => restArr.size | some k => k
        let inScopeArr  := restArr.extract 0 inScopeSize
        -- ── Collect uses ─────────────────────────────────────────────────────
        -- Exclude lines that RE-BIND the same name (`have hName`/`let hName`):
        -- those are sequential same-name shadowing declarations, not uses.
        -- Treating them as uses in Case A would replace the binding's name with the
        -- call expression, producing the invalid pattern `have (call) : T := ...`.
        let useIdxs := (List.range inScopeArr.size).filter fun j =>
          let l  := inScopeArr[j]!
          let lt := l.trimLeft
          containsWord l hName &&
          !(lt.startsWith ("have " ++ hName) || lt.startsWith ("let " ++ hName))
        let repl :=
          if termPart.startsWith "(" && termPart.endsWith ")" then termPart
          else "(" ++ termPart ++ ")"
        -- Whether any in-scope simp_all is preceded on the same line by `rw [...] at`.
        -- This is only relevant for Case A (explicit use) where we inject at the site
        -- AND into simp_all; for Case C the have becomes a `let` in context (no issue).
        let riskySimpAllAfterRw := inScopeArr.any (fun l =>
          usesSimpAllOrStar l && hasRwAtBeforeSimpAll l)
        -- ── Type-aware preserve check ────────────────────────────────────────────
        -- `simp_all +decide` uses ALL local `have` hypotheses for forward reasoning.
        -- For *non-equation* Prop types this is critical: simp can't use a raw Prop
        -- as a rewrite rule, so the have MUST stay in the local context.
        -- Exception: if the have's type is an equation (`=` or `↔`), simp_all CAN
        -- use the injected lemma name via `let h := call` as a simp lemma.
        -- Extract the type annotation T from `have h : T := call`.
        let typeAnnotation : String :=
          match lt.splitOn " := " with
          | namePlusType :: _ =>
            match namePlusType.splitOn " : " with
            | _ :: typeParts => " : ".intercalate typeParts
            | _ => ""
          | _ => ""
        -- Fallback: for `h_auto_N` names with no source-level `: T` annotation,
        -- look up the MetaM-derived type from `anonTypes` (provided by `walkFull`).
        -- This enables equation detection for anonymous haves (`have := term`)
        -- that were renamed to `h_auto_N` by `preprocessBodyLines`.
        let metaTypeAnnotation : String :=
          if !typeAnnotation.isEmpty then ""
          else if hName.startsWith "h_auto_" then
            let nStr := hName.drop "h_auto_".length
            match nStr.toNat? with
            | some n =>
              if n ≥ 1 && n - 1 < anonTypes.size then anonTypes[n - 1]!
              else ""
            | none => ""
          else ""
        let effectiveTypeAnnotation :=
          if !typeAnnotation.isEmpty then typeAnnotation else metaTypeAnnotation
        -- An equation type: contains ` = ` (but not as part of `:=`) or `↔`.
        -- The source type string is extracted BEFORE ` := `, so it never contains `:=`.
        -- The meta type string (from ppExpr) may contain newlines — splitOn still works.
        let isEqType : Bool :=
          let ta := effectiveTypeAnnotation
          !ta.isEmpty &&
          ((ta.splitOn " = ").length ≥ 2 ||
           (ta.splitOn "↔").length ≥ 2)
        -- `specialize h` / `rcases h` require `h` to be a `have` hypothesis.
        -- `let` bindings don't work with these tactics.
        -- Search the full line (not just the start): `specialize` can appear mid-line
        -- after a semicolon, e.g. `intro x y; specialize h_foo arg1 arg2`.
        let hasSpecializeUse := inScopeArr.any fun sl =>
          (sl.splitOn ("specialize " ++ hName)).length ≥ 2 ||
          (sl.splitOn ("rcases " ++ hName)).length ≥ 2
        -- Guard against zeta-reduction: `simp_all` zeta-reduces `let` bindings, so
        -- if `simp_all +decide` appears BEFORE a non-inlineable `at h` use (e.g.
        -- `unfold X at h` or `norm_num at h` in a sub-branch), converting to `let`
        -- would cause the binding to vanish before the `at h` tactic runs.
        -- Detect by finding the earliest `simp_all +decide` and earliest `at hName`
        -- index; if simp_all comes first, preserve as `have`.
        let simpAllPlusDecideIdx := (List.range inScopeSize).find? fun j =>
          hasSimpAllPlusDecide inScopeArr[j]!
        let firstAtUseIdx := (List.range inScopeSize).find? fun j =>
          isNonInlineableUse inScopeArr[j]! hName
        let simpAllBeforeAtUse := match simpAllPlusDecideIdx, firstAtUseIdx with
          | some si, some ai => si < ai
          | _, _ => false
        -- Whether the equation type was derived from MetaM (no source-level `: T`).
        -- Used in both the preserve check and the Case A guard below.
        let typeFromMeta := typeAnnotation.isEmpty && !metaTypeAnnotation.isEmpty
        -- All non-inlineable `at h` use indices.
        let atUseIndices : List Nat := (List.range inScopeSize).filter fun j =>
          isNonInlineableUse inScopeArr[j]! hName
        -- Whether a line in inScopeArr is inside a `·` bullet branch.
        -- True if the line ITSELF starts with `·`, or a preceding line is a `·` at lower indent.
        let isInBulletBranch (j : Nat) : Bool :=
          let jl := inScopeArr[j]!
          let jt := jl.trimLeft
          jt.startsWith "· " || jt == "·" ||
          (let jIndent := lineIndent jl
           (List.range j).any fun k =>
             let kl := inScopeArr[k]!
             let kt := kl.trimLeft
             lineIndent kl < jIndent &&
             (kt.startsWith "· " || kt == "·"))
        -- Case D applies when simp_all precedes at-uses BUT all at-uses are in bullet
        -- branches.  In each bullet, the context is a fresh goal state after the
        -- `cases <;> simp_all` dispatch — we can reintroduce `have h := (repl)` at
        -- the start of the bullet so that `unfold X at h` / `norm_num at h` work.
        let atUsesAllInBullets : Bool :=
          !atUseIndices.isEmpty && atUseIndices.all isInBulletBranch
        -- Detect naming conflicts for Case D: `cases NAME : expr` in scope rebinds NAME.
        -- If `repl` (the private lemma call) uses that NAME as an argument, prepending
        -- `have h := repl` inside the bullet would use the INNER (case-split) NAME
        -- rather than the outer theorem parameter, causing type errors.
        -- Collect names bound by `cases NAME :` patterns in the scope lines.
        -- Uses `splitOn " :"` to detect `NAME :` (requires space before colon).
        let casesBoundNames : List String :=
          (List.range inScopeSize).foldl (fun acc j =>
            let l := inScopeArr[j]!
            let parts := l.splitOn "cases "
            let found := parts.tail.filterMap fun part =>
              let trimmed := part.trimLeft
              -- Only match `NAME :` form (space before colon); `cases h` (no `:`) is different
              match trimmed.splitOn " :" with
              | name :: _ :: _ =>
                let n := name.trim
                if !n.isEmpty && n.all isIdentChar then some n else none
              | _ => none
            acc ++ found
          ) []
        let replHasConflict := casesBoundNames.any (containsWord repl)
        -- Preserve if: specialize/rcases uses exist (need `have` hypothesis semantics)
        -- OR simp_all +decide is in scope but the type is NOT an equation.
        -- OR simp_all +decide precedes a non-inlineable `at h` use (zeta-reduction risk)
        --    AND the at-uses are NOT all inside bullet branches (Case D handles that case).
        -- OR Case D would apply (all at-uses in bullets) BUT repl uses a name rebound
        --    by `cases NAME :` — injecting repl inside bullets would shadow the outer var.
        -- OR the equation type came from MetaM AND simp_all +decide is in scope AND
        --    there are no prior `at h` uses: simp_all uses the hypothesis for
        --    *hypothesis-type simplification* (e.g. unfolding `gowers_product` via
        --    `gowers_product_succ` then using the result to close the goal).  Both
        --    Case A (term injection) and Case C (let conversion) fail here because
        --    simp_all can only do hypothesis-type simplification on `have` hypotheses,
        --    not on bare injected terms or `let` bindings.
        if hasSpecializeUse ||
           (inScopeArr.any hasSimpAllPlusDecide && !isEqType) ||
           (inScopeArr.any hasSimpAllPlusDecide && simpAllBeforeAtUse && !atUsesAllInBullets) ||
           (inScopeArr.any hasSimpAllPlusDecide && simpAllBeforeAtUse && atUsesAllInBullets && replHasConflict) ||
           (typeFromMeta && isEqType && simpAllPlusDecideIdx.isSome && firstAtUseIdx.isNone) then
          continue
        -- ── Sharing guard (anti-blowup) ──────────────────────────────────────
        -- Case A/D substitute `repl` TEXTUALLY into every use site. When
        -- extracted-call one-liners CHAIN — each capturing the previous haves
        -- as call arguments, 15-deep in `Hedge.lean`'s regret theorems —
        -- greedy inlining expands the call DAG into a TREE: observed a single
        -- 271,265-char output line with `aux_hN_pos` duplicated 2,785×. Cap
        -- the total text one inline step may add (each accepted step then adds
        -- ≤ budget chars, so total growth stays LINEAR in the have count); an
        -- oversized have keeps its binder, and the verified ladder later
        -- converts it to `let`, which PRESERVES sharing instead of copying.
        let inlineBudget := 400
        let injectSiteCount := (List.range inScopeSize).countP (fun j =>
          !useIdxs.any (· == j) && usesSimpAllOrStar inScopeArr[j]!)
        -- Count OCCURRENCES, not use-lines: `replaceWord` replaces every
        -- occurrence on a line, and a previously-inlined call text sitting on
        -- one line can carry dozens of them.
        let occCount := useIdxs.foldl (fun acc j =>
          acc + ((inScopeArr[j]!.splitOn hName).length - 1)) 0
        let oversized := (occCount + injectSiteCount) * repl.length > inlineBudget
        if oversized then
          continue
        -- ── Case D: at-uses all in bullet branches ─────────────────────────────
        -- `simpAllBeforeAtUse` fired but all non-inlineable `at h` uses are inside
        -- `·` bullet branches.  Each bullet is a fresh goal state: we can prepend
        -- `have h := (repl)` at the start of each bullet so the `unfold X at h` /
        -- `norm_num at h` tactics see a named hypothesis.
        -- Also inject `(repl)` into the dispatch `simp_all` so branches that relied
        -- on `h` being in context can still be closed.
        if simpAllBeforeAtUse && atUsesAllInBullets then
          -- Find the bullet line (in inScopeArr coords) that CONTAINS a given at-use.
          let findContainingBullet (j : Nat) : Nat :=
            let jl := inScopeArr[j]!
            let jt := jl.trimLeft
            if jt.startsWith "· " || jt == "·" then j  -- line IS the bullet
            else
              let jIndent := lineIndent jl
              ((List.range j).reverse.find? fun k =>
                let kl := inScopeArr[k]!
                let kt := kl.trimLeft
                lineIndent kl < jIndent &&
                (kt.startsWith "· " || kt == "·")
              ).getD j
          let bulletIndices := atUseIndices.map findContainingBullet
          let uniqueBullets : List Nat :=
            bulletIndices.foldl (fun acc b =>
              if acc.any (· == b) then acc else acc ++ [b]) []
          let mut newLines := lines
          -- 1. Inject (repl) into all simp_all calls in scope (dispatch + bullets).
          for j in List.range inScopeSize do
            let idx := i + 1 + j
            if usesSimpAllOrStar newLines[idx]! then
              newLines := newLines.set! idx (injectIntoSimpCalls newLines[idx]! repl)
          -- 2. Prepend `have hName := (repl); ` to the start of each bullet's content.
          for bk in uniqueBullets do
            let absIdx := i + 1 + bk
            let bulletLine := newLines[absIdx]!
            let bulletTrimmed := bulletLine.trimLeft
            let indentStr := String.mk (List.replicate (lineIndent bulletLine) ' ')
            let newLine :=
              if bulletTrimmed.startsWith "· " then
                indentStr ++ "· have " ++ hName ++ " := " ++ repl ++ "; " ++
                bulletTrimmed.drop 2
              else bulletLine
            newLines := newLines.set! absIdx newLine
          -- 3. Remove the original `have h` line.
          newLines := newLines.extract 0 i ++ newLines.extract (i + 1) newLines.size
          if i > 0 && newLines[i - 1]!.trimLeft.startsWith "-- auto-named:" then
            newLines := newLines.extract 0 (i - 1) ++ newLines.extract i newLines.size
          return some newLines
        -- ── Case A: explicit uses, all inlineable ─────────────────────────────
        -- Guard: when the equation type was detected via MetaM type info (not a
        -- source-level `: T` annotation) AND `simp_all +decide` is in scope,
        -- skip Case A and fall through to Case C (kept as defense-in-depth;
        -- the preserve check above should already prevent reaching this point).

        if !useIdxs.isEmpty &&
           useIdxs.all (fun j => !isNonInlineableUse inScopeArr[j]! hName) &&
           !riskySimpAllAfterRw &&
           !(typeFromMeta && inScopeArr.any hasSimpAllPlusDecide) then
          let mut newLines := lines
          for j in useIdxs do
            let idx := i + 1 + j
            newLines := newLines.set! idx (replaceWord newLines[idx]! hName repl)
          -- Inject repl into simp_all/simp[*] lines in scope (skip lines already
          -- handled by replaceWord above, to avoid double-injection)
          for j in List.range inScopeSize do
            if !useIdxs.any (· == j) && usesSimpAllOrStar newLines[i + 1 + j]! then
              let idx := i + 1 + j
              newLines := newLines.set! idx (injectIntoSimpCalls newLines[idx]! repl)
          -- Remove the `have h` line; also clean up any preceding auto-named comment
          newLines := newLines.extract 0 i ++ newLines.extract (i + 1) newLines.size
          if i > 0 && newLines[i - 1]!.trimLeft.startsWith "-- auto-named:" then
            newLines := newLines.extract 0 (i - 1) ++ newLines.extract i newLines.size
          return some newLines
        -- ── Case C: convert to `let` and inject name into simp_all/simp[*] ─────
        -- Case B (term injection + have removal) was removed: it lost the hypothesis
        -- from the local context, so subsequent `simp [*]` calls could not use it.
        -- Case C keeps `let h := call` in scope for `*` expansion AND injects the
        -- name into simp_all so it is used both as a local hypothesis and explicitly.
        else
          let mut newLines := lines
          -- 1. Convert `have h …` → `let h …`
          let istr := String.mk (newLines[i]!.toList.takeWhile Char.isWhitespace)
          let hlt  := newLines[i]!.trimLeft
          newLines := newLines.set! i (istr ++ "let" ++ hlt.drop "have".length)
          -- 2. Inject `h` (by name) into every simp_all / simp[*] in scope.
          --    Also absorb any preceding `rw [X] at *;` into simp_all: since
          --    `rw at *` does NOT rewrite let-binding types in Lean 4, we merge
          --    X into simp_all so the lemma is applied via simp's fixpoint loop.
          for j in List.range inScopeSize do
            let idx := i + 1 + j
            let ln := newLines[idx]!
            if usesSimpAllOrStar ln then
              -- Inject `hName` into simp_all even if `hName` appears elsewhere on the
              -- same line (e.g. in `unfold X at hName; simp_all [Y]`).  The old guard
              -- `!containsWord ln hName` prevented injection when `hName` appeared in
              -- `at hName` position, which left simp_all without the let-binding name
              -- and caused "simp_all made no progress" (Root Cause 3).
              let injected := injectIntoSimpCalls ln hName
              newLines := newLines.set! idx (absorbRwIntoSimpAll injected)
          -- 3. Fix `norm_num at h` → `(simp only [*] at h; norm_num at h)`.
          --    `simp only [*]` applies all current local hypotheses (e.g. case-split
          --    equations) to reduce `h`'s type to a numeric equation so that
          --    `norm_num` can then evaluate and derive the contradiction.
          for j in List.range inScopeSize do
            let idx := i + 1 + j
            if (newLines[idx]!.splitOn ("norm_num at " ++ hName)).length ≥ 2 then
              newLines := newLines.set! idx
                (newLines[idx]!.replace ("norm_num at " ++ hName)
                  ("(simp only [*] at " ++ hName ++ "; norm_num at " ++ hName ++ ")"))
          return some newLines
  return none

/-- Repeatedly inline `have h := term` one-liners to fixpoint.
    Runs `preprocessBodyLines` first to handle anonymous and bullet-prefixed haves.
    `anonTypes` provides MetaM-derived types for `h_auto_N` anonymous haves; the
    Nth entry (1-based) corresponds to the Nth anonymous have in encounter order,
    matching the numbering assigned by `preprocessBodyLines`. -/
private def inlineOneLiners (lines : Array String) (anonTypes : Array String := #[]) : Array String := Id.run do
  let mut ls := preprocessBodyLines lines
  let mut go := true
  while go do
    match inlineOneLinersStep ls anonTypes with
    | none    => go := false
    | some ls' => ls := ls'
  ls

/-- Case D v2 for auto-named anonymous haves.
    Finds `-- auto-named: rename 'h_auto_N'` / `have h_auto_N := term` pairs and
    handles them using the MetaM-computed inlined proof term when simp_all context-
    dependence prevents normal inlining:
    · Case E: no `at h_auto_N` uses — `simp_all` uses `h` only for hypothesis-type
      simplification.  Emit `exact <inlinedTerm>` to close the goal without `have`.
    · Case F: `at h_auto_N` uses exist but NOT all in bullet branches — the `at`
      tactics are part of the main proof flow.  Same fix: `exact <inlinedTerm>`.
    · Case D v2: all at-uses in bullet branches AND `term` uses a name rebound by
      `cases NAME :` (naming conflict).  Rename `have` → `h_auto_N_saved` and
      prepend `have h_auto_N := h_auto_N_saved; ` at the start of each affected bullet.
    `anonInlinedTerms` is aligned with `walkAnonTypes` output (index N-1 = h_auto_N). -/
private def processAutoNamedHaves (lines : Array String) (anonInlinedTerms : Array String := #[])
    (localParams : List String := []) : Array String := Id.run do
  let mut out := lines
  let mut i := 0
  while i < out.size do
    let l  := out[i]!
    let lt := l.trimLeft
    -- Only process `-- auto-named: rename 'h_auto_N'` comment lines
    if !lt.startsWith "-- auto-named: rename '" then
      i := i + 1
      continue
    -- Extract autoName from the single-quoted name in the comment
    let nameParts := lt.splitOn "'"
    let autoName := if nameParts.length >= 2 then nameParts[1]! else ""
    if autoName.isEmpty || i + 1 >= out.size then
      i := i + 1
      continue
    -- Next line must be `have autoName := term` (no `:= by`)
    let nl := out[i + 1]!
    let nlt := nl.trimLeft
    let havePrefix := "have " ++ autoName ++ " := "
    if !nlt.startsWith havePrefix || (nlt.splitOn ":= by").length >= 2 then
      i := i + 1
      continue
    let haveIndent := lineIndent nl
    let term := nlt.drop havePrefix.length |>.trimRight
    -- Compute scope: lines after the have, until first bullet at lower indent OR
    -- a top-level declaration (indent 0) which marks the end of the current lemma body.
    let baseIdx := i + 2
    let restSize := out.size - baseIdx
    let isTopLevelDecl (rt : String) : Bool :=
      ["lemma ", "private lemma ", "private def ", "def ", "theorem ", "private theorem ",
       "section ", "end ", "open ", "variable ", "instance ", "class ", "structure "].any rt.startsWith
    let inScopeSize :=
      match (List.range restSize).find? fun j =>
        let rl := out[baseIdx + j]!
        let rt := rl.trimLeft
        (lineIndent rl < haveIndent &&
         (rt.startsWith "· " || rt == "·" || rt.startsWith "·\n")) ||
        (lineIndent rl == 0 && isTopLevelDecl rt)
      with
      | some k => k
      | none   => restSize
    let inScopeArr := (List.range inScopeSize).map fun j => out[baseIdx + j]!
    -- Require simp_all +decide in scope (without it, convertHavesToLet already handles)
    if !inScopeArr.any hasSimpAllPlusDecide then
      i := i + 1
      continue
    -- Extract N from "h_auto_N" to index into anonInlinedTerms.
    -- Also strip trailing "_saved" suffix (from Case D v2 renames) when indexing.
    let rawName := if autoName.endsWith "_saved" then autoName.dropRight "_saved".length else autoName
    let autoN := (rawName.drop "h_auto_".length).toNat?.getD 0
    let indentStr := String.mk (List.replicate haveIndent ' ')
    let scopeEnd := baseIdx + inScopeSize
    -- Helper: replace [i..scopeEnd) with `exact <inlinedTerm>`.
    -- ppExpr uses 0-based absolute indentation.  `exact` is at `haveIndent` spaces;
    -- continuation lines must be indented MORE than `haveIndent` for Lean's tactic
    -- parser to treat them as part of the term (not as new tactics).  We prefix every
    -- embedded newline with `haveIndent + 2` spaces to shift the whole term right.
    let tryInlinedExact : Option (Array String) :=
      if autoN > 0 && autoN ≤ anonInlinedTerms.size then
        let inlinedTerm := anonInlinedTerms[autoN - 1]!
        if !inlinedTerm.isEmpty && !(inlinedTerm.contains '⋯') && inlinedTerm.length < 100000 then
          let contIndent := String.mk (List.replicate (haveIndent + 2) ' ')
          let reindented := inlinedTerm.replace "\n" ("\n" ++ contIndent)
          some (out.extract 0 i ++ #[indentStr ++ "exact " ++ reindented] ++
                out.extract scopeEnd out.size)
        else none
      else none
    -- Find all non-inlineable `at autoName` uses
    let atUseIndices := (List.range inScopeSize).filter fun j =>
      isNonInlineableUse inScopeArr[j]! autoName
    -- ── Case E: no at-uses — simp_all uses h only for hyp-type simplification ──
    if atUseIndices.isEmpty then
      match tryInlinedExact with
      | some newLines => out := newLines; i := i + 1; continue
      | none          =>
        -- tryInlinedExact failed (inlined term > 100K chars or contains ⋯).
        -- Two strategies to eliminate the `have` without a huge inlined term:
        --
        -- Strategy 1 (`specialize`): if term's leading identifier is a LOCAL HYPOTHESIS
        --   (parameter of the enclosing lemma, or introduced by `intro`), emit
        --   `specialize IDENT ARGS` and rename autoName → IDENT in all scope lines.
        --   simp_all then treats the specialized hypothesis exactly as it would a `have`.
        --
        -- Strategy 2 (simp-list): if the leading ident is a global lemma, add the term
        --   value directly to the nearest simp_all's lemma list.  Only applied when
        --   autoName is NOT referenced in any scope line after the simp_all (i.e., the
        --   simp_all fully closes the goal so there are no later name uses).
        --
        -- Fall through (keep `have`) if neither strategy applies.
        let leadingIdent : String := String.mk (term.toList.takeWhile isIdentChar)
        -- Detect if leadingIdent is a param or intro'd name of the enclosing lemma.
        -- localParams (passed by the private-lemma call site) contains signature params;
        -- for the outer theorem body, we fall back to backward-scanning for `lemma`.
        let isLocalHyp : Bool :=
          if leadingIdent.isEmpty then false
          else if localParams.contains leadingIdent then true
          else
            match (List.range i).reverse.find? fun k =>
                let lt := (out[k]!).trimLeft
                lt.startsWith "private lemma " || lt.startsWith "lemma " with
            | none => false
            | some start =>
              -- Check the lemma signature line for `(ident :`, `{ident :`, `[ident :`
              let sig := out[start]!
              let inSig := ["(" ++ leadingIdent ++ " :", "{" ++ leadingIdent ++ " :",
                            "[" ++ leadingIdent ++ " :"].any fun p => (sig.splitOn p).length >= 2
              -- Also check for `intro ... ident ...` lines between lemma start and here
              let inIntro := (List.range (i - start)).any fun j =>
                let sl := out[start + j]!.trimLeft
                sl.startsWith "intro " && containsWord sl leadingIdent
              inSig || inIntro
        -- Guard: `specialize` requires the term to start with `IDENT ` (space after ident),
        -- not `IDENT.field` (dot projection). Dot access means the hypothesis is being
        -- destructured — `specialize hfar.2.2 args` would be invalid.
        let termAfterIdent := term.drop leadingIdent.length
        let canSpecialize := isLocalHyp && (termAfterIdent.startsWith " " || termAfterIdent.isEmpty)
        if canSpecialize then
          -- Strategy 1: emit `specialize term` (term starts with leadingIdent),
          -- rename autoName → leadingIdent in all in-scope lines.
          let specializeLine := indentStr ++ "specialize " ++ term
          let newScopeLines := (List.range inScopeSize).map fun j =>
            replaceWord (out[baseIdx + j]!) autoName leadingIdent
          out := out.extract 0 i ++ #[specializeLine] ++
                 newScopeLines.toArray ++
                 out.extract scopeEnd out.size
          i := i + 1
          continue
        else
          -- Global lemma terms can't be used as simp rewrite rules (they're Props, not equations).
          -- simp_all needs them as hypotheses (via have), not in the simp lemma list.
          -- Fall through to keep the original `have h_auto_N := term`.
          i := i + 1; continue
    -- Check all at-uses are inside `·` bullet branches
    let isInBulletBranch (j : Nat) : Bool :=
      let jl := inScopeArr[j]!
      let jt := jl.trimLeft
      jt.startsWith "· " || jt == "·" ||
      (let jIndent := lineIndent jl
       (List.range j).any fun k =>
         let kl := inScopeArr[k]!
         let kt := kl.trimLeft
         lineIndent kl < jIndent && (kt.startsWith "· " || kt == "·"))
    -- ── Case F: at-uses not all in bullets — emit exact <inlinedTerm> ─────────
    if !atUseIndices.all isInBulletBranch then
      match tryInlinedExact with
      | some newLines => out := newLines; i := i + 1; continue
      | none          => i := i + 1; continue
    -- Check naming conflict: `cases NAME :` in scope rebinds a name used in `term`
    let casesBoundNames : List String :=
      (List.range inScopeSize).foldl (fun acc j =>
        let line := inScopeArr[j]!
        let parts := line.splitOn "cases "
        let found := parts.tail.filterMap fun part =>
          let trimmed := part.trimLeft
          match trimmed.splitOn " :" with
          | name :: _ :: _ =>
            let n := name.trim
            if !n.isEmpty && n.all isIdentChar then some n else none
          | _ => none
        acc ++ found
      ) []
    if !casesBoundNames.any (containsWord term) then
      i := i + 1
      continue
    -- ── Case D v2: rename have, prepend in bullets ────────────────────────────
    -- First: try exact <inlinedTerm> to eliminate the have entirely (avoids rename artifact).
    match tryInlinedExact with
    | some newLines => out := newLines; i := i + 1; continue
    | none          => ()
    -- Fallback: rename h_auto_N → h_auto_N_saved and prepend in each bullet.
    let savedName := autoName ++ "_saved"
    -- 1. Rename `have autoName := term` → `have autoName_saved := term`
    out := out.set! (i + 1) (indentStr ++ "have " ++ savedName ++ " := " ++ term)
    -- 2. Update the comment to reflect the new name (no trailing \n — lines here have none)
    let commentIndent := String.mk (List.replicate (lineIndent l) ' ')
    out := out.set! i (commentIndent ++ "-- auto-named: rename '" ++ savedName ++ "'")
    -- 3. Find containing bullet for each at-use
    let findContainingBullet (j : Nat) : Nat :=
      let jl := inScopeArr[j]!
      let jt := jl.trimLeft
      if jt.startsWith "· " || jt == "·" then j
      else
        let jIndent := lineIndent jl
        ((List.range j).reverse.find? fun k =>
          let kl := inScopeArr[k]!
          let kt := kl.trimLeft
          lineIndent kl < jIndent && (kt.startsWith "· " || kt == "·")
        ).getD j
    let bulletIndices := atUseIndices.map findContainingBullet
    let uniqueBullets : List Nat :=
      bulletIndices.foldl (fun acc b =>
        if acc.any (· == b) then acc else acc ++ [b]) []
    -- 4. Prepend `have autoName := savedName; ` to each bullet's first line
    for bk in uniqueBullets do
      let absIdx := baseIdx + bk
      let bulletLine := out[absIdx]!
      let bulletTrimmed := bulletLine.trimLeft
      let bindentStr := String.mk (List.replicate (lineIndent bulletLine) ' ')
      if bulletTrimmed.startsWith "· " then
        out := out.set! absIdx
          (bindentStr ++ "· have " ++ autoName ++ " := " ++ savedName ++ "; " ++
           bulletTrimmed.drop 2)
    i := i + 1
  out

/-- Post-process: for each remaining `have hName := call` line (NOT `:= by`), look up
    hName in namedInlinedTerms and emit `exact <inlinedTerm>` replacing the have and
    everything in its scope (the continuation that the inlined term encodes).
    Scope = from the have line to the first non-blank line at STRICTLY LOWER indent.
    Used to eliminate named `have` one-liners that can't be converted to `let` (due to
    `specialize`, `at`-mutations, or `simp_all +decide` with non-equation type). -/
private def eliminateNamedHavesWithInlinedTerms
    (lines            : Array String)
    (namedInlinedTerms : Array (String × String)) : Array String := Id.run do
  if namedInlinedTerms.isEmpty then return lines
  let mut out := lines
  let mut i   := 0
  while i < out.size do
    let l  := out[i]!
    let lt := l.trimLeft
    if lt.startsWith "have " &&
       (lt.splitOn ":=").length ≥ 2 &&
       (lt.splitOn ":= by").length < 2 then
      let afterHave := lt.drop "have ".length
      let nameStop  := afterHave.find (fun c => c == ' ' || c == ':' || c == '=')
      let hName     := String.Pos.Raw.extract afterHave ⟨0⟩ nameStop
      if !hName.isEmpty then
        match namedInlinedTerms.find? fun p => p.1 == hName with
        | some (_, inlinedTerm) =>
          -- Skip inlined terms that are too large to elaborate in reasonable time.
          -- A term > 100000 chars typically means a `specialize`-use have whose MetaM
          -- value is a large proof inlined at many sites; keep the `have` as-is.
          if !inlinedTerm.isEmpty && !(inlinedTerm.contains '⋯') && inlinedTerm.length < 100000 then
            let haveIndent := lineIndent l
            let indentStr  := String.mk (List.replicate haveIndent ' ')
            let contIndent := String.mk (List.replicate (haveIndent + 2) ' ')
            let reindented := inlinedTerm.replace "\n" ("\n" ++ contIndent)
            -- Scope: from (i+1) to first non-blank line at indent < haveIndent.
            let scopeEnd :=
              if haveIndent == 0 then out.size
              else blockEnd out (i + 1) (haveIndent - 1)
            out := out.extract 0 i ++
                   #[indentStr ++ "exact " ++ reindented] ++
                   out.extract scopeEnd out.size
            i := i + 1
            continue
        | none => ()
    i := i + 1
  out

/-- Convert remaining `have h := expr` one-liner bindings to `let h := expr`.
    The `let` form keeps `h` in the local tactic context (so tactics like
    `rw [...] at h`, `norm_num at h`, and `simp_all` can still use the
    rewritten form of `h`) while eliminating the `have` keyword.
    Exceptions (binding left as `have`):
    - `simp_all +decide` in scope: non-equation Props need forward-reasoning semantics.
    - `specialize h` / `rcases h` in scope: these tactics need `h` as a hypothesis. -/
private def convertHavesToLet (lines : Array String) : Array String := Id.run do
  let mut out := lines
  for i in List.range out.size do
    let l  := out[i]!
    let lt := l.trimLeft
    if lt.startsWith "have " &&
       (lt.splitOn ":=").length ≥ 2 &&
       (lt.splitOn ":= by").length < 2 then
      -- Extract have name for specialize-use check
      let afterHave := lt.drop "have ".length
      let nameStop  := afterHave.find (fun c => c == ' ' || c == ':' || c == '=')
      let hName     := String.Pos.Raw.extract afterHave ⟨0⟩ nameStop
      -- Compute scope: lines after this have up to first bullet at lower indent
      let have_indent := lineIndent l
      let restSize := out.size - i - 1
      let scopeEnd := (List.range restSize).find? fun j =>
        let rl := out[i + 1 + j]!
        let rt := rl.trimLeft
        lineIndent rl < have_indent &&
        (rt.startsWith "· " || rt == "·" || rt.startsWith "·\n")
      let inScopeSize := match scopeEnd with | none => restSize | some k => k
      -- Preserve if simp_all +decide is in scope (non-equation forward reasoning)
      -- or if specialize/rcases uses exist (those tactics need a `have` hypothesis)
      let hasPlusDecide := (List.range inScopeSize).any fun j =>
        hasSimpAllPlusDecide (out[i + 1 + j]!)
      let hasSpecializeUse := !hName.isEmpty && (List.range inScopeSize).any fun j =>
        let sl := out[i + 1 + j]!
        (sl.splitOn ("specialize " ++ hName)).length ≥ 2 ||
        (sl.splitOn ("rcases " ++ hName)).length ≥ 2
      if hasPlusDecide || hasSpecializeUse then
        continue
      let indentStr := String.mk (l.toList.takeWhile Char.isWhitespace)
      out := out.set! i (indentStr ++ "let" ++ lt.drop "have".length)
  out

-- ── Build the output ──────────────────────────────────────────────────────

/-- Collect the contents of every top-level `(…)` group in `s`, ignoring
    nested parentheses.  Used to extract explicit arg names without being
    confused by `∀ (x : T)` appearing inside a parameter's type. -/
private def topLevelParenGroups (s : String) : List String :=
  let step : Nat × String × List String → Char → Nat × String × List String
    | (depth, cur, acc), c =>
      if c == '(' then
        if depth == 0 then (1, "", acc) else (depth + 1, cur.push '(', acc)
      else if c == ')' then
        if depth == 1 then (0, "", acc ++ [cur])
        else if depth > 1 then (depth - 1, cur.push ')', acc)
        else (0, cur, acc)
      else
        if depth > 0 then (depth, cur.push c, acc) else (depth, cur, acc)
  let (_, _, acc) := s.foldl step (0, "", [])
  acc

/-- Generate the refactored source lines for one theorem.
    Returns (preamble, newThmLines).
    `preamble` is a list of `private lemma` declarations to insert before the theorem.
    `newThmLines` is a modified copy of the theorem lines with have blocks replaced by
    ONE-LINER calls (`have h : T := call`). -/
private def buildRefactored
    (lines                   : Array String)
    (span                    : ThmSpan)
    (richSnippets            : Array (String × Array String × Array String))
    (outerAnonTypes          : Array String := #[])
    (outerAnonInlinedTerms   : Array String := #[])
    (outerNamedInlinedTerms  : Array (String × String) := #[])
    : Array String × Array String := Id.run do
  let entries := richSnippets.filterMap fun (snip, anons, inlined) => parseSnippet snip anons inlined
  -- Count total occurrences of each haveName (to decide whether suffixes are needed).
  let countTotal (name : String) : Nat :=
    entries.foldl (fun n e => if e.haveName == name then n + 1 else n) 0
  -- Mutable seen-count table: Array of (name, seenSoFar) pairs.
  let findSeen (table : Array (String × Nat)) (name : String) : Nat :=
    (table.find? fun p => p.1 == name) |>.map (·.2) |>.getD 0
  let bumpSeen (table : Array (String × Nat)) (name : String) : Array (String × Nat) :=
    let n := findSeen table name
    (table.filter fun p => p.1 != name).push (name, n + 1)
  let mut seenTable : Array (String × Nat) := #[]
  let mut preamble  : Array String := #[]
  let mut bodyLines : Array String := lines.extract span.bodyStart span.bodyEnd
  for entry in entries do
    let total := countTotal entry.haveName
    let seen  := findSeen seenTable entry.haveName
    seenTable := bumpSeen seenTable entry.haveName
    -- Unique suffix: none for a unique have name; "_N" (1-based) for duplicates.
    let uniqHaveName :=
      if total == 1 then entry.haveName
      else entry.haveName ++ "_" ++ toString (seen + 1)
    let uniqExtName' := span.name ++ "_aux_" ++ uniqHaveName
    -- If this lemma name already appears as a declaration before the current span
    -- (i.e. the source file already has a private lemma with that name), add "_h"
    -- to avoid a duplicate-declaration error.
    let preSpanLines := lines.extract 0 span.headerStart
    let uniqExtName :=
      if preSpanLines.any (fun l => containsWord l uniqExtName') then
        uniqExtName' ++ "_h"
      else
        uniqExtName'
    -- The base extName as stored in entry.sig (same stem, no suffix yet).
    let baseExtName := span.name ++ "_aux_" ++ entry.haveName
    -- Rewrite the sig to use the unique lemma name.
    let uniqSig := entry.sig.replace baseExtName uniqExtName
    match findHaveLine bodyLines entry.haveName 0 with
    | none => continue  -- have not found (already replaced or absent)
    | some relIdx =>
      let haveLineText := bodyLines[relIdx]!
      let (proofBody, relEnd) := extractHaveBody bodyLines relIdx
      -- Collect the full block text (header + body) for type annotation extraction.
      let haveBlockLines := bodyLines.extract relIdx relEnd
      let haveBlockText  := "\n".intercalate haveBlockLines.toList
      -- True when the have proof uses `by` tactics; false for term-mode proofs.
      let isTacticHave := (haveBlockText.splitOn ":= by").length ≥ 2
      let typeAnnotation :=
        let header :=
          match haveBlockText.splitOn ":= by" with
          | h :: _ => h.trimLeft
          | []     => haveLineText.trimLeft
        match header.splitOn " : " with
        | _ :: rest =>
          let joined := " : ".intercalate rest
          -- Collapse multi-line type to one line (continuation lines are more-indented).
          let collapsed := joined.trimRight.splitOn "\n"
            |>.map String.trimLeft
            |>.filter (!·.isEmpty)
            |> " ".intercalate
          -- For term-mode, "collapsed" ends with " := body"; strip that to get only
          -- the type.  For tactic-mode, ":= by" was already split out, so no
          -- " :=" remains and the match falls through to the unchanged collapsed form.
          match collapsed.splitOn " :=" with
          | typ :: _ :: _ => typ.trim
          | _             => collapsed
        | _ => ""
      -- When the source-level type annotation is available, override the MetaM return type
      -- in uniqSig with it.  ppExpr can drop type ascriptions on numeric literals (e.g.
      -- `(1:ℝ)/2` → `1/2`) because the MetaM context makes the ℝ type redundant, but
      -- the extracted lemma is elaborated without that context and infers ℕ division instead.
      -- The source annotation has the correct type ascriptions as written by the user.
      let uniqSig :=
        if !typeAnnotation.isEmpty then
          match uniqSig.splitOn " :\n" with
          | params :: _ => params ++ " :\n    " ++ typeAnnotation
          | _           => uniqSig
        else uniqSig
      -- Build the call from the lemma's PARAMETER list only (not the return type).
      -- Stop parsing at " :\n" which separates params from the return type in
      -- pretty-printed output, so that ∀-bound variables in the return type are
      -- not mistaken for explicit parameters.
      let paramSig :=
        match uniqSig.splitOn " :\n" with
        | first :: _ => first
        | []         => uniqSig
      let sigArgs : List String :=
        topLevelParenGroups paramSig |>.filterMap fun group =>
          match group.splitOn " : " with
          | first :: (_ :: _) => some first.trim
          | _                 => none
      let allArgs := sigArgs.foldl (fun acc names => acc ++ names.splitOn " ") []
      let call :=
        if allArgs.isEmpty then uniqExtName
        else "(" ++ uniqExtName ++ " " ++ " ".intercalate allArgs ++ ")"
      -- Sig-return-type fallback: if no source-level type annotation, use the sig's
      -- return type (from MetaM `ppExpr`) when it's an equation.  This lets
      -- `inlineOneLinersStep` detect the equation type on the one-liner line
      -- for correct preserve/Case-C handling.
      let sigReturnType : String :=
        match uniqSig.splitOn " :\n" with
        | _ :: rest =>
          let raw := (" :\n".intercalate rest).trimLeft
          raw.splitOn "\n"
             |>.map String.trimLeft
             |>.filter (!·.isEmpty)
             |> " ".intercalate
        | _ => ""
      let sigIsEq : Bool :=
        !sigReturnType.isEmpty &&
        ((sigReturnType.splitOn " = ").length ≥ 2 ||
         (sigReturnType.splitOn "↔").length ≥ 2)
      let effectiveTypeAnnotation :=
        if !typeAnnotation.isEmpty then typeAnnotation
        else if sigIsEq then sigReturnType
        else ""
      -- ONE-LINER replacement (preserves the original `have` binding name).
      -- A `have` sharing its line with a `·` bullet (`"· have h : T := ..."`) needs the
      -- bullet split onto its own line so the one-liner have gets valid, unambiguous
      -- indentation (mirrors the same split `preprocessBodyLines` Case 1 does later).
      let bulletIndentStr := String.mk (List.replicate (lineIndent haveLineText) ' ')
      let isBulletAttached := haveLineText.trimLeft.startsWith "· "
      let indent := if isBulletAttached then bulletIndentStr ++ "  " else bulletIndentStr
      let oneLiner := indent ++ "have " ++ entry.haveName ++
                      (if effectiveTypeAnnotation.isEmpty then "" else " : " ++ effectiveTypeAnnotation) ++
                      " := " ++ call ++ "\n"
      -- Collect `unfold X at param` / `simp only [...] at param` lines that
      -- immediately precede this `have` at the same indent level.  These tactic
      -- calls transform a hypothesis in-place (e.g. `unfold lift_pm1 at hS`);
      -- the extracted lemma needs to re-execute them since it receives the param
      -- in its original (un-transformed) form.
      --
      -- Guard: for `unfold X at arg`, only include the line if X actually appears
      -- in arg's type in uniqSig.  If a prior tactic (e.g. `contrapose!`) already
      -- transformed arg's type, the extracted lemma receives arg in the
      -- post-transform form and re-running `unfold X at arg` would fail because X
      -- is no longer present.
      let haveIndent := lineIndent haveLineText
      -- Look up the type of a sig parameter by name (content inside its paren group).
      let argType (arg : String) : String :=
        (topLevelParenGroups paramSig |>.findSome? fun group =>
          match group.splitOn " : " with
          | name :: rest =>
            if name.trim == arg then some (" : ".intercalate rest)
            else none
          | _ => none).getD ""
      let setupLines : List String :=
        (bodyLines.extract 0 relIdx).toList.filter fun l =>
          let t := l.trimLeft
          lineIndent l == haveIndent &&
          (t.startsWith "unfold " || (t.startsWith "simp only" && (t.splitOn " at ").length ≥ 2)) &&
          sigArgs.any fun arg =>
            (t.splitOn (" at " ++ arg)).length ≥ 2 &&
            -- For `unfold X [Y …] at arg`: skip if none of the unfold targets appear
            -- in arg's type (they were already eliminated by a prior tactic).
            (if t.startsWith "unfold " then
               let defNames :=
                 match t.splitOn " at " with
                 | first :: _ => first.splitOn " " |>.drop 1  -- remove "unfold" keyword
                 | _          => []
               defNames.any fun defName => !defName.isEmpty && ((argType arg).splitOn defName).length ≥ 2
             else true)
      let setupPreamble : String :=
        if setupLines.isEmpty then ""
        else "\n".intercalate (setupLines.map fun l => "  " ++ l.trimLeft) ++ "\n"
      -- Emit the private lemma.  Tactic-mode: `:= by` block with inlined one-liners.
      -- Term-mode: `:= body` (the body is a term, not a tactic sequence).
      let lemmaText :=
        if isTacticHave then
          let proofLines   := proofBody.splitOn "\n" |>.map (fun l => "  " ++ l) |>.toArray
          -- Thread valAnonTypes so inlineOneLinersStep can detect equation types
          -- for h_auto_N haves inside this private lemma's proof body.
          let inlinedProof := inlineOneLiners proofLines entry.valAnonTypes
          let processedProof := processAutoNamedHaves inlinedProof entry.valAnonInlinedTerms allArgs
          uniqSig ++ " :=\n  by\n" ++ setupPreamble ++ "\n".intercalate processedProof.toList
        else
          uniqSig ++ " :=\n  " ++ proofBody
      preamble := preamble.push lemmaText
      -- For term-mode haves with a same-line semicolon continuation
      -- (e.g. "have h := term; rw at h; exact h"), preserve the continuation
      -- as a separate tactic line after the one-liner so no tactics are lost.
      let termContinuation : String :=
        if isTacticHave then ""
        else
          let afterEq :=
            match haveLineText.trimLeft.splitOn ":=" with
            | _ :: rest => (":=".intercalate rest).trimLeft
            | _         => ""
          match splitAtOuterSemi afterEq with
          | some (_, cont) => cont.trim
          | none           => ""
      -- Replace the have block with the one-liner (plus any continuation) in bodyLines.
      -- If the original have was bullet-attached, restore the bullet on its own line first.
      let replacementLines : Array String :=
        (if isBulletAttached then #[bulletIndentStr ++ "·"] else #[]) ++
        (if termContinuation.isEmpty then #[oneLiner]
         else #[oneLiner, indent ++ termContinuation])
      let newBody : Array String :=
        bodyLines.extract 0 relIdx ++ replacementLines ++ bodyLines.extract relEnd bodyLines.size
      bodyLines := newBody

  -- Inline any remaining `have h := term` one-liners in the theorem body.
  -- Thread outerAnonTypes for h_auto_N equation detection in the outer body.
  bodyLines := inlineOneLiners bodyLines outerAnonTypes
  -- Handle anonymous haves (h_auto_N): Cases E/F use MetaM inlined terms to emit
  -- `exact <term>` eliminating simp_all context-dependent haves; Case D v2 handles
  -- `cases NAME :` naming conflicts by renaming and prepending in bullets.
  bodyLines := processAutoNamedHaves bodyLines outerAnonInlinedTerms
  -- Convert remaining `have h := call` one-liners to `let h := call`.
  -- This keeps `h` accessible to `rw at h`, `norm_num at h`, `simp_all`, etc.
  -- while eliminating the `have` keyword.
  bodyLines := convertHavesToLet bodyLines
  -- Eliminate named `have` one-liners that survived convertHavesToLet (e.g. due to
  -- `specialize`, `at`-mutations, or `simp_all +decide` with inequality type) by
  -- emitting `exact <inlinedTerm>` using the MetaM-computed continuation term.
  bodyLines := eliminateNamedHavesWithInlinedTerms bodyLines outerNamedInlinedTerms
  let thmHeader := lines.extract span.headerStart span.bodyStart
  return (preamble, thmHeader ++ bodyLines)

-- ── Command ───────────────────────────────────────────────────────────────

/--
`#extract_haves_file "path/to/File.lean"`

Reads `File.lean` (which must already be imported so its theorems are in the
current environment), extracts every `have` block to a `private lemma`, and
writes `File_output.lean` next to the original.
-/
elab "#extract_haves_file " pathLit:str : command => do
  let inputPath  := pathLit.getString
  let fp         := System.FilePath.mk inputPath
  let stem       := fp.fileStem.getD "out"
  let outputPath := ((fp.parent.getD (System.FilePath.mk ".")) /
                      (stem ++ "_output.lean")).toString

  let src   ← IO.FS.readFile inputPath
  let lines := src.splitOn "\n" |>.toArray

  let spans := findTheorems lines

  -- For each theorem, look it up in the environment and call walk
  let env ← getEnv
  let mut outputSections : Array (Array String × Array String) := #[]
  let mut debugLog : Array String := #[s!"spans={spans.size}"]

  for span in spans do
    let thmName := span.name.toName       -- short name, used by walk for lemma naming
    let ciOpt   := env.find? span.fullName.toName  -- full name for env lookup
    match ciOpt with
    | none =>
      debugLog := debugLog.push s!"{span.name}:NOT_FOUND"
      -- Not found in environment — emit unchanged
      outputSections := outputSections.push (#[], lines.extract span.headerStart span.bodyEnd)
    | some ci =>
      match ci.value? with
      | none =>
        debugLog := debugLog.push s!"{span.name}:NO_VALUE"
        outputSections := outputSections.push (#[], lines.extract span.headerStart span.bodyEnd)
      | some val =>
        -- walkFull: snippets with per-snippet anon types (for private lemma bodies)
        -- walkAnonTypes: anon types for the outer theorem body
        let (richSnippets, outerAnonTypes, outerAnonInlinedTerms, outerNamedInlinedTerms) ← liftTermElabM <| MetaM.run' do
          lambdaTelescope val fun _ body => do
            let snips          ← walkFull thmName body
            let anons          ← walkAnonTypes body
            let anonInlined    ← walkAnonInlinedTerms body
            let namedInlined   ← walkNamedInlinedTerms body
            return (snips, anons, anonInlined, namedInlined)
        debugLog := debugLog.push s!"{span.name}:snips={richSnippets.size}"
        let (preamble, thmLines) := buildRefactored lines span richSnippets outerAnonTypes outerAnonInlinedTerms outerNamedInlinedTerms
        outputSections := outputSections.push (preamble, thmLines)

  -- Reconstruct the full file
  -- Strategy: rebuild by splicing sections; keep unchanged lines between theorems
  let mut outParts : Array String := #[]
  let mut covered  : Nat := 0

  -- Use .1/.2 field access; avoid nested for-in loop (causes stuck HAppend metavar in batch mode)
  for pair in spans.zip outputSections do
    let span     : ThmSpan      := pair.1
    let preamble : Array String  := pair.2.1
    let thmLines : Array String  := pair.2.2
    -- Lines between `covered` and this theorem's header
    if span.headerStart > covered then
      outParts := outParts.push ("\n".intercalate
        (lines.extract covered span.headerStart).toList)
    -- Preamble lemmas: use foldl instead of for-in to give batch compiler explicit types
    outParts := preamble.foldl (fun (acc : Array String) (s : String) => acc.push (s ++ "\n")) outParts
    -- Modified theorem
    outParts := outParts.push ("\n".intercalate thmLines.toList)
    covered := span.bodyEnd

  -- Trailing lines after last theorem
  if covered < lines.size then
    outParts := outParts.push ("\n".intercalate (lines.extract covered lines.size).toList)

  let output := "\n".intercalate outParts.toList

  IO.FS.writeFile outputPath output
  logInfo s!"#extract_haves_file: written to {outputPath} | {" ".intercalate debugLog.toList}"

/--
`#extract_haves_file_to "src/File.lean" "dst/Output.lean"`

Like `#extract_haves_file`, but writes to the explicitly specified output path
instead of the default `File_output.lean` next to the source.  Useful for
testing new versions of the extractor without overwriting the known-good output.
-/
elab "#extract_haves_file_to " srcLit:str dstLit:str : command => do
  let inputPath  := srcLit.getString
  let outputPath := dstLit.getString
  let src   ← IO.FS.readFile inputPath
  let lines := src.splitOn "\n" |>.toArray
  let spans := findTheorems lines
  let env ← getEnv
  let mut outputSections : Array (Array String × Array String) := #[]
  let mut debugLog : Array String := #[s!"spans={spans.size}"]
  for span in spans do
    let thmName := span.name.toName
    let ciOpt   := env.find? span.fullName.toName
    match ciOpt with
    | none =>
      debugLog := debugLog.push s!"{span.name}:NOT_FOUND"
      outputSections := outputSections.push (#[], lines.extract span.headerStart span.bodyEnd)
    | some ci =>
      match ci.value? with
      | none =>
        debugLog := debugLog.push s!"{span.name}:NO_VALUE"
        outputSections := outputSections.push (#[], lines.extract span.headerStart span.bodyEnd)
      | some val =>
        let (richSnippets, outerAnonTypes, outerAnonInlinedTerms, outerNamedInlinedTerms) ← liftTermElabM <| MetaM.run' do
          lambdaTelescope val fun _ body => do
            let snips          ← walkFull thmName body
            let anons          ← walkAnonTypes body
            let anonInlined    ← walkAnonInlinedTerms body
            let namedInlined   ← walkNamedInlinedTerms body
            return (snips, anons, anonInlined, namedInlined)
        debugLog := debugLog.push s!"{span.name}:snips={richSnippets.size}"
        let (preamble, thmLines) := buildRefactored lines span richSnippets outerAnonTypes outerAnonInlinedTerms outerNamedInlinedTerms
        outputSections := outputSections.push (preamble, thmLines)
  let mut outParts : Array String := #[]
  let mut covered  : Nat := 0
  for pair in spans.zip outputSections do
    let span     : ThmSpan      := pair.1
    let preamble : Array String  := pair.2.1
    let thmLines : Array String  := pair.2.2
    if span.headerStart > covered then
      outParts := outParts.push ("\n".intercalate
        (lines.extract covered span.headerStart).toList)
    outParts := preamble.foldl (fun (acc : Array String) (s : String) => acc.push (s ++ "\n")) outParts
    outParts := outParts.push ("\n".intercalate thmLines.toList)
    covered := span.bodyEnd
  if covered < lines.size then
    outParts := outParts.push ("\n".intercalate (lines.extract covered lines.size).toList)
  let output := "\n".intercalate outParts.toList
  IO.FS.writeFile outputPath output
  logInfo s!"#extract_haves_file_to: written to {outputPath} | {" ".intercalate debugLog.toList}"

-- ══════════════════════════════════════════════════════════════════════════
-- ITERATIVE, extract_goal-BASED HAVE EXTRACTION  (#extract_haves_iter_to)
-- ══════════════════════════════════════════════════════════════════════════
--
-- `#extract_haves_file`/`_to` above compute EVERY extracted lemma's signature
-- up front, in one MetaM walk over the elaborated proof term (`ExtractHaves.walk`).
-- This section takes a different approach: it processes one `have` at a time —
-- always the INNERMOST ("lowest-level") one, i.e. the one whose own proof
-- contains no further nested `have` — by reconstructing the literal source
-- PREFIX up to that `have` as a self-contained synthetic theorem, inserting
-- Mathlib's `extract_goal` tactic right where the `have` would open its own
-- sub-goal, running it, and parsing `extract_goal`'s message. `extract_goal`
-- already implements the "minimal relevant local context" computation
-- (`MVarId.cleanup`) that `ExtractHaves.walk` has to hand-roll via manual FVar
-- collection, so this sidesteps that machinery entirely — and since each probe
-- re-elaborates from literal source text, the target theorem never needs to
-- already be present in the environment (unlike `#extract_haves_file`, whose
-- documented limitation is exactly that requirement).

/-- Parse `src` as a single `command`, elaborate it in the CURRENT environment,
    and return every message logged during that elaboration, in order. Never
    permanently changes the environment (wrapped in `withoutModifyingEnv`) —
    only the message log (a separate part of the command state) survives. -/
private def elabCaptureMessages (src : String) : CommandElabM (Array String) := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command src with
  | .error _ => return #[]
  | .ok stx =>
    -- `MessageLog.toList`/`toArray` only reflect `unreported` messages — messages can
    -- be silently promoted to `reported` mid-elaboration (e.g. via snapshot reporting),
    -- so diffing on those would miss messages logged deep inside `elabCommand`.
    -- `reportedPlusUnreported` is stable across that transition.
    let before := (← get).messages.reportedPlusUnreported.toList.length
    -- `Elab.async` (on by default) defers a `theorem`'s BODY elaboration — where
    -- `extract_goal`'s message actually gets logged — to a background snapshot task
    -- that is not merged into this state before `elabCommand` returns. Force
    -- synchronous elaboration so the message is visible immediately afterward.
    -- (Options live in the scope stack for `CommandElabM`, not the reader context,
    -- so `withScope` — not `withOptions`, which `CommandElabM` has no instance for.)
    withoutModifyingEnv (withScope (fun sc => { sc with opts := sc.opts.setBool `Elab.async false })
      (elabCommand stx))
    let afterList := (← get).messages.reportedPlusUnreported.toList
    (afterList.drop before).toArray.mapM (·.toString)

/-- Parse `src` as a single `command`, elaborate it (rolled back, same as
    `elabCaptureMessages`), and report whether that elaboration logged any
    ERROR-severity message. Unlike `elabCaptureMessages` (which stringifies
    every message, losing severity), this keeps the real `Message` values just
    long enough to check `.severity` — the actual, authoritative signal for
    "did this compile," as opposed to guessing from message TEXT. Used to
    empirically VERIFY a candidate change (e.g. dropping a parameter believed
    unused) by literally re-elaborating the modified declaration, rather than
    reasoning about whether some downstream tactic secretly depends on it —
    a text-based "is this name used" check cannot see, e.g., that `omega` or
    `simp_all` consult every hypothesis in context regardless of whether it's
    named anywhere; actually asking the elaborator sidesteps that entirely.

    Crucially forces `autoImplicit`/`relaxedAutoImplicit` OFF regardless of the
    calling (driver) file's own settings: the driver typically does NOT set
    these `false` itself, but the SOURCE file (and hence the written-out
    target file) usually does — so without forcing them off here too, a
    genuinely-missing identifier (e.g. dropping a parameter the return type
    still mentions) gets silently auto-generalized into a fresh, disconnected
    implicit instead of raising the "unknown identifier" error the real file
    would report, making this check falsely pass. Confirmed as a real failure
    mode, not a hypothetical: dropping `(d : Nat)` from a signature whose
    return type still used `d` passed this check before this fix, then failed
    with "Unknown identifier `d`" everywhere `d` was used once the file was
    actually checked for real. -/
private def elabCheckFirstError (src : String) : CommandElabM (Option String) := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command src with
  | .error e => return some s!"PARSE: {e}"
  | .ok stx =>
    let before := (← get).messages.reportedPlusUnreported.toList.length
    let aiOn ← probeAutoImplicitRef.get
    let setOpts (o : Options) : Options :=
      o.setBool `Elab.async false |>.setBool `autoImplicit aiOn |>.setBool `relaxedAutoImplicit aiOn
    withoutModifyingEnv (withScope (fun sc => { sc with opts := setOpts sc.opts }) (elabCommand stx))
    let afterList := (← get).messages.reportedPlusUnreported.toList
    let newMsgs := afterList.drop before
    match newMsgs.find? (fun m => m.severity == .error) with
    | none => return none
    | some m => return some (← m.toString)

/-- `logInfo` + crash-surviving append to the probe-log sidecar (see
    `probeLogPathRef`). Used for every probe/rejection line so a mid-decl
    kill (disk auto-stop) still leaves the diagnosis material on disk. -/
private def plogInfo (msg : String) : CommandElabM Unit := do
  logInfo msg
  if let some p ← probeLogPathRef.get then
    try IO.FS.withFile p .append fun h => h.putStrLn msg
    catch _ => pure ()

private def elabCheckOk (src : String) : CommandElabM Bool := do
  return (← elabCheckFirstError src).isNone

/-- Multi-command variant of `elabCheckFirstError`: parse each element of
    `srcs` as a single command, elaborate them IN SEQUENCE inside ONE
    rolled-back environment (so later commands see earlier ones' declarations
    — e.g. a rewritten theorem body calling the just-assembled aux lemma), and
    return the first ERROR-severity message from any of them. This is the
    DECLARATION-LEVEL COMMIT GATE's engine: verifying the assembled lemma
    alone (bug #11's gate) says nothing about the REWRITTEN THEOREM — a
    callsite one-liner whose stated type changed (e.g. the unfold rung's
    definition-free form) can break downstream SYNTACTIC consumers in the
    same proof (`rw` patterns no longer match; `linarith` sees different
    atoms), which only re-elaborating the whole rewritten declaration can
    catch. Observed for real: `hη_sq` extracted with an unfolded type broke
    the sibling `hsq`'s inline `rw`, shipping the first-ever broken output
    file (2 errors) before this gate existed. -/
private def elabCheckFirstErrorSeq (srcs : List String) : CommandElabM (Option String) := do
  let env ← getEnv
  let mut stxs : Array Syntax := #[]
  for src in srcs do
    match Lean.Parser.runParserCategory env `command src with
    | .error e => return some s!"PARSE: {e}"
    | .ok stx => stxs := stxs.push stx
  let before := (← get).messages.reportedPlusUnreported.toList.length
  let aiOn ← probeAutoImplicitRef.get
  let setOpts (o : Options) : Options :=
    o.setBool `Elab.async false |>.setBool `autoImplicit aiOn |>.setBool `relaxedAutoImplicit aiOn
  withoutModifyingEnv (withScope (fun sc => { sc with opts := setOpts sc.opts }) do
    for stx in stxs do
      elabCommand stx)
  let afterList := (← get).messages.reportedPlusUnreported.toList
  match (afterList.drop before).find? (fun m => m.severity == .error) with
  | none => return none
  | some m => return some (← m.toString)

/-- Parse+elaborate `src` (rolled back, same probe discipline as
    `elabCheckFirstError`) and return the VALUE (stored proof term) of the
    declaration it declares, looked up BEFORE the rollback. This is the door
    to proof-term-level analysis of a declaration the pipeline only has as
    TEXT: a tactic-mode `have` survives elaboration as an inspectable redex
    (see `collectHaveRedexUsage`), so questions the surface syntax cannot
    answer — "did the downstream `simp_all` actually consume this have?" —
    are answered exactly by the elaborated term. -/
private def elabGetDeclInfo (src : String) (declName : Name) : CommandElabM (Option ConstantInfo) := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command src with
  | .error _ => return none
  | .ok stx =>
    let aiOn ← probeAutoImplicitRef.get
    let setOpts (o : Options) : Options :=
      o.setBool `Elab.async false |>.setBool `autoImplicit aiOn |>.setBool `relaxedAutoImplicit aiOn
    withoutModifyingEnv do
      withScope (fun sc => { sc with opts := setOpts sc.opts }) (elabCommand stx)
      return (← getEnv).find? declName

/-- Collect have-style redexes — `(fun x => b) v` (tactic-mode `have`),
    `letFun v (fun x => b)` (term-mode `have`), and `.letE` (`let`) — from a
    proof term, recording for each whether the bound variable actually OCCURS
    in `b` (`hasLooseBVar 0`). This answers "was this have consumed by the
    downstream proof — including by context-sweeping tactics like `simp_all`
    that name no hypotheses in their syntax" purely from the STORED proof
    term, with no tactic re-execution: `simp_all`'s reconstructed proof
    references exactly the hypotheses it NEEDED, not those it merely
    processed. Caveats: USED means the proof ROUTES THROUGH the have, not
    that it's irreplaceable (simp_all may be able to rederive the fact
    without it — usage ≠ necessity, which is why the ladder below still
    ablates empirically rather than trusting USED as "keep"); and a have used
    only for definitional rfl-style rewriting can leave no trace (UNUSED) —
    but such a use is by definition erasable, so the verdict remains correct
    for elimination purposes. -/
private partial def collectHaveRedexUsage (e : Expr) (acc : Array (Name × Bool)) :
    Array (Name × Bool) :=
  if e.isAppOfArity ``letFun 4 then
    let args := e.getAppArgs
    let v := args[2]!
    match args[3]! with
    | .lam n _ b _ => collectHaveRedexUsage b (collectHaveRedexUsage v (acc.push (n, b.hasLooseBVar 0)))
    | f => collectHaveRedexUsage f (collectHaveRedexUsage v acc)
  else
    match e with
    | .app (.lam n _ b _) v => collectHaveRedexUsage b (collectHaveRedexUsage v (acc.push (n, b.hasLooseBVar 0)))
    | .app f a => collectHaveRedexUsage a (collectHaveRedexUsage f acc)
    | .lam _ _ b _ => collectHaveRedexUsage b acc
    | .forallE _ _ b _ => collectHaveRedexUsage b acc
    | .letE n _ v b _ => collectHaveRedexUsage b (collectHaveRedexUsage v (acc.push (n, b.hasLooseBVar 0)))
    | .mdata _ b => collectHaveRedexUsage b acc
    | .proj _ _ b => collectHaveRedexUsage b acc
    | _ => acc

/-- Peel the leading `∀`-binders of a declaration's TYPE (and, in lockstep, the
    matching `fun`-binders of its VALUE when the shapes line up) and report,
    for each binder in order, its name and whether the variable is USED
    anywhere after its own introduction — in a later binder's type, the return
    type, or the proof body. The proof-term side is what makes this
    authoritative even for context-sweeping tactics (`omega`, `simp_all`,
    `aesop`, ...): their reconstructed proofs reference exactly the hypotheses
    they consumed, though their SYNTAX names none of them (same principle as
    `collectHaveRedexUsage`, applied to a lemma's parameters instead of its
    haves). Conservative on shape mismatch: a binder whose value-side λ can't
    be found is reported USED. -/
private partial def binderUsage (ty : Expr) (val? : Option Expr) (acc : Array (Name × Bool)) :
    Array (Name × Bool) :=
  match ty with
  | .forallE n _ tyBody _ =>
    match val?.map Expr.consumeMData with
    | some (.lam _ _ valBody _) =>
      binderUsage tyBody (some valBody)
        (acc.push (n, tyBody.hasLooseBVar 0 || valBody.hasLooseBVar 0))
    | _ =>
      binderUsage tyBody none (acc.push (n, true))
  | _ => acc

/-- Like `elabCaptureMessages`, but the environment change is KEPT (not rolled
    back). Used to make a just-extracted private lemma's NAME resolvable to
    LATER probes within the same theorem: each probe is a fresh, literal
    re-elaboration of a source snippet, and has no way to see an earlier
    extraction that exists only as a text edit to `lines`, not as a real
    declaration — UNLESS we actually add a (stub) declaration for it here. -/
private def elabPersistCommand (src : String) : CommandElabM Unit := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command src with
  | .error _ => pure ()
  | .ok stx =>
    withScope (fun sc => { sc with opts := sc.opts.setBool `Elab.async false }) (elabCommand stx)

/-- Find the first captured message shaped like `"theorem NAME ... := sorry"` or
    `"def NAME ... := sorry"` (this is exactly `extract_goal`'s output format),
    and return the `"NAME ... : TYPE"` portion with the leading keyword and the
    trailing `:= sorry` stripped. -/
private def findExtractedSignature (msgs : Array String) : Option String := Id.run do
  for m in msgs do
    let mt := m.trim
    for kw in (["theorem ", "def "] : List String) do
      if mt.startsWith kw then
        let rest := mt.drop kw.length
        let stripped :=
          if rest.endsWith ":= sorry" then (rest.dropRight ":= sorry".length).trimRight
          else rest
        return some stripped
  return none

/-- Collapse a possibly-multi-line string down to ONE physical line (interior
    whitespace/newlines trimmed to single spaces). `extract_goal` line-wraps long
    binder groups as `NAME :\n    TYPE` (colon then NEWLINE, no trailing space
    before it) — any naive `.splitOn " : "` on such a group's raw text fails to
    find the separator at all (there's no space right after the colon), silently
    treating the WHOLE group (name + type glued together) as "the name", which
    then gets mangled further (e.g. blindly split on spaces into garbage
    "argument names"). Normalizing first makes every `NAME : TYPE` split robust
    regardless of how the source text happened to be wrapped. -/
private def collapseToOneLine (s : String) : String :=
  " ".intercalate (s.splitOn "\n" |>.map String.trim |>.filter (·.length > 0))

/-- Scan `s` for a sequence of bracket-delimited binder groups — `(..)`, `{..}`,
    `[..]`, `⦃..⦄` — starting at the first non-whitespace character, tracking
    bracket depth across all four kinds together (Lean binders are always
    well-nested, so this is unambiguous). Stops at the first point where the
    next non-whitespace character is not an opening bracket (where ` : TYPE`
    begins). Returns the group substrings (including their own delimiters). -/
private def scanBinderGroups (s : String) : Array String × String := Id.run do
  let chars := s.toList.toArray
  let n := chars.size
  let isOpen  (c : Char) := c == '(' || c == '{' || c == '[' || c == '⦃'
  let isClose (c : Char) := c == ')' || c == '}' || c == ']' || c == '⦄'
  let mut i := 0
  let mut groups : Array String := #[]
  let mut go := true
  while go do
    while i < n && chars[i]!.isWhitespace do i := i + 1
    if i < n && isOpen chars[i]! then
      let start := i
      let mut depth := 0
      let mut first := true
      while first || depth > 0 do
        let c := chars[i]!
        i := i + 1
        if isOpen c then depth := depth + 1
        else if isClose c then depth := depth - 1
        first := false
      groups := groups.push (String.mk (chars.extract start i).toList)
    else
      go := false
  return (groups, String.mk (chars.extract i n).toList)

/-- Parse a captured `extract_goal` signature string (e.g.
    `"__sig__ (i j k : Nat) (h0 : i ≤ j) : i ≤ k"`) into
    (capturedName, argNames-for-the-call-site, textAfterName-verbatim,
    justTheReturnType — the ` : TYPE` tail with its leading " : " stripped,
    paramsOnlyText — just the reconstructed binder groups, e.g.
    `" (i j k : Nat) (h0 : i ≤ j)"`, with NO return type — needed because the
    captured return type can be MISSING type ascriptions on bound variables
    (`∑ x, ...` instead of `∑ x : hypercube n, ...`) that were only inferable
    inside the ORIGINAL probe's elaboration context; re-attaching the have's own
    source-level type text (which always has the ascriptions the user wrote)
    to these reconstructed params is what actually fixes that,
    rawGroups — the same binder groups un-joined, so a caller can override an
    individual PARAMETER's (not just the return type's) captured text — needed
    because a reverted-context hypothesis referring to an EARLIER extracted
    have has the exact same ascription-dropping problem, but for a param
    instead of the return type; there's no "source text" for a param, but the
    earlier have's own one-liner replacement (already correctly re-ascribed)
    is sitting in `lines` and can be substituted in instead). -/
private def parseExtractedSignature (sig : String) :
    Option (String × List String × String × String × String × Array String) :=
  Id.run do
    let chars := sig.toList.toArray
    let n := chars.size
    let isNameChar (c : Char) :=
      !(c == ' ' || c == '(' || c == '{' || c == '[' || c == '⦃' || c == '\n')
    let mut i := 0
    while i < n && isNameChar chars[i]! do i := i + 1
    if i == 0 then return none
    let capturedName := String.mk (chars.extract 0 i).toList
    let restAfterName := String.mk (chars.extract i n).toList
    let (groups, remainder) := scanBinderGroups restAfterName
    -- Only genuinely-EXPLICIT `(...)` groups belong in a positional call: `{...}`
    -- (implicit), `[...]` (instance), and `⦃...⦄` (strict-implicit) parameters are
    -- inferred automatically, and applying them positionally shifts every
    -- following explicit argument into the wrong slot (e.g. calling `n` against a
    -- lemma with `{n : Nat} (hS : S.Nonempty)` binds `n` to `hS`'s slot instead).
    let argNames : List String := groups.toList.foldl (fun acc g =>
        if !g.startsWith "(" then acc
        else
          let inner := collapseToOneLine ((g.drop 1).dropRight 1)
          let namesPart := match inner.splitOn " : " with
            | first :: (_ :: _) => first
            | _ => inner
          acc ++ (namesPart.trim.splitOn " " |>.filter (·.length > 0))) []
    let retType := match remainder.trimLeft.splitOn ":" with
      | _ :: rest => (":".intercalate rest).trim
      | [] => remainder.trim
    let paramsOnlyText := groups.toList.foldl (fun acc g => acc ++ " " ++ collapseToOneLine g) ""
    return some (capturedName, argNames, restAfterName, retType, paramsOnlyText, groups)

/-- Separators used by Lean/Mathlib's bounded-quantifier notation (`∀ x ∈ s, P`,
    `∀ x ≥ a, P`, `∀ x ≤ a, P`, `∀ x < a, P`, `∀ x > a, P`) — each is sugar for
    `∀ x, x REL bound → P`. Tried in this fixed order against a binder group
    with no `:` and no parens, in `dropOneLeadingForallLevel`. -/
private def boundedQuantifierRels : List String := [" ∈ ", " ≥ ", " ≤ ", " > ", " < "]

/-- Strip exactly ONE leading `∀ ... ,` level from `ty` (if any) and return
    `(namesBoundByThatLevel, remainderAfterIt)` — e.g.
    `"∀ (c : Nat), a + c = b + c"` ↦ `(["c"], "a + c = b + c")`. Returns
    `([], ty.trim)` (no-op) when `ty` doesn't start with `∀`. Factored out of
    `leadingForallBoundNames`/`dropLeadingForallHeader` so both can loop it
    across a CHAIN of consecutive leading `∀`s (`∀ x, ∀ hs, P` has two levels,
    not one) rather than handling only the outermost. -/
private def dropOneLeadingForallLevel (ty : String) : List String × String := Id.run do
  let t := ty.trim
  if !t.startsWith "∀" then return ([], t)
  let afterForall := (t.drop 1).trim
  let chars := afterForall.toList.toArray
  let n := chars.size
  let isOpen  (c : Char) := c == '(' || c == '{' || c == '[' || c == '⦃'
  let isClose (c : Char) := c == ')' || c == '}' || c == ']' || c == '⦄'
  let mut depth := 0
  let mut commaPos := n
  let mut i := 0
  while i < n && commaPos == n do
    let c := chars[i]!
    if isOpen c then depth := depth + 1
    else if isClose c then depth := depth - 1
    else if c == ',' && depth == 0 then commaPos := i
    i := i + 1
  if commaPos == n then return ([], t)
  let bindersText := String.mk (chars.extract 0 commaPos).toList
  let afterComma := (String.mk (chars.extract (commaPos + 1) n).toList).trim
  let (groups, _) := scanBinderGroups (bindersText ++ " ")
  if !groups.isEmpty then
    let names := groups.toList.foldl (fun acc g =>
        let inner := collapseToOneLine ((g.drop 1).dropRight 1)
        let namesPart := match inner.splitOn " : " with
          | first :: (_ :: _) => first
          | _ => inner
        acc ++ (namesPart.trim.splitOn " " |>.filter (·.length > 0))) []
    return (names, afterComma)
  else if boundedQuantifierRels.any (fun rel => ((collapseToOneLine bindersText).splitOn rel).length ≥ 2) then
    -- Bounded-quantifier sugar `∀ i ∈ S, body` / `∀ k ≥ d, body` / etc, notation
    -- for `∀ i, i ∈ S → body` — `revert`/`extract_goal` capture `i` as a REAL
    -- flat parameter (matching the OTHER binder forms above) but re-print the
    -- RETURN type back in this same bounded notation, so `i` would otherwise
    -- get bound TWICE. Since `i` is now a real param, what's left of the
    -- obligation is `i ∈ S → body` (the bound fact becomes a plain hypothesis
    -- over the now-fixed `i`).
    let collapsed := collapseToOneLine bindersText
    let namePart := (boundedQuantifierRels.findSome? fun rel =>
      match collapsed.splitOn rel with
      | first :: (_ :: _) => some first
      | _ => none).getD collapsed
    let names := namePart.trim.splitOn " " |>.filter (·.length > 0)
    return (names, collapsed ++ " → " ++ afterComma)
  else
    -- No-parens form: `∀ c d : Nat, ...` — names are everything before " : ".
    -- If there's no `:` at all, it's a BARE (type-inferred) binder like
    -- `∀ x, body` or `∀ x y, body` — the whole (collapsed) text is the names.
    let collapsed := collapseToOneLine bindersText
    let names := match collapsed.splitOn " : " with
      | first :: (_ :: _) => first.trim.splitOn " " |>.filter (·.length > 0)
      | _ => collapsed.trim.splitOn " " |>.filter (·.length > 0)
    return (names, afterComma)

/-- Names bound by `ty`'s ENTIRE leading CHAIN of `∀`s, e.g.
    `"∀ x : Nat, ∀ hs : Fin 2 → Nat, P"` ↦ `["x", "hs"]` (not just `["x"]`).
    Needed because `extract_goal`'s `revert` prenexes EVERY level of a have's
    own leading `∀`-chain as its own separate parameter group (not just the
    outermost), together with genuine reverted context hypotheses — so ALL
    of them must be excluded from call-site arguments (they aren't in scope
    where the have appears, and leaving them off keeps the call's result
    correctly `∀`-quantified), unlike the real context hypotheses. -/
private def leadingForallBoundNames (ty : String) : List String := Id.run do
  let mut acc : List String := []
  let mut cur := ty.trim
  let mut go := true
  while go do
    let (names, rest) := dropOneLeadingForallLevel cur
    if names.isEmpty then go := false
    else
      acc := acc ++ names
      cur := rest
  return acc

/-- Strip `ty`'s ENTIRE leading CHAIN of `∀`s (not just the outermost level —
    see `leadingForallBoundNames`'s docstring for why a chain can be more than
    one level deep). Companion to `leadingForallBoundNames`: those same names
    are re-attached as REAL parameters in the extracted lemma's own signature
    (via the captured, `revert`-prenexed binder groups), so leaving ANY level
    of the `∀`-chain in the return type would bind its names TWICE (e.g.
    `(x : Nat) (hs : Fin 2 → Nat) : ∀ hs : Fin 2 → Nat, ...` — a
    duplicate-binder error for `hs` if only the outer `∀ x` were stripped). -/
private def dropLeadingForallHeader (ty : String) : String := Id.run do
  let mut cur := ty.trim
  let mut go := true
  while go do
    let (names, rest) := dropOneLeadingForallLevel cur
    if names.isEmpty then go := false
    else cur := rest
  return cur

/-- Locate every NAMED have-header line (bullet-attached or not) within
    `lines[from_..to_)`. Anonymous `have := term` bindings are skipped — out of
    scope for this iterative extractor. Returns `(lineIdx, haveName)` pairs in
    source order. -/
private def findAllHaveHeaders (lines : Array String) (from_ to_ : Nat) : Array (Nat × String) :=
  Id.run do
    let mut result : Array (Nat × String) := #[]
    let mut i := from_
    while i < to_ do
      let l := lines[i]!
      let t := l.trimLeft
      let tCore := if t.startsWith "· " then t.drop 2 else t
      if tCore.startsWith "have " then
        let afterHave := tCore.drop "have ".length
        let nameStop := afterHave.find (fun c => c == ' ' || c == ':' || c == '=')
        let name := String.Pos.Raw.extract afterHave ⟨0⟩ nameStop
        -- destructuring `have ⟨...⟩` has no NAME — the raw `⟨l,` token leaked
        -- into a lemma name once ("PARSE: expected ':'"); the pre-pass
        -- `destructuringHavesToObtain` converts the convertible ones, and any
        -- leftover (e.g. bullet-attached) must simply never be attempted.
        if !name.isEmpty && !name.startsWith "⟨" then
          result := result.push (i, name)
      i := i + 1
    return result

/-- DESTRUCTURING HAVES (#57): `have ⟨l, hl⟩ : T := proof` binds PATTERN
    components — there is no have-name for the extractor to target, and the
    raw text `⟨l,` leaked into a lemma name (CanonicalDTree 8/9, "PARSE:
    expected ':'" on every variant). Rewrite each into the equivalent
    named-have + obtain pair the pipeline already handles:
      have __destr_K : T := proof     ← extracts like any named have
      obtain ⟨l, hl⟩ := __destr_K     ← stays behind as the consumer
    Runs inside the pre-pass REVERT-GATE (a rewrite that breaks the decl is
    rolled back wholesale). Bullet-attached (`· have ⟨...⟩`) forms are left
    alone — the obtain insertion point would be inside the bullet block —
    and `findAllHaveHeaders` skips `⟨`-named haves so they stay unconverted
    rather than producing garbage-name attempts. Bottom-up so insertions
    never shift the indices still to be visited. -/
private def destructuringHavesToObtain (lines : Array String) (span : ThmSpan) :
    Array String := Id.run do
  let mut out := lines
  for off in List.range (span.bodyEnd - span.bodyStart) do
    let i := span.bodyEnd - 1 - off
    if i >= out.size then continue
    let l := out[i]!
    let t := l.trimLeft
    if t.startsWith "have ⟨" then
      let indent := String.mk (List.replicate (lineIndent l) ' ')
      let afterHave := t.drop "have ".length
      -- matching top-level `⟩` (patterns nest: ⟨a, ⟨b, c⟩⟩)
      let mut depth := 0
      let mut cut : Option Nat := none
      let mut j := 0
      for c in afterHave.toList do
        if cut.isNone then
          if c == '⟨' then depth := depth + 1
          else if c == '⟩' then
            depth := depth - 1
            if depth == 0 then cut := some (j + 1)
        j := j + 1
      match cut with
      | none => pure ()
      | some cutN =>
        let pat := String.mk (afterHave.toList.take cutN)
        let rest := String.mk (afterHave.toList.drop cutN)
        -- `⟩ : T := ...` (typed) or `⟩ := ...` (untyped) — both keep working
        -- as `have __destr_K<rest>`; anything else (e.g. pattern spans
        -- multiple lines) is left alone.
        if rest.trimLeft.startsWith ":" then
          let nm := s!"__destr_{i}"
          let (_, relEnd) := extractHaveBody out i
          out := out.set! i (indent ++ "have " ++ nm ++ rest)
          out := out.extract 0 relEnd ++ #[indent ++ "obtain " ++ pat ++ " := " ++ nm] ++
                 out.extract relEnd out.size
  return out

/-- Among `headers` (found via `findAllHaveHeaders`), return the first one whose
    own extracted span (via `extractHaveBody`, bullet-aware) contains no OTHER
    have-header that isn't ALREADY in `doneNames` — i.e. a "leaf"/lowest-level
    have, safe to extract next. A have whose only nested haves have already been
    successfully extracted (and are now safe one-liner calls, textually still
    starting with `have `) counts as a leaf too — this is what lets extraction
    climb back UP through a have-in-have chain once every descendant is done,
    rather than getting stuck forever seeing its own already-extracted child's
    one-liner as "still nested". -/
private def findLeafHave (lines : Array String) (headers : Array (Nat × String))
    (doneNames : List String) : Option (Nat × String) := Id.run do
  for (idx, name) in headers do
    let (_, relEnd) := extractHaveBody lines idx
    let nested := findAllHaveHeaders lines (idx + 1) relEnd
    if nested.all (fun (_, n) => doneNames.contains n) then
      return some (idx, name)
  return none

/-- Every downstream mechanism here (`doneNames`, `findLeafHave`'s nesting check,
    the final `inlineOneLiners`/`convertHavesToLet` pass) identifies a `have` by
    its bare NAME, implicitly assuming that name is unique within the theorem —
    true for almost all proofs, but Lean itself permits a nested `have NAME`
    to legitimately SHADOW an outer `have` of the same name (e.g. an outer
    `have h : P ∧ Q := by have h : P := by ...; aesop`). Left alone, this
    collapses two independent bindings into one from our tools' point of view:
    `doneNames` marks the OUTER done as soon as the INNER (same name) is
    extracted (so the outer never gets its own turn), and the final inlining
    pass's name-based text substitution rewrites the outer's LATER uses to
    point at the inner's extracted lemma instead of its own. Since headers are
    returned in source order (outer always precedes a nested shadow), renaming
    every occurrence AFTER the first (to `NAME__dupK`, scoped to just that
    have's own extracted span) restores the uniqueness every other function
    here assumes, without changing what the proof means.

    The rename must cover more than the shadowing have's OWN proof — its
    binding stays in scope for the rest of whatever encloses it, and text
    there can reference it by name. Two distinct shapes both reuse a name:
    (1) NESTED — `have h : P ∧ Q := by have h : P := by ...; convert h ...`:
    the inner `h` shadows for the rest of the OUTER have's own body, so the
    rename must run through the outer's `extractHaveBody` end, not just the
    inner's own span (that `convert h` means the inner `h`).
    (2) SIBLING reuse — `have h : A := ...; have h : B := ...; use h`: the
    first `h`'s own span ends BEFORE the second `h` even starts, so bounding
    by "the previous same-named have's end" would produce an EMPTY range and
    rename nothing. Here the second `h` shadows until a THIRD same-named have
    (if any) reuses the name again, or otherwise through the theorem's end.
    Distinguishing them: if this have's own index falls INSIDE the previous
    same-named have's span, it's nested (case 1); otherwise it's a sibling
    reuse (case 2). -/
private def renameShadowedHaveNames (lines : Array String) (span : ThmSpan) : Array String :=
  Id.run do
    let mut lines := lines
    let headers := findAllHaveHeaders lines span.bodyStart span.bodyEnd
    -- All occurrence indices of each name, in source order — needed for the
    -- sibling case's bound (the NEXT same-named occurrence, if any).
    let mut occByName : List (String × Array Nat) := []
    for (idx, name) in headers do
      let cur := (occByName.lookup name).getD #[]
      occByName := (name, cur.push idx) :: occByName.filter (fun (n, _) => n != name)
    let mut countForName : List (String × Nat) := []
    for (idx, name) in headers do
      let priorCount := (countForName.lookup name).getD 0
      let newCount := priorCount + 1
      countForName := (name, newCount) :: countForName.filter (fun (n, _) => n != name)
      if newCount > 1 then
        let newName := name ++ s!"__dup{newCount}"
        let occs := (occByName.lookup name).getD #[]
        let prevIdx := occs.getD (newCount - 2) idx
        let (_, prevRelEnd) := extractHaveBody lines prevIdx
        let boundEnd :=
          if idx < prevRelEnd then prevRelEnd            -- case 1: nested
          else occs.getD newCount span.bodyEnd            -- case 2: sibling reuse
        for i in [idx:boundEnd] do
          lines := lines.set! i (replaceWord lines[i]! name newName)
    return lines

/-- Give every line-start ANONYMOUS have (`have := term`, `have : T := term`,
    bullet-attached variants) a synthetic name `h_anon_N`, renaming downstream
    `this` references to match (scoped: stops at the first less-indented
    nonblank line, or at the next `this`-rebinding statement — another
    anonymous `have`/`suffices`). Run before each extraction scan.

    WHY: `findAllHaveHeaders` skips empty-named haves, so anonymous haves were
    never extraction CANDIDATES at all — and that gap was then misread as
    "these haves are unextractable" once they survived to the output (the
    failure-vs-impossibility conflation: a have the pipeline never ATTEMPTED
    is not a have that CAN'T be converted — AXLE's `have2lemma` swaps exactly
    these shapes easily, see [[project_axle_have2lemma_simp_all]]). Once
    named, the existing revert-based anonymous-typed branch of
    `extractOneHaveViaGoal` handles them with NO new extraction machinery:
    the probe keeps the have verbatim, `revert`s it, and reads its true type
    off the captured signature. Only Lean's ANONYMOUS binders introduce
    `this`, so a named `have h : T := v` does NOT end the renaming scope. -/
private def nameAnonymousHaves (lines : Array String) (span : ThmSpan) : Array String := Id.run do
  let mut out := lines
  let mut counter := 0
  for i in [span.bodyStart:span.bodyEnd] do
    let l := out[i]!
    let t := l.trimLeft
    let bullet := if t.startsWith "· " then "· " else ""
    let core := t.drop bullet.length
    if core.startsWith "have :=" || core.startsWith "have : " then
      counter := counter + 1
      let newName := s!"h_anon_{counter}"
      let indentStr := String.mk (l.toList.takeWhile Char.isWhitespace)
      out := out.set! i (indentStr ++ bullet ++ "have " ++ newName ++ " " ++ core.drop "have ".length)
      let haveIndent := lineIndent l
      for j in [i+1:span.bodyEnd] do
        let lj := out[j]!
        if !isBlankLine lj && lineIndent lj < haveIndent then
          break
        let tj := lj.trimLeft
        let cj := if tj.startsWith "· " then tj.drop 2 else tj
        if cj.startsWith "have :=" || cj.startsWith "have : " || cj.startsWith "suffices" then
          break
        if containsWord lj "this" then
          out := out.set! j (replaceWord lj "this" newName)
  return out

/-- Split MID-LINE named term-mode haves (`... ; have h := term [; rest]`) in
    `span`'s body onto their own lines, mirroring `preprocessBodyLines`
    Case 3 exactly — but run BEFORE extraction rather than only in the final
    pass: the extraction scanner (`findAllHaveHeaders`) sees only line-START
    haves, so a mid-line have was never an extraction CANDIDATE at all — the
    same failure-vs-impossibility trap as anonymous haves (see
    `nameAnonymousHaves`), one normalization pass away from being ordinary.
    Returns `(newLines, didSplit)`; `didSplit = true` GROWS the line count,
    invalidating the caller's span — the caller must rescan before continuing
    (the extraction loop's `keepGoing` re-iteration does exactly that). -/
private def splitMidLineHavesInSpan (lines : Array String) (span : ThmSpan) :
    Array String × Bool := Id.run do
  let mut out : Array String := lines.extract 0 span.bodyStart
  let mut didSplit := false
  for i in [span.bodyStart:span.bodyEnd] do
    let l := lines[i]!
    match findMidLineHave l (allowAnon := true) with
    | some (before, haveAndRest) =>
      didSplit := true
      let indentStr := String.mk (l.toList.takeWhile Char.isWhitespace)
      let hasBulletInBefore := before.trimLeft.startsWith "· "
      let innerIndent := if hasBulletInBefore then indentStr ++ "  " else indentStr
      out := out.push before
      match splitAtOuterSemi haveAndRest with
      | some (hp, rp) =>
        out := out.push (innerIndent ++ hp)
        if !rp.isEmpty then out := out.push (innerIndent ++ rp)
      | none =>
        out := out.push (innerIndent ++ haveAndRest)
    | none => out := out.push l
  out := out ++ lines.extract span.bodyEnd lines.size
  return (out, didSplit)

/-- Names to `open` so a standalone synthetic probe (a bare top-level command, NOT
    nested inside whatever `namespace`/`open` context the real theorem sits in) can
    still resolve the SAME unqualified identifiers the real theorem does. Combines
    (1) the namespace(s) the theorem is textually nested in (from `span.fullName`
    vs `span.name`) and (2) every `open X Y ...` command appearing before the
    theorem in the file. Without this, any symbol defined in the file's own
    namespace (not from Mathlib) — e.g. `hypercube`, `char_S` — is unresolvable in
    the probe, cascading into "Function expected"/"Unknown identifier" errors. -/
private def neededOpens (lines : Array String) (span : ThmSpan) : List String := Id.run do
  let mut opens : List String := []
  if span.fullName.length > span.name.length then
    opens := opens ++ [span.fullName.dropRight (span.name.length + 1)]
  for i in List.range span.headerStart do
    let t := lines[i]!.trim
    if t.startsWith "open " then
      opens := opens ++ ((t.drop "open ".length).trim.splitOn " " |>.filter (·.length > 0))
  return opens

/-- Extract every name `X` mentioned in an `"Unknown identifier `X`"` message
    (Lean's exact error text for an unresolved identifier). -/
private def extractUnknownIdentifiers (msgs : Array String) : List String := Id.run do
  let mut result : List String := []
  for m in msgs do
    let parts := m.splitOn "Unknown identifier `"
    for part in parts.drop 1 do
      match part.splitOn "`" with
      | nm :: _ => if !result.contains nm then result := result ++ [nm]
      | [] => pure ()
  return result

/-- Find a top-level declaration named `name` anywhere in `lines` (`def`,
    `abbrev`, `lemma`, `theorem`, optionally `private`/`noncomputable`-prefixed)
    and return its full source text block, or `none` if not found. Used to give
    a probe access to a dependency it can't otherwise see — most commonly a
    `private` declaration from the target file, which Lean's privacy model
    makes structurally inaccessible to code elaborated as part of a DIFFERENT
    file (the probe is technically part of the driver file, not the target
    file, regardless of what it `open`s or imports). Re-declaring a fresh copy
    of the SAME text under the SAME name in the driver's own environment sidesteps
    this: Lean's privacy is per-declaring-module, and this makes the driver the
    declaring module for its own copy. -/
private def findAndExtractDecl (lines : Array String) (name : String) : Option String := Id.run do
  let kws := ["private noncomputable def ", "private noncomputable abbrev ",
              "private def ", "private lemma ", "private theorem ", "private abbrev ",
              "noncomputable def ", "noncomputable abbrev ",
              "def ", "lemma ", "theorem ", "abbrev "]
  for i in List.range lines.size do
    let l := lines[i]!
    if lineIndent l == 0 then
      for kw in kws do
        if l.startsWith kw then
          let rest := l.drop kw.length
          let nameEnd := rest.find (fun c => c == ' ' || c == '{' || c == '(' || c == ':')
          let declName := String.Pos.Raw.extract rest ⟨0⟩ nameEnd
          if declName == name then
            let endIdx := blockEnd lines (i + 1) 0
            return some ("\n".intercalate (lines.extract i endIdx).toList)
  return none

/-- Run `elabCaptureMessages` on `syntheticSrc`; if `extract_goal`'s message isn't
    found, check whether the failure cites an `"Unknown identifier"` that exists
    as a declaration somewhere in the ORIGINAL file (most commonly a `private`
    dependency, structurally invisible to this externally-elaborated probe no
    matter what it `open`s) — if so, persist a fresh copy of it (Lean's privacy
    is per-DECLARING-module, so a copy declared as part of the driver's own
    elaboration is fully visible to the driver's own later probes) and retry, up
    to a few times (bounded, in case resolution doesn't actually help). -/
private def captureWithDependencyRetry
    (lines : Array String) (openPrefix : String) (syntheticSrc : String) :
    CommandElabM (Array String) := do
  let mut msgs ← elabCaptureMessages syntheticSrc
  let mut copied : List String := []
  let mut retriesLeft := 4
  while (findExtractedSignature msgs).isNone && retriesLeft > 0 do
    retriesLeft := retriesLeft - 1
    let missing := (extractUnknownIdentifiers msgs).filter (fun nm => !copied.contains nm)
    if missing.isEmpty then
      retriesLeft := 0
    else
      let mut resolvedAny := false
      for nm in missing do
        match findAndExtractDecl lines nm with
        | some declText =>
          elabPersistCommand (openPrefix ++ declText)
          copied := nm :: copied
          resolvedAny := true
        | none => copied := nm :: copied
      if resolvedAny then
        msgs ← elabCaptureMessages syntheticSrc
      else
        retriesLeft := 0
  return msgs

/-- Special-case signature parsing for an ANONYMOUS/untyped have, probed via
    `have haveName := <original value/tactics>; revert haveName; extract_goal`.
    Lean's `revert` places the reverted variable among the new leading binders,
    so the captured signature has `haveName` itself as one of the parameter
    groups (mixed in with genuine reverted context) — extract exactly ITS type
    (this is `haveName`'s real, otherwise un-inferrable-without-the-value type)
    and every OTHER explicit group's names for the call site. `haveName` itself
    is excluded from both the extracted lemma's own signature and the call — it
    doesn't exist yet at the point the original have appears; it's what's being
    defined. Returns `(haveType, callArgNames, paramsText)`. -/
private def parseRevertedSignature (sig : String) (haveName : String) :
    Option (String × List String × String) := Id.run do
  let chars := sig.toList.toArray
  let n := chars.size
  let isNameChar (c : Char) :=
    !(c == ' ' || c == '(' || c == '{' || c == '[' || c == '⦃' || c == '\n')
  let mut i := 0
  while i < n && isNameChar chars[i]! do i := i + 1
  if i == 0 then return none
  let restAfterName := String.mk (chars.extract i n).toList
  let (groups, _) := scanBinderGroups restAfterName
  let mut haveType : Option String := none
  let mut otherGroups : Array String := #[]
  for g in groups do
    let inner := collapseToOneLine ((g.drop 1).dropRight 1)
    let namesPart : String := match inner.splitOn " : " with
      | np :: _ => np
      | _ => inner
    let names := namesPart.trim.splitOn " " |>.filter (·.length > 0)
    if names.contains haveName then
      haveType := match inner.splitOn " : " with
        | _ :: rest => some (" : ".intercalate rest).trim
        | _ => none
    else
      otherGroups := otherGroups.push g
  match haveType with
  | none => return none
  | some ty =>
    let callArgNames : List String := otherGroups.toList.foldl (fun acc g =>
        if !g.startsWith "(" then acc
        else
          let inner := collapseToOneLine ((g.drop 1).dropRight 1)
          let namesPart := match inner.splitOn " : " with
            | first :: (_ :: _) => first
            | _ => inner
          acc ++ (namesPart.trim.splitOn " " |>.filter (·.length > 0))) []
    let paramsText := otherGroups.toList.foldl (fun acc g => acc ++ " " ++ g) ""
    return some (ty, callArgNames, paramsText)

/-- Scan `lines[0 until_)` for the LAST one-liner `have NAME : TYPE := ...`
    (the replacement this same extractor inserts after extracting a have) and
    return its TYPE text verbatim. That one-liner's type was built from
    `collapseToOneLine effectiveType` — the have's own source-level type,
    always correctly ascribed — so when a LATER have's probe reverts `NAME`
    as a context hypothesis, substituting this text back in place of the
    captured (possibly ascription-dropped) parameter type fixes the same
    "typeclass instance problem is stuck" failure the return-type fix handles,
    but for a parameter instead of the return type. -/
private def findPriorOneLinerType (lines : Array String) (from_ until_ : Nat) (name : String) : Option String :=
  Id.run do
    let needle := "have " ++ name ++ " : "
    let mut result := none
    -- Scan ONLY the current theorem's body (`from_` = span.bodyStart), never
    -- the whole file: have names REPEAT across theorems (`hbound`/`hstep`/
    -- `hsq` appear in five different Hedge.lean theorems), and a same-named
    -- one-liner from an EARLIER theorem carries types mentioning THAT
    -- theorem's variables — substituting one in produced an assembled lemma
    -- referencing an unbound `t.val` (observed on `hη_ne`).
    let mut i := from_
    while i < until_ do
      let t := lines[i]!.trimLeft
      if t.startsWith needle then
        let rest := t.drop needle.length
        result := some (match rest.splitOn " := " with
          | ty :: _ => ty.trim
          | [] => rest.trim)
      i := i + 1
    return result

/-- Same `open`/namespace-scoping computation as `neededOpens`, but from a raw
    line index (`bStart`) rather than a `ThmSpan` — used by the FINAL
    post-processing pass, which works from `findAllDeclSpans` (plain index
    pairs) rather than `findTheorems`'s richer span records. Tracks the
    enclosing `namespace ... / end ...` nesting directly (a stack) instead of
    `ThmSpan.fullName`, since no such field exists here. -/
private def enclosingOpensFor (lines : Array String) (bStart : Nat) : List String := Id.run do
  let mlines := maskCommentLines lines
  let declKws : List String := ["theorem ", "lemma ", "def ", "abbrev ", "instance ",
    "example ", "private ", "noncomputable ", "structure ", "inductive ", "have ", "@["]
  let mut nsStack : List String := []
  let mut opens : List String := []
  -- `open X in` scopes exactly the NEXT command, not everything below it —
  -- ingesting it as an ambient open used to append BOTH `X` and the literal
  -- token `in` to the names list, emitting `open ... X in in` (parse error
  -- at the second `in` — the Entropy.lean ladder wipeout). Track it as
  -- PENDING instead: consumed by the next decl-start line; whichever decl
  -- consumed it LAST before `bStart` is the target itself (a body's `bStart`
  -- belongs to the most recent header), so its names DO apply — as do any
  -- still-unconsumed pendings when `bStart` is the header line itself.
  let mut pendingInOpen : List String := []
  let mut lastDeclPending : List String := []
  for i in List.range bStart do
    let t := mlines[i]!.trim
    if t.startsWith "namespace " then
      nsStack := nsStack ++ [(t.drop "namespace ".length).trim]
    else if t.startsWith "end " then
      let nm := (t.drop "end ".length).trim
      if nsStack.getLast? == some nm then
        nsStack := nsStack.dropLast
    else if t.startsWith "open " then
      -- drop the literal `scoped` keyword: `open scoped BigOperators` would
      -- otherwise contribute "scoped" as a NAMESPACE NAME to the merged
      -- probe prefix (`open ... scoped BigOperators ... in` — resolution
      -- garbage, a 0/85 wipeout on SmolenskyAlgebra.lean); a PLAIN open of
      -- the namespace is a strict superset (names + scoped notation), so
      -- probes stay faithful
      let names := (t.drop "open ".length).trim.splitOn " "
        |>.filter (fun s => s.length > 0 && s != "scoped")
      if names.getLast? == some "in" then
        pendingInOpen := pendingInOpen ++ names.dropLast
      else
        opens := opens ++ names
    else if declKws.any t.startsWith then
      lastDeclPending := pendingInOpen
      pendingInOpen := []
  -- Open EVERY cumulative prefix of the namespace path, not just the full
  -- path: inside `namespace A.B.C`, a reference to a SIBLING name (`Protocol`
  -- = A.B.Protocol from within `namespace A.B.Protocol`, Subprotocol.lean)
  -- resolves via the enclosing-prefix walk — which `open A.B.C in` does NOT
  -- replicate (it only exposes members OF A.B.C). Opening A, A.B, and A.B.C
  -- together reproduces in-namespace resolution for probes. Entries may
  -- themselves be dotted (`namespace Deterministic.Protocol`), so flatten
  -- components first. Never bit before because every prior campaign file
  -- used a single-level namespace, where full path = only prefix.
  let nsComponents := nsStack.foldl (fun acc s => acc ++ (s.splitOn ".")) ([] : List String)
  let nsPrefixes := (List.range nsComponents.length).map (fun i =>
    ".".intercalate (nsComponents.take (i+1)))
  return nsPrefixes ++ opens ++ lastDeclPending ++ pendingInOpen

/-- The enclosing namespace path ("A.B.C", or "" at top level) for the line at
    `bStart`. OPEN-COLLISION class (#58, Derandomization): emulating namespace
    nesting with `open A A.B A.B.C in` puts the enclosing namespaces at the
    SAME priority as the file's explicit `open`s — `Protocol` became ambiguous
    (`FiniteMessage.Protocol` vs `PublicCoin.Protocol`) in probes while the
    real in-file decl resolves it via nesting PRIORITY. Lean gives the body of
    a DOTTED-NAME declaration (`lemma A.B.C.probe : ...`) true
    current-namespace resolution priority — so probe headers qualify their
    throwaway names with this path, which beats the flattened opens exactly
    like real nesting does. -/
private def enclosingNamespacePathFor (lines : Array String) (bStart : Nat) : String := Id.run do
  let mlines := maskCommentLines lines
  let mut nsStack : List String := []
  for i in List.range bStart do
    let t := mlines[i]!.trim
    if t.startsWith "namespace " then
      nsStack := nsStack ++ [(t.drop "namespace ".length).trim]
    else if t.startsWith "end " then
      if nsStack.getLast? == some ((t.drop "end ".length).trim) then
        nsStack := nsStack.dropLast
  return ".".intercalate (nsStack.foldl (fun acc s => acc ++ (s.splitOn ".")) [])

/-- DECL-SCOPED opens (`open Classical in` on the line(s) before the decl at
    `bStart`) — the CLASSICAL-INSTANCE-LOSS class (Derandomization, 16 errors
    twice): probes carry these via `enclosingOpensFor`'s pending tracking, so
    they pass, but written aux lemmas are SPLICED ABOVE the `open ... in`
    line, outside its single-command scope — Decidable instances that the
    decl gets from `open Classical in` fail to synthesize in the written
    file (error-recovery renders the failed subterms as `sorry`, which
    misled the first diagnosis). Bake these into the WRITTEN lemma text,
    like `classicalPrefix` (#36: check-context = write-context). -/
private def declScopedOpensFor (lines : Array String) (bStart : Nat) : List String := Id.run do
  let mlines := maskCommentLines lines
  let declKws : List String := ["theorem ", "lemma ", "def ", "abbrev ", "instance ",
    "example ", "private ", "noncomputable ", "structure ", "inductive ", "have ", "@["]
  let mut pendingInOpen : List String := []
  let mut lastDeclPending : List String := []
  for i in List.range bStart do
    let t := mlines[i]!.trim
    if t.startsWith "open " then
      let names := (t.drop "open ".length).trim.splitOn " "
        |>.filter (fun s => s.length > 0 && s != "scoped")
      if names.getLast? == some "in" then
        pendingInOpen := pendingInOpen ++ names.dropLast
    else if declKws.any t.startsWith then
      lastDeclPending := pendingInOpen
      pendingInOpen := []
  return (lastDeclPending ++ pendingInOpen).eraseDups

/-- Top-level `set_option NAME VALUE` lines appearing before `bStart` in the
    file being assembled. The verification probes below elaborate a candidate
    declaration in the DRIVER file's option context — but the SOURCE file's
    proofs may only elaborate under the source's own header options.
    `LowDegree.lean`'s header sets `maxHeartbeats 0` / `maxRecDepth 10000`,
    and its heavy `simp_all +decide` proofs exceed the DEFAULT heartbeat
    budget — so a probe run without these deterministically times out and a
    perfectly valid candidate transformation gets rejected as an "error".
    Confirmed empirically, not hypothetical: `h_second_deriv_zero`'s have→let
    conversion verified clean when hand-edited into the real file (which has
    the header), yet the automated pass — probing without the header — had
    rejected that exact transformation. Same class of environment-mismatch bug
    as `elabCheckOk`'s forced `autoImplicit false` (see its docstring): a
    verification probe is only as sound as its faithfulness to the context
    the real file elaborates in. -/
private def enclosingSetOptionsFor (lines : Array String) (bStart : Nat) : List (String × String) :=
  Id.run do
    let mlines := maskCommentLines lines
    let mut result : List (String × String) := []
    for i in List.range bStart do
      let t := mlines[i]!.trim
      if t.startsWith "set_option " then
        match (t.drop "set_option ".length).trim.splitOn " " |>.filter (·.length > 0) with
        | nm :: v :: _ => result := result ++ [(nm, v)]
        | _ => pure ()
    -- DEDUPE exact (name, value) repeats, keeping the LAST occurrence (so an
    -- intervening different-value override of the same option still wins per
    -- innermost-`in` semantics). Without this, the scanner re-collects the
    -- `set_option ... in` prefix lines of every previously WRITTEN aux lemma
    -- as ambient context, so each new lemma's prefix gains one more copy per
    -- prior lemma — quadratic text growth on files with header-wide options
    -- (observed on Entropy.lean: 4× duplicated prefixes by the fourth decl).
    let mut seen : List (String × String) := []
    let mut dedup : List (String × String) := []
    for p in result.reverse do
      if !seen.contains p then
        seen := p :: seen
        dedup := p :: dedup
    -- CLAMP an unbounded `maxHeartbeats 0` to a large finite budget. This is
    -- the #40 cost-structure lesson applied at the source: one heartbeats-0
    -- probe on a heavy measure-theory candidate can spin for HOURS (observed:
    -- Entropy's boolVector.hsplit pinned a core for 2h with no verdict),
    -- wedging the whole campaign. Because this function feeds probes, commit
    -- gates, AND the written lemma prefixes alike, the clamp preserves
    -- check-context = write-context exactly; and it is safe-direction — a
    -- candidate that passes at the clamped budget passes a fortiori under the
    -- real file's unbounded header, while a slow-but-valid conversion is
    -- merely LOST (rejected), never shipped broken. Bounded values (400000,
    -- 1000000, ...) pass through untouched.
    return dedup.map (fun (nm, v) =>
      if nm == "maxHeartbeats" && v == "0" then (nm, "2000000") else (nm, v))

/-- The `variable ...` commands in scope at line `bStart` — a third kind of
    ambient context the verification probes must replay, alongside `open`s
    (`enclosingOpensFor`) and `set_option`s (`enclosingSetOptionsFor`): a
    declaration like `lemma foo {f : hypercube n → Bool} ...` may use `n`
    WITHOUT binding it because a `variable {n : ℕ}` command earlier in the
    file binds it ambiently — re-elaborating the declaration without that
    context fails with "Unknown identifier `n`" (a probe artifact, not a
    verdict; hit 4 of the 7 blocked haves on `LowDegree.lean`). Scope-aware:
    `variable`s declared inside a `section`/`namespace` die at its `end`, so
    track a scope stack and only keep the ones still active at `bStart`. -/
private def enclosingVariablesFor (lines : Array String) (bStart : Nat) : List String := Id.run do
  let mlines := maskCommentLines lines
  let mut stack : List (List String) := [[]]
  let mut i := 0
  while i < bStart do
    let t := mlines[i]!.trim
    if t.startsWith "section" || t.startsWith "namespace " then
      stack := [] :: stack
    else if t == "end" || t.startsWith "end " then
      match stack with
      | _ :: rest@(_ :: _) => stack := rest
      | _ => pure ()
    else if t.startsWith "variable " then
      -- A `variable` command can SPAN MULTIPLE physical lines (continuation
      -- lines are indented) — `Entropy.lean`'s second one runs four lines,
      -- and collecting only the first truncated `{X : Ω → S} {Y : Ω → T} ...`
      -- out of existence ("Unknown identifier `X`" across every probe for
      -- the rest of the file). Consume indented continuations, joined flat.
      let mut cmd := t
      while i + 1 < bStart && !mlines[i+1]!.trim.isEmpty &&
            mlines[i+1]!.startsWith " " do
        i := i + 1
        cmd := cmd ++ " " ++ mlines[i]!.trim
      match stack with
      | top :: rest => stack := (top ++ [cmd]) :: rest
      | [] => stack := [[cmd]]
    i := i + 1
  return stack.reverse.foldl (· ++ ·) []

/-- The line at which to SPLICE an aux lemma above a declaration header. Naive
    insertion at `headerStart` lands BETWEEN the declaration's doc comment (or
    `@[...]` attributes / `set_option ... in` prefix lines) and the declaration
    itself — and a doc comment must be immediately followed by a declaration,
    so the WRITTEN file breaks with "unexpected token 'set_option'; expected
    'lemma'" while every probe gate stays green (probes never include the
    docstring — the check-context ≠ write-context class yet again; observed
    as 6 shipped parse errors on Entropy.lean). Back up over any contiguous
    attached block: in-scoped prefix lines, attribute lines, and a doc comment
    block (a comment-closing line directly above, with its doc-comment opener
    found within a bounded upward scan). -/
private def spliceLineAbove (lines : Array String) (headerStart : Nat) : Nat := Id.run do
  let mut i := headerStart
  let mut changed := true
  while changed do
    changed := false
    while i > 0 &&
        (let t := lines[i-1]!.trim
         t.startsWith "@[" ||
         (t.endsWith " in" &&
          (t.startsWith "set_option " || t.startsWith "open " || t.startsWith "omit "))) do
      i := i - 1
      changed := true
    if i > 0 && lines[i-1]!.trim.endsWith "-/" then
      let mut j := i - 1
      let mut found := false
      let mut fuel := 60
      while fuel > 0 && !found do
        fuel := fuel - 1
        let t := lines[j]!.trimLeft
        if t.startsWith "/--" || t.startsWith "/-!" then
          found := true
        else if j == 0 then
          fuel := 0
        else
          j := j - 1
      if found then
        i := j
        changed := true
  return i

/-- Process ONE leaf `have` (absolute line `haveIdx`, name `haveName`) belonging
    to theorem `span`: build a synthetic probe theorem (original signature,
    renamed, plus the literal tactic prefix up to this `have`, plus the have's
    own header with `extract_goal` as its body), elaborate it, and use the
    captured signature to emit a `private lemma` (with the ORIGINAL proof body)
    plus a one-liner call replacing the `have`. Returns `none` (leaving the
    have untouched) if the probe's message couldn't be found/parsed. -/
private def extractOneHaveViaGoal
    (lines : Array String) (span : ThmSpan) (haveIdx : Nat) (haveName : String)
    (counter : Nat) : CommandElabM (Option (Array String)) := do
  let (proofBody, relEnd) := extractHaveBody lines haveIdx
  let haveLineText := lines[haveIdx]!
  let isBulletAttached := haveLineText.trimLeft.startsWith "· "
  let bulletIndentStr := String.mk (List.replicate (lineIndent haveLineText) ' ')
  let haveBlockText := "\n".intercalate (lines.extract haveIdx relEnd).toList
  -- Top-level split, NOT `splitOn ":="`: a `:=` can sit INSIDE the have's type
  -- (named arguments like `(α := Fin T)`) — see `splitAtTopLevelAssign`.
  let topSplit := splitAtTopLevelAssign haveBlockText
  let isTacticHave := match topSplit with
    | some (_, body) =>
      let b := body.trimLeft
      b == "by" || b.startsWith "by " || b.startsWith "by\n"
    | none => false
  let headerBeforeAssign := match topSplit with
    | some (h, _) => h.trimRight
    | none        => haveLineText.trimRight
  -- The have's OWN declared type, verbatim from source (e.g. "have step2 :
  -- ∀ (c : Nat), a + c = b + c" → "∀ (c : Nat), a + c = b + c"), empty when the
  -- source have has no explicit annotation (`have h := term`).
  -- COLLAPSE the header before the name/type split: a multi-line header
  -- (`have hnorm :` with the type on following lines) has its colon at
  -- end-of-LINE — colon-newline, not colon-space — so `splitOn " : "` on the
  -- raw text instead matches the first BINDER's colon inside the type
  -- (`∀ x : ZkVec p n, ...`), beheading the `∀` and shipping a mangled
  -- return type (`: ZkVec p n, ...` — "expected ':='" parse failures on
  -- ZkBLR's hpoint/hnorm). Collapsing turns colon-newline into colon-space
  -- first, so the have-name separator matches as intended.
  let originalTypeText : String :=
    match (collapseToOneLine headerBeforeAssign).splitOn " : " with
    | _ :: rest => (" : ".intercalate rest).trim
    | []        => ""
  -- A term-mode have can carry SAME-LINE continuation tactics after an outer
  -- semicolon (e.g. "have h := term; rw [sq] at h; exact h") — the have block's
  -- span is just that one line, so replacing it with a one-liner call would
  -- silently DROP those tactics entirely unless preserved as a separate line.
  let termContinuation : String :=
    if isTacticHave then ""
    else
      match splitAtTopLevelAssign haveLineText.trimLeft with
      | some (_, body) =>
        match splitAtOuterSemi body.trimLeft with
        | some (_, cont) => cont.trim
        | none => ""
      | none => ""
  -- dotted probe name = true current-namespace resolution priority
  -- (see enclosingNamespacePathFor — the open-collision class)
  let nsPath := enclosingNamespacePathFor lines span.headerStart
  let tempThmName := (if nsPath.isEmpty then "" else nsPath ++ ".") ++ s!"__extract_probe_{counter}__"
  let headerText := "\n".intercalate (lines.extract span.headerStart span.bodyStart).toList
  -- A `private `-headed declaration MUST have the modifier stripped before the
  -- keyword/name arithmetic: the old `kw := ... else "lemma "` default made
  -- `afterKw.drop span.name.length` drop from the WRONG offset, shipping
  -- mangled probe headers like `lemma __extract_probe_1__lesToAux` — a
  -- whole-decl probe wipeout on privacy-heavy files (Switching.lean, 51
  -- private decls; every prior campaign target happened to be public).
  let headerText :=
    if headerText.startsWith "private " then headerText.drop "private ".length else headerText
  let kw := if headerText.startsWith "theorem " then "theorem " else "lemma "
  let afterKw := headerText.drop kw.length
  let afterName := afterKw.drop span.name.length
  let renamedHeader := kw ++ tempThmName ++ afterName
  let prefixLines := lines.extract span.bodyStart haveIdx
  let prefixText := if prefixLines.isEmpty then "" else ("\n".intercalate prefixLines.toList ++ "\n")
  let contentIndentN := lineIndent haveLineText + (if isBulletAttached then 2 else 0)
  let tacticIndentStr := String.mk (List.replicate (contentIndentN + 2) ' ')
  let siblingIndentStr := String.mk (List.replicate contentIndentN ' ')
  -- The theorem's own base tactic indent (e.g. 2). A single line at this indent,
  -- however deeply we're currently nested inside bullets/case-splits, pops back out
  -- to the theorem's outermost tactic sequence (Lean's indentation-scoped blocks all
  -- close at once when a line's indent is ≤ their reference column) — so `all_goals
  -- sorry` there closes every sibling goal left open by every case-split we replayed
  -- but didn't finish (`rcases`/`by_cases`/etc. share a "motive" metavariable across
  -- branches; leaving siblings entirely unresolved makes `extract_goal` itself fail
  -- with "Extracted goal has metavariables", confirmed empirically in isolation).
  let baseIndentStr := String.mk (List.replicate (lineIndent lines[span.bodyStart]!) ' ')
  -- The probe is a bare top-level command, not textually nested in whatever
  -- `namespace`/`open` context the real theorem sits in — replay it via a single
  -- `open ... in` prefix so unqualified references to the file's OWN definitions
  -- (not from Mathlib) resolve exactly as they do for the real theorem.
  let opens := enclosingOpensFor lines span.headerStart
  let openPrefix := if opens.isEmpty then "" else "open " ++ " ".intercalate opens ++ " in\n"
  -- The FULL ambient context, not just opens: extraction probes on
  -- `Entropy.lean` failed 77/77 with "failed to synthesize MeasurableSpace S"
  -- because the file's section-scoped `variable {Ω S : Type*}
  -- [MeasurableSpace Ω] [MeasurableSpace S]` (and its `set_option`s) were
  -- only ever replayed by the LADDER's probes, never the extraction probes —
  -- LowDegree/BoolFourier masked this by binding everything in-header. Used
  -- for probes, dependency-copy persists, commit gates, and assembled-lemma
  -- persists alike (unused section variables cost only a linter warning).
  let setOptPrefix :=
    (enclosingSetOptionsFor lines span.headerStart).foldl
      (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") ""
  let ambientPrefix := setOptPrefix ++ openPrefix ++
    (enclosingVariablesFor lines span.headerStart).foldl (fun acc v => acc ++ v ++ " in\n") ""
  -- LEMMA commands must NOT carry the `variable ... in` prefix: the captured
  -- signature binds everything explicitly (universe spec included), and an
  -- ambient `variable {Ω S : Type*}` in the SAME command auto-declares its
  -- own `u_1`-style levels, colliding with the lemma's explicit `.{u_1, ...}`
  -- ("a universe level named `u_5` has already been declared" ×106 on
  -- Entropy.lean). Probes and the rewritten-theorem gate still need it.
  -- A source proof running under the `classical` tactic has
  -- `Classical.propDecidable` installed as a proof-wide LOCAL instance; a
  -- captured type whose `Finset.filter`s relied on it fails to re-elaborate
  -- standalone ("failed to synthesize DecidablePred ...", the
  -- counting_obstruction bottom layer). Elaborate such lemmas under the
  -- scoped classical instances.
  let classicalPrefix :=
    -- decl-scoped `open ... in` names must be BAKED into written lemmas
    -- (splices land above the `open ... in` line — see declScopedOpensFor)
    (let dOpens := declScopedOpensFor lines span.headerStart
     if dOpens.isEmpty then "" else "open " ++ " ".intercalate dOpens ++ " in\n") ++
    (if (maskCommentLines (lines.extract span.bodyStart span.bodyEnd)).toList.any
        (fun l => l.trim == "classical") then
      "open scoped Classical in\n"
    else "")
  let lemmaPrefix := setOptPrefix ++ openPrefix ++ classicalPrefix
  let externalName := span.name ++ "_aux_" ++ haveName
  if originalTypeText.isEmpty then
    -- Anonymous/untyped have: `extract_goal` can't be handed the have's own type
    -- (there isn't one in the source) without discarding the ORIGINAL VALUE, which
    -- is the only thing that determines it — so instead, KEEP the have exactly as
    -- written, then `revert` it right after (before any continuation tactics run,
    -- so the goal is still whatever it was right after introducing it) and read
    -- its type off the captured (prenexed) signature.
    let keptHaveText :=
      if isTacticHave then
        let proofLines := proofBody.splitOn "\n" |>.map (fun l => tacticIndentStr ++ l)
        headerBeforeAssign ++ " := by\n" ++ "\n".intercalate proofLines
      else
        headerBeforeAssign ++ " := " ++ proofBody
    -- RENDERING-FALLBACK LADDER: the captured type is `ppExpr` output, which
    -- is NOT guaranteed to re-parse to the same term in file context —
    -- observed for real: `Bool.xor` rendered as `^^` misresolved on
    -- re-elaboration ("failed to synthesize CartesianMonoidalCategory Bool"),
    -- so the assembled lemma failed bug #11's round-trip gate. Rather than
    -- giving up on the first rendering, retry the WHOLE capture with pretty-
    -- printer options that trade notation for round-trip fidelity
    -- (`pp.fullNames` + `pp.notation false`: prefix applications with
    -- unambiguous names — verbose, but valid input syntax). Each rendering's
    -- assembled lemma still faces the same empirical gate; first to pass wins.
    -- `set`-bound ldecls in the replayed prefix defeat the capture (see
    -- `setBoundNamesInPrefix`) — an outer clear_value dimension retries every
    -- rendering with the ldecls' values stripped. Tried SECOND: when no ldecl
    -- actually interferes (cleanup pruned it), the plain probe is both cheaper
    -- and faithful to the original context.
    let clearNames := setBoundNamesInPrefix prefixText contentIndentN
    -- Rung 3 (unfold + clear): a proof can rely on the ldecl's TRANSPARENCY
    -- (`log_pos hN_pos : 0 < log ↑N` closing goal `0 < a`), which clear_value
    -- alone destroys. Unfolding the definitions in the have's own type FIRST
    -- (`simp only [x]` zeta-delta-unfolds a let-fvar) makes the captured type
    -- definition-free, so the lemma never mentions the ldecl — and the real
    -- callsite accepts the unfolded type by defeq, since `x` IS transparent
    -- there. `try` because the have's type may not mention any set-var.
    let cvVariants : List String :=
      if clearNames.isEmpty then [""]
      else
        -- Per-name `try` lines, NOT one atomic call: a collected name can be
        -- a term-mode `let` or otherwise not an ldecl at the probe point, and
        -- an atomic `clear_value a b c` then fails wholesale ("Variable `F`
        -- is not a proposition or let-declaration", 25× on Entropy.lean) —
        -- per-name `try` degrades bad names to no-ops instead.
        let cvLine := clearNames.foldl
          (fun acc n => acc ++ siblingIndentStr ++ "try clear_value " ++ n ++ "\n") ""
        let unfoldLine := clearNames.foldl
          (fun acc n => acc ++ siblingIndentStr ++ "try simp only [" ++ n ++ "] at " ++ haveName ++ "\n") ""
        ["", cvLine, unfoldLine ++ cvLine]
    for cvLine in cvVariants do
     for renderPrefix in ["",
        "set_option pp.funBinderTypes true in\n",
        "set_option pp.fullNames true in\nset_option pp.notation false in\nset_option pp.funBinderTypes true in\n"] do
      let revertSynthetic :=
        renderPrefix ++
        ambientPrefix ++
        renamedHeader ++ "\n" ++ prefixText ++
        keptHaveText ++ "\n" ++
        cvLine ++
        siblingIndentStr ++ "revert " ++ haveName ++ "\n" ++
        siblingIndentStr ++ "extract_goal using __sig__\n" ++
        siblingIndentStr ++ "sorry\n" ++
        baseIndentStr ++ "all_goals sorry\n"
      let msgs ← captureWithDependencyRetry lines ambientPrefix revertSynthetic
      match findExtractedSignature msgs with
      | none =>
        -- The rejection-reasons rule: an unexplained PROBE_FAILED is
        -- indistinguishable from "genuinely unextractable" (the inert-verifier
        -- lesson) — surface the probe's actual first error.
        match msgs.find? (fun m => (m.splitOn "error").length ≥ 2) with
        | some e => plogInfo s!"[extract-probe] '{haveName}' capture failed: {e.take 300}"
        | none => plogInfo s!"[extract-probe] '{haveName}' capture failed with no error message ({msgs.size} msgs)"
      | some capturedSigText0 =>
        let capturedSigText := capturedSigText0.replace "ℕ" "Nat"
        -- DAGGERED SIG PARAMS (#57): `extract_goal` prints INACCESSIBLE
        -- context hyps as literal `{m✝ : Nat} (gates✝ : ...)` groups — `✝`
        -- is not valid syntax, so every variant died at PARSE ("expected
        -- token" exactly at the dagger; CircuitTreeManip h_elem_le_foldr).
        -- Binder names of a standalone lemma are arbitrary: rename them to
        -- fresh accessible names (longest marker first so `✝¹` never leaves
        -- a stray `¹`). The source-replayed proof body cannot reference
        -- them (they were inaccessible), and the CALLSITE side is covered
        -- by the inacc-args retry (type-directed `apply <;> assumption`).
        let capturedSigText := (((((capturedSigText.replace "✝⁴" "_inacc4").replace
          "✝³" "_inacc3").replace "✝²" "_inacc2").replace "✝¹" "_inacc1").replace "✝" "_inacc")
        -- extract_goal renders universe-polymorphic captures with a UNIVERSE
        -- SPEC after the name (`__sig__.{u_2, u_1} ...`) — the group parsers
        -- would read `{u_2, u_1}` as a (comma-broken) binder group, failing
        -- every capture in a `Type*`-variable file (Entropy.lean: 0/77).
        -- Split it off and re-attach it to the extracted lemma's NAME
        -- (`private lemma foo.{u_2, u_1} ...` is valid syntax); callsites
        -- need no change (universes are inferred), but the DECLARATION must
        -- bind them: the output file sets `autoImplicit false`, which
        -- disables universe auto-binding too.
        let (univSpec, capturedSigText) :=
          if capturedSigText.startsWith "__sig__.{" then
            let afterName := capturedSigText.drop "__sig__".length
            match afterName.splitOn "}" with
            | spec :: rest => (spec ++ "}", "__sig__" ++ "}".intercalate rest)
            | [] => ("", capturedSigText)
          else ("", capturedSigText)
        -- Collision-proof universe names for the WRITTEN lemma: it lands
        -- inside the file's `variable {.. : Type*}` scope, whose auto-named
        -- `u_k` levels collide with an explicit `.{u_k, ...}` spec
        -- ("universe level already declared" — 15 output errors on
        -- Entropy.lean, cascading into "Unknown identifier" at every
        -- callsite; the lemma-check probe couldn't see it because it
        -- deliberately omits the `variable` prefix). Longest names first so
        -- `u_1` never clobbers `u_10`'s text. `scrubUnivs` handles the
        -- CALLSITE ascription instead: `Type u_k` from one capture can be
        -- unknown in another context ("unknown universe level `u_6`") — an
        -- inferred `Type _` is always right there, since the call's result
        -- type determines it.
        let univNames := (if univSpec.isEmpty then [] else
            ((univSpec.drop 2).dropRight 1).splitOn "," |>.map String.trim)
          |>.filter (·.length > 0)
        let univNamesSorted := univNames.toArray.qsort (fun a b => a.length > b.length) |>.toList
        let renameUnivs (s : String) : String :=
          univNamesSorted.foldl (fun acc n => acc.replace n ("ul" ++ n.drop 1)) s
        let scrubUnivs (s : String) : String :=
          univNamesSorted.foldl (fun acc n =>
            (acc.replace ("Type " ++ n) "Type _").replace ("Sort " ++ n) "Sort _") s
        match parseRevertedSignature capturedSigText haveName with
        | none => plogInfo s!"[extract-probe] '{haveName}' captured sig unparseable: {capturedSigText.take 500}"
        | some (ty, callArgNames, paramsText0) =>
          -- Bug #24's parameter-ascription fix, PORTED to this branch: a
          -- reverted-context parameter (e.g. an earlier have, now a one-liner
          -- in scope) can lose binder ascriptions in the ppExpr capture,
          -- leaving the assembled lemma with stuck typeclass metavariables
          -- ("typeclass instance problem is stuck") no rendering option cures
          -- reliably. The correctly-ascribed type is the one-liner this same
          -- extractor already inserted — substitute it back per-group, unless
          -- the captured type is LONGER (= legitimately mutated in place by an
          -- intervening tactic; see the typed branch's note).
          let (pGroups, _) := scanBinderGroups paramsText0
          -- forward-reference guard — see the typed branch
          let ownBinderNames : List String := pGroups.toList.foldl (fun acc g =>
            if !g.startsWith "(" then acc else
            let inner := collapseToOneLine ((g.drop 1).dropRight 1)
            match inner.splitOn " : " with
            | nm :: _ :: _ => acc ++ (nm.trim.splitOn " " |>.filter (·.length > 0))
            | _ => acc) []
          let paramsText := pGroups.foldl (init := "") fun acc g =>
            let fixed :=
              if !g.startsWith "(" then g
              else
                let inner := collapseToOneLine ((g.drop 1).dropRight 1)
                match inner.splitOn " : " with
                | name :: rest =>
                  let capturedTy := " : ".intercalate rest
                  match findPriorOneLinerType lines span.bodyStart haveIdx name.trim with
                  | some fixedTy =>
                    let introducesForwardRef := ownBinderNames.any (fun nm =>
                      nm != name.trim && containsWord fixedTy nm && !containsWord capturedTy nm)
                    if fixedTy.length > capturedTy.length && !introducesForwardRef then
                      "(" ++ name.trim ++ " : " ++ fixedTy ++ ")"
                    else g
                  | none => g
                | _ => g
            acc ++ " " ++ fixed
          let finalSigLine := externalName ++ univSpec ++ paramsText ++ " : " ++ ty
          -- SHIPPED-ERROR GATES (#51) — see the typed branch: sorry/match-aux
          -- in a captured sig is probe-green but write-broken.
          if containsWord finalSigLine "sorry" || (finalSigLine.splitOn ".match_").length ≥ 2 ||
             (finalSigLine.splitOn "._simp_").length ≥ 2 || (finalSigLine.splitOn "._proof_").length ≥ 2 || (finalSigLine.splitOn "._eq_").length ≥ 2 then
            plogInfo s!"[extract-probe] '{haveName}' variant rejected: captured sig carries sorry/match-aux"
          -- SELF-RECURSION GATE (#56): a have inside a `termination_by`
          -- decl whose proof CALLS THE DECL ITSELF (buildFullDTree_depth's
          -- h1/h2) cannot be extracted — the aux lemma is spliced ABOVE the
          -- decl, a forward reference. The gate can't see it: in the probe
          -- env the module is IMPORTED, so the self-call resolves against
          -- the imported copy (probe-green/write-broken, recursion edition).
          else if containsWord proofBody span.name || containsWord finalSigLine span.name then
            plogInfo s!"[extract-probe] '{haveName}' variant rejected: self-recursive (references enclosing decl '{span.name}')"
          else
          let lemmaText := renameUnivs <|
            if isTacticHave then
              let proofLines := proofBody.splitOn "\n" |>.map (fun l => "  " ++ l)
              "private lemma " ++ finalSigLine ++ " := by\n" ++ "\n".intercalate proofLines
            else
              "private lemma " ++ finalSigLine ++ " :=\n  " ++ proofBody
          let call := if callArgNames.isEmpty then externalName
                      else "(" ++ externalName ++ " " ++ " ".intercalate callArgNames ++ ")"
          let oneLinerIndent := bulletIndentStr ++ (if isBulletAttached then "  " else "")
          let oneLiner := oneLinerIndent ++ "have " ++ haveName ++ " : " ++ scrubUnivs (collapseToOneLine ty) ++ " := " ++ call
          let replacementLines : Array String :=
            (if isBulletAttached then #[bulletIndentStr ++ "·"] else #[]) ++
            (if termContinuation.isEmpty then #[oneLiner] else #[oneLiner, oneLinerIndent ++ termContinuation])
          let newLines := lines.extract 0 haveIdx ++ replacementLines ++ lines.extract relEnd lines.size
          -- `lemmaText` contains embedded "\n"s (it's a whole multi-line declaration) —
          -- MUST be split into one array element per physical line before insertion, or
          -- every later line-based scan over `lines` (`findAllDeclSpans`, `blockEnd`,
          -- `findAllHaveHeaders`, ...) treats this whole declaration as a single
          -- (degenerate, 1-line) array slot, silently never looking inside it again.
          let lemmaLines := (lemmaText.splitOn "\n").toArray
          let insAt := spliceLineAbove newLines span.headerStart
          let finalLines := newLines.extract 0 insAt ++ lemmaLines ++ #[""] ++
                             newLines.extract insAt newLines.size
          -- Bug #11's lesson, ENFORCED at the source and extended to the
          -- DECLARATION level: verify the assembled lemma AND the rewritten
          -- theorem together (the callsite one-liner can break downstream
          -- syntactic consumers — see `elabCheckFirstErrorSeq`). On failure,
          -- fall through to the next rendering (or exhaust and reject to the
          -- graceful PROBE_FAILED path) — logging the real reason either way.
          let newBodyEnd := span.bodyEnd - (relEnd - haveIdx) + replacementLines.size
          let gateDecl := ambientPrefix ++ renamedHeader ++ "\n" ++
            "\n".intercalate (newLines.extract span.bodyStart newBodyEnd).toList
          match ← elabCheckFirstErrorSeq [lemmaPrefix ++ lemmaText, gateDecl] with
          | none =>
            -- Persist the REAL lemma, not a `:= sorry` stub: later probes for
            -- sibling haves in this theorem then elaborate against the actual
            -- proof, closing the stub-vs-real behavioral gap in probe
            -- verdicts. Safe now that the text is verified; a persist failure
            -- still degrades gracefully to error-recovery's sorryAx-backed
            -- declaration (= the old stub).
            elabPersistCommand (lemmaPrefix ++ lemmaText)
            return some finalLines
          | some err =>
            plogInfo s!"[extract-probe] '{haveName}' assembled lemma rejected: {err.take 300}"
            if err.startsWith "PARSE" || (err.splitOn "unknownIdentifier").length ≥ 2 then
              plogInfo s!"[extract-probe] '{haveName}' lemma text: {(collapseToOneLine lemmaText).take 2500}"
              plogInfo s!"[extract-probe] '{haveName}' decl text: {(collapseToOneLine gateDecl).take 2500}"
            -- INACC-ARGS retry (untyped-have twin of the typed branch's):
            -- `extract_goal` prints inaccessible split/cases-arm hypotheses
            -- (`t✝`, `heq✝` under a `next fl fls _ =>` arm) with clean
            -- accessible-LOOKING names — the assembled lemma binds them
            -- fine, but the positional callsite passes identifiers that do
            -- not exist in the tactic context ("Unknown identifier `t`",
            -- EncodingProperties 0/3). Fire only when the unknown name is
            -- one WE passed; retry the SAME lemma with the type-directed
            -- callsite (`apply` unifies data args from the stated type,
            -- `assumption` matches hypothesis args by type — inaccessible
            -- hyps included).
            let unkName := match err.splitOn "identifier `" with
              | _ :: rest :: _ => (rest.splitOn "`").headD ""
              | _ => ""
            if !unkName.isEmpty && callArgNames.contains unkName then
              let call2 := "by apply " ++ externalName ++ " <;> assumption"
              let oneLiner2 := oneLinerIndent ++ "have " ++ haveName ++ " : " ++ scrubUnivs (collapseToOneLine ty) ++ " := " ++ call2
              let replacement2 : Array String :=
                (if isBulletAttached then #[bulletIndentStr ++ "·"] else #[]) ++
                (if termContinuation.isEmpty then #[oneLiner2] else #[oneLiner2, oneLinerIndent ++ termContinuation])
              let newLines2 := lines.extract 0 haveIdx ++ replacement2 ++ lines.extract relEnd lines.size
              let insAt2 := spliceLineAbove newLines2 span.headerStart
              let finalLines2 := newLines2.extract 0 insAt2 ++ lemmaLines ++ #[""] ++
                                 newLines2.extract insAt2 newLines2.size
              let newBodyEnd2 := span.bodyEnd - (relEnd - haveIdx) + replacement2.size
              let gateDecl2 := ambientPrefix ++ renamedHeader ++ "\n" ++
                "\n".intercalate ((newLines2.extract span.bodyStart newBodyEnd2).toList)
              match ← elabCheckFirstErrorSeq [lemmaPrefix ++ lemmaText, gateDecl2] with
              | none =>
                elabPersistCommand (lemmaPrefix ++ lemmaText)
                plogInfo s!"[extract-probe] '{haveName}' INACC-ARGS retry committed (type-directed callsite)"
                return some finalLines2
              | some err2 =>
                plogInfo s!"[extract-probe] '{haveName}' inacc-args retry rejected: {err2.take 240}"
    return none
  else
    -- `set`-bound ldecls in the replayed prefix defeat the capture (see
    -- `setBoundNamesInPrefix`): the ldecl either renders as a `let x := ...;`
    -- inside the captured signature or is referenced-but-unbound in the
    -- assembled lemma ("Unknown identifier `x`"). Retry the capture with
    -- `clear_value` stripping the ldecls' values; plain probe tried first.
    let clearNames := setBoundNamesInPrefix prefixText contentIndentN
    -- Rung 3 (unfold + clear): see the anonymous branch — the proof can rely
    -- on the ldecl's TRANSPARENCY, which clear_value alone destroys; unfold
    -- the definitions in the have's own goal first. When THIS rung wins, the
    -- source-level type text is stale (it still says `a`), so the captured
    -- return type must be preferred (tracked via `wonUnfold`).
    let unfoldMarker := tacticIndentStr ++ "try simp only ["
    -- Per-name `try` lines (see the anonymous branch): atomic calls fail
    -- wholesale on any non-ldecl name; `wonUnfold`'s startsWith check
    -- still holds — the unfold variant begins with `unfoldMarker`.
    -- (Hoisted out of the if so the REVERT grid below can reuse them.)
    let cvClearLine := clearNames.foldl
      (fun acc n => acc ++ tacticIndentStr ++ "try clear_value " ++ n ++ "\n") ""
    let cvUnfoldLine := clearNames.foldl
      (fun acc n => acc ++ unfoldMarker ++ n ++ "]\n") ""
    let cvVariants : List String :=
      if clearNames.isEmpty then [""]
      else ["", cvClearLine, cvUnfoldLine ++ cvClearLine]
    -- REVERT-PRIORS variant: `extract_goal`'s cleanup keeps only hypotheses
    -- the GOAL type depends on — but this have's PROOF may use sibling haves
    -- its type never mentions, so the assembled lemma references them
    -- unbound ("Unknown identifier `hx1_of_ne_ω`", the dominant class on
    -- SmolenskyAlgebra: 57 rejections). Reverting the proof-referenced
    -- priors in the probe folds their types into the captured signature (as
    -- arrows in the RETURN — extract_goal cannot re-bind a pre-reverted
    -- hypothesis as a named group), and the callsite passes them as extra
    -- arguments; the one-liner keeps the have's ORIGINAL stated type since
    -- the application peels the arrows back off.
    -- IN-SCOPE priors only: `findAllHaveHeaders` lists every have textually
    -- before the target, including ones inside CLOSED bullet branches and
    -- inside earlier haves' own proof blocks — reverting an out-of-scope
    -- name aborts the tactic block and the capture dies ("unsolved goals",
    -- the run-4 no-op). A prior have is still in scope iff no line between
    -- it and the target dedents below its own indent.
    let priorHeaders := (findAllHaveHeaders lines span.bodyStart haveIdx).toList
    let inScopeAt (j : Nat) : Bool := Id.run do
      let jInd := lineIndent lines[j]!
      -- a bullet-attached introduction (`· have hall := ...`) is scoped to
      -- ITS branch: the next SIBLING bullet at EQUAL indent closes it, so
      -- the dedent test must be ≤ there, not <
      let isBullet := lines[j]!.trim.startsWith "·"
      for k in [j+1:haveIdx+1] do
        if !lines[k]!.trim.isEmpty then
          let kInd := lineIndent lines[k]!
          if kInd < jInd || (isBullet && kInd ≤ jInd) then
            return false
      return true
    let priorRefPairs := (priorHeaders.filter (fun (j, nm) =>
      nm != haveName && containsWord proofBody nm && inScopeAt j)).map (fun (j, nm) => (j, nm))
    -- LOCAL binders too: `by_cases hxi : ...`, `intro x y`, `funext i` names
    -- are textually visible in the prefix — when the have's type or proof
    -- references one, revert it like a prior. Data vars come back as NAMED
    -- ∀-groups in the telescope (revert preserves user names); Prop hyps
    -- come back as anonymous arrows, resolved type-directedly at the
    -- callsite (`assumption`) and pp-directedly in the lemma's intro line.
    let refText := proofBody ++ " " ++ originalTypeText
    let localRefPairs : List (Nat × String) := Id.run do
      let mut res : List (Nat × String) := []
      for j in [span.bodyStart:haveIdx] do
        if inScopeAt j then
          for seg in (lines[j]!.trim.splitOn ";") do
            let s := seg.trim
            if s.startsWith "by_cases " then
              match (s.drop "by_cases ".length).splitOn " : " with
              | nm :: _ :: _ => res := res ++ [(j, nm.trim)]
              | _ => pure ()
            else if s.startsWith "intro " then
              res := res ++ (((s.drop "intro ".length).splitOn " "
                |>.filter (fun x => x.length > 0 && x != "_" && x.all (fun c => c.isAlphanum || c == '_' || c == '\'' || c.val ≥ 0x80))).map ((j, ·)))
            else if s.startsWith "funext " then
              res := res ++ (((s.drop "funext ".length).splitOn " " |>.filter (·.length > 0)).map ((j, ·)))
            else if s.startsWith "obtain " || s.startsWith "rcases " then
              -- DESTRUCTURING binders: `obtain ⟨c, hc⟩ := e` (pattern before
              -- `:=`) / `rcases e with ⟨c, hc⟩` (pattern after ` with `).
              -- Unharvested, they surface as unbound identifiers in the
              -- assembled lemma (`hc`, the counting_obstruction last layer).
              let pat :=
                if s.startsWith "obtain " then
                  (((s.drop "obtain ".length).splitOn " := ").head!)
                else match s.splitOn " with " with
                  | _ :: p :: _ => p
                  | _ => ""
              let names := ((pat.toList.map (fun ch =>
                  if ch == '⟨' || ch == '⟩' || ch == ',' || ch == '|' ||
                     ch == '(' || ch == ')' || ch == ':' || ch == '=' then ' ' else ch)).asString.splitOn " ")
                |>.filter (fun x => x.length > 0 && x != "_" &&
                  (x.data.head!.isAlpha || x.data.head!.val ≥ 0x80))
              res := res ++ (names.map ((j, ·)))
      return res.filter (fun (_, nm) => containsWord refText nm)
    -- SOURCE-LINE order: `revert` reorders to context order, which is the
    -- order of introduction — i.e. line order. The intro-line assignment
    -- of arrow slots below depends on this ordering.
    let revertRefs : List String :=
      (((priorRefPairs ++ localRefPairs).toArray.qsort (fun a b => a.1 < b.1)).toList.map (·.2)).eraseDups
    plogInfo s!"[extract-probe] '{haveName}' revertRefs: [{" ".intercalate revertRefs}] (priors {priorRefPairs.length}, locals {localRefPairs.length})"
    -- Variant grid entries are (cvLine, revertNames, renderPrefix):
    -- 1. the cv ladder (no revert, default rendering)
    -- 2. plain revert — locals/priors folded into the captured telescope
    -- 3. clear_value + revert — opaque ldecl params + bound locals (aims
    --    the gate's first error at the LET-REPLAY trigger)
    -- 4. LET-TELESCOPE: revert + `pp.proofs true` rendering — the ldecls
    --    stay in the captured RETURN as a `let`-chain, but with their
    --    values printed IN FULL (no `⋯` proof elision). The lemma keeps
    --    the chain verbatim; `intro` re-introduces the ldecls with their
    --    TRANSPARENCY intact (so `simp [code]`-style delta use needs no
    --    replay), and the callsite's own identical ldecls make the
    --    type-directed application definitional (zeta).
    -- Rendering 1 adds `pp.notation false`: notation like the Finset
    -- set-builder (`{i | ↑x i = ω}` for `Finset.univ.filter ...`) does NOT
    -- round-trip without a known expected type ("invalid coercion notation",
    -- 17 gate rejections in one run) — explicit applications do. Rendering 2
    -- is the maximally explicit fallback (rung E's 4th rendering).
    -- pp.letVarTypes: anonymous instance ldecls print as
    -- `let this := inferInstance;` WITHOUT the ascription — re-elaborating
    -- bare `inferInstance` mints a stuck `?m` ("type class instance
    -- expected", the whole counting_obstruction class); with the option the
    -- binder round-trips as `let this : DecidablePred ... := inferInstance;`.
    let ppLetTele1 := "set_option pp.letVarTypes true in\nset_option pp.fullNames true in\nset_option pp.notation false in\nset_option pp.funBinderTypes true in\nset_option pp.proofs true in\nset_option pp.deepTerms true in\n"
    -- pp.explicit does NOT expand notation: the Finset set-builder
    -- `{s | ...}` survives it and re-elaborates as `Set` ("Application
    -- type mismatch ... Finset.sum low"), while rendering 1's
    -- pp.notation-false output dies on `↑x` coercions instead (which
    -- pp.explicit DOES expand, to `@Subtype.val ...`). Both options
    -- together cover both failure halves.
    let ppLetTele2 := "set_option pp.letVarTypes true in\nset_option pp.explicit true in\nset_option pp.notation false in\nset_option pp.proofs true in\nset_option pp.deepTerms true in\nset_option pp.universes true in\n"
    let cvVariantsR : List (String × List String × String) :=
      (cvVariants.map (fun cv => (cv, ([] : List String), ""))) ++
      (if revertRefs.isEmpty then [] else
        [("", revertRefs, "")] ++
        (if clearNames.isEmpty then [] else [(cvClearLine, revertRefs, "")]) ++
        [("", revertRefs, ppLetTele1), ("", revertRefs, ppLetTele2)]) ++
      -- no-revert rendering fallbacks — UNCONDITIONAL, two reasons:
      -- (1) goal-referenced ldecls put a `let x := ...;` prefix in the
      -- capture even when nothing needs reverting (wonTele handles it);
      -- (2) default pp DROPS context-inferable implicit args (`modQTarget
      -- p` loses its {q}) — re-elaboration hits a stuck
      -- `Fact (Nat.Prime ?m)` instance; only the explicit rendering
      -- round-trips those, and the class occurs with NO ldecls in sight.
      [("", ([] : List String), ppLetTele1), ("", ([] : List String), ppLetTele2)]
    -- FULL retry loop — capture, parse, assembly and verification all live
    -- INSIDE the variant loop: a variant that captures cleanly can still fail
    -- at the ASSEMBLY gate for a reason only the NEXT variant fixes
    -- (clear_value alone captures `(a : ℝ)` opaque, but a transparency-reliant
    -- proof — `log_pos hN_pos : 0 < log ↑N` against goal `0 < a` — only
    -- assembles under the unfold rung). Observed for real: `ha_pos` failed
    -- exactly this way while only the CAPTURE step was retried per variant.
    let mut lastMsgs : Array String := #[]
    -- the let-replay retry is EXPENSIVE (two capped-but-heavy gates) — fire
    -- it at most once per have, not once per rendering variant
    let mut letReplayTried := false
    -- same once-per-have budget for the inaccessible-args callsite retry
    let mut inaccRetried := false
    for (cvLine, revertNames, renderPrefix) in cvVariantsR do
      let revertLine := if revertNames.isEmpty then "" else
        tacticIndentStr ++ "revert " ++ " ".intercalate revertNames ++ "\n"
      -- keepTail: append the theorem's ORIGINAL remaining proof after the
      -- probed have instead of truncating. Used as a RETRY when the capture
      -- contains unassigned metavariables (`?m.NN` in the printed sig):
      -- extract_goal's message is FORMATTED LAZILY, so assignments made by
      -- the LATER tactics (deferred unification, postponed instances —
      -- `DecidablePred fun x => (MvPolynomial.eval ?m.137) ... ` on
      -- rootCube_counting_obstruction) exist by pretty-print time and the
      -- retried capture round-trips.
      let mkSrc (keepTail : Bool) : String :=
        renderPrefix ++
        ambientPrefix ++
        renamedHeader ++ "\n" ++ prefixText ++
        headerBeforeAssign ++ " := by\n" ++
        cvLine ++
        revertLine ++
        tacticIndentStr ++ "extract_goal using __sig__\n" ++
        tacticIndentStr ++ "sorry\n" ++
        (if keepTail then
          "\n".intercalate ((lines.extract relEnd span.bodyEnd).toList) ++ "\n"
         else "") ++
        baseIndentStr ++ "all_goals sorry\n"
      let msgs ← captureWithDependencyRetry lines ambientPrefix (mkSrc false)
      lastMsgs := msgs
      let captured? : Option String ← do
        match findExtractedSignature msgs with
        | some s =>
          -- A `let x := ...;` in the captured signature is a replayed ldecl
          -- the cleanup did NOT prune — unbindable as a parameter, so don't
          -- accept it while the clear_value variants are still untried.
          -- EXCEPT under the let-telescope rendering variant, which WANTS
          -- the chain (fully printed) in the return.
          if renderPrefix.isEmpty && cvLine.isEmpty && !clearNames.isEmpty &&
             (s.splitOn "let ").length ≥ 2 then pure none
          else if (s.splitOn "?m.").length ≥ 2 then do
            -- metavar-carrying capture — retry with the tail kept
            let msgs2 ← captureWithDependencyRetry lines ambientPrefix (mkSrc true)
            match findExtractedSignature msgs2 with
            | some s2 =>
              if (s2.splitOn "?m.").length ≥ 2 then
                plogInfo s!"[extract-probe] '{haveName}' capture still metavar-carrying after keep-tail retry"
                pure none
              else pure (some s2)
            | none => pure none
          else pure (some s)
        | none =>
          if !revertNames.isEmpty then
            let e := (msgs.find? (fun mg => (mg.splitOn "error").length ≥ 2)).getD s!"({msgs.size} msgs)"
            plogInfo s!"[extract-probe] '{haveName}' revert-priors [{" ".intercalate revertNames}] capture failed: {e.take 240}"
          pure none
      match captured? with
      | none => continue
      | some capturedSigText0 =>
        let wonUnfold := cvLine.startsWith unfoldMarker
        let wonRevert := !revertNames.isEmpty
        -- telescope handling (verbatim return, intro line, type-directed
        -- callsite) applies to BOTH the revert variants and the no-revert
        -- let-telescope renderings: a goal-referenced ldecl produces a
        -- `let x := ...;` capture prefix even with nothing to revert
        -- (observed: hchoose's chooseC — revertRefs empty, telescope rung
        -- never fired, capture kept a `Classical.choose ⋯` elision)
        let wonTele := wonRevert || !renderPrefix.isEmpty
        -- `extract_goal` pretty-prints in whatever environment THIS PROBE runs in, which
        -- always has Mathlib loaded (needed for `extract_goal` itself) — so it renders
        -- `Nat` as `ℕ` regardless of how the ORIGINAL source wrote it. If the target file
        -- doesn't import Mathlib (as plain files may not), `ℕ` would be unresolvable in
        -- the written-out output. For now, normalize back to `Nat` unconditionally.
        let capturedSigText := capturedSigText0.replace "ℕ" "Nat"
        -- DAGGERED SIG PARAMS (#57): `extract_goal` prints INACCESSIBLE
        -- context hyps as literal `{m✝ : Nat} (gates✝ : ...)` groups — `✝`
        -- is not valid syntax, so every variant died at PARSE ("expected
        -- token" exactly at the dagger; CircuitTreeManip h_elem_le_foldr).
        -- Binder names of a standalone lemma are arbitrary: rename them to
        -- fresh accessible names (longest marker first so `✝¹` never leaves
        -- a stray `¹`). The source-replayed proof body cannot reference
        -- them (they were inaccessible), and the CALLSITE side is covered
        -- by the inacc-args retry (type-directed `apply <;> assumption`).
        let capturedSigText := (((((capturedSigText.replace "✝⁴" "_inacc4").replace
          "✝³" "_inacc3").replace "✝²" "_inacc2").replace "✝¹" "_inacc1").replace "✝" "_inacc")
        -- extract_goal renders universe-polymorphic captures with a UNIVERSE
        -- SPEC after the name (`__sig__.{u_2, u_1} ...`) — the group parsers
        -- would read `{u_2, u_1}` as a (comma-broken) binder group, failing
        -- every capture in a `Type*`-variable file (Entropy.lean: 0/77).
        -- Split it off and re-attach it to the extracted lemma's NAME
        -- (`private lemma foo.{u_2, u_1} ...` is valid syntax); callsites
        -- need no change (universes are inferred), but the DECLARATION must
        -- bind them: the output file sets `autoImplicit false`, which
        -- disables universe auto-binding too.
        let (univSpec, capturedSigText) :=
          if capturedSigText.startsWith "__sig__.{" then
            let afterName := capturedSigText.drop "__sig__".length
            match afterName.splitOn "}" with
            | spec :: rest => (spec ++ "}", "__sig__" ++ "}".intercalate rest)
            | [] => ("", capturedSigText)
          else ("", capturedSigText)
        -- Collision-proof universe names for the WRITTEN lemma: it lands
        -- inside the file's `variable {.. : Type*}` scope, whose auto-named
        -- `u_k` levels collide with an explicit `.{u_k, ...}` spec
        -- ("universe level already declared" — 15 output errors on
        -- Entropy.lean, cascading into "Unknown identifier" at every
        -- callsite; the lemma-check probe couldn't see it because it
        -- deliberately omits the `variable` prefix). Longest names first so
        -- `u_1` never clobbers `u_10`'s text. `scrubUnivs` handles the
        -- CALLSITE ascription instead: `Type u_k` from one capture can be
        -- unknown in another context ("unknown universe level `u_6`") — an
        -- inferred `Type _` is always right there, since the call's result
        -- type determines it.
        let univNames := (if univSpec.isEmpty then [] else
            ((univSpec.drop 2).dropRight 1).splitOn "," |>.map String.trim)
          |>.filter (·.length > 0)
        let univNamesSorted := univNames.toArray.qsort (fun a b => a.length > b.length) |>.toList
        let renameUnivs (s : String) : String :=
          univNamesSorted.foldl (fun acc n => acc.replace n ("ul" ++ n.drop 1)) s
        let scrubUnivs (s : String) : String :=
          univNamesSorted.foldl (fun acc n =>
            (acc.replace ("Type " ++ n) "Type _").replace ("Sort " ++ n) "Sort _") s
        match parseExtractedSignature capturedSigText with
        | none =>
          plogInfo s!"[extract-probe] '{haveName}' captured sig unparseable: {capturedSigText.take 500}"
          continue
        | some (_capturedName, argNames, _restAfterName, retType, _paramsOnlyText, groups) =>
          -- Source-level type text is preferred (bug #17: captured types drop
          -- ascriptions) — EXCEPT when the unfold rung produced this capture:
          -- the source text still mentions the now-cleared ldecl (`0 < a`),
          -- which the lemma doesn't bind; the captured type is the unfolded,
          -- definition-free one, and the real callsite accepts it by defeq.
          -- under the revert-priors variant the captured RETURN carries the
          -- reverted hypotheses as leading arrows — it must be used verbatim
          let effectiveType := if originalTypeText.isEmpty || wonUnfold || wonTele then retType else originalTypeText
          -- `extract_goal`'s `revert` prenexes the have's OWN leading `∀`-binders together
          -- with genuine reverted context hypotheses (both just look like parameter groups
          -- in the captured signature) — so any names bound by a leading `∀` in the have's
          -- OWN type must be excluded from the call-site arguments: applying them would be
          -- wrong (they aren't in scope where the have appears) and unnecessary (leaving
          -- them off keeps the call's result correctly `∀`-quantified, matching the have's
          -- original type exactly).
          -- Under the revert-closure variant the captured RETURN is the whole
          -- telescope (closure → original type) and its leading ∀-binders are
          -- NOT parameter groups — they must stay in the return verbatim, so
          -- the leading-∀-as-params machinery is disabled for it.
          let leadingNames := if wonTele then [] else leadingForallBoundNames effectiveType
          -- Revert-closure application is TYPE-DIRECTED at the callsite (see
          -- the `call` construction below): no textual chain-parsing — data
          -- vars are recovered by unifying the lemma's conclusion with the
          -- have's stated type, hypothesis antecedents (named OR anonymous)
          -- by `assumption` matching the local context by type.
          let callArgNames := argNames.filter (fun n => !leadingNames.contains n)
          -- Lemma-side of the revert-closure variant: the proof must first
          -- re-introduce the telescope under the NAMES the copied proof body
          -- uses. Assignment is pp-directed: named ∀-groups keep their pp
          -- names (revert preserves user names); anonymous arrow slots take
          -- the reverted Prop refs not matched by any named group, in
          -- source-line order; parsing stops once every reverted ref is
          -- covered (T's own structure is never introduced). A wrong
          -- assignment cannot commit — the declaration gate rejects it.
          -- TYPE-KNOWN prop refs skip slot assignment entirely: after the
          -- intros, `have R : <source type> := by assumption` re-binds them
          -- type-directedly (defeq match — immune to pp variance and to the
          -- telescope's context-order interleaving that defeats positional
          -- alignment; observed both ways: hc needed back-align, hall broke
          -- under it). Sources of known types: prior have one-liners and
          -- `by_cases R : TYPE` lines.
          let refTypeOf (nm : String) : Option String := Id.run do
            match findPriorOneLinerType lines span.bodyStart haveIdx nm with
            | some t => return some t
            | none =>
              for j in [span.bodyStart:haveIdx] do
                for seg in (lines[j]!.trim.splitOn ";") do
                  let s := seg.trim
                  if s.startsWith ("by_cases " ++ nm ++ " : ") then
                    return some (s.drop ("by_cases " ++ nm ++ " : ").length)
              return none
          let (revertIntroNames, recoveryLines) : List String × List String := Id.run do
            if !wonTele then return ([], [])
            -- pre-parse the leading telescope into slots (over-parsing into
            -- T's own structure is harmless: the cut rule below discards it)
            -- slot = (payload, isLet): payload some = named group/let name,
            -- none = anonymous arrow
            let mut slots : List (Option (List String) × Bool) := []
            let mut namedSeen : List String := []
            let mut restTy := effectiveType.trimLeft
            let mut fuel := 60
            while fuel > 0 do
              fuel := fuel - 1
              if restTy.startsWith "∀ (" || restTy.startsWith "∀ {" then
                let (nms, rest) := dropOneLeadingForallLevel restTy
                if nms.isEmpty then fuel := 0
                else
                  slots := slots ++ [(some nms, false)]
                  namedSeen := namedSeen ++ nms
                  restTy := rest.trimLeft
              else if restTy.startsWith "let " then
                -- let-telescope slot: `let NAME := value;` (or `let NAME :
                -- T := value;`) — `intro NAME` re-introduces the ldecl with
                -- its transparency intact. The value can contain brackets;
                -- the binder ends at the first `;` at bracket depth 0.
                let afterLet := restTy.drop "let ".length
                let nm := ((afterLet.splitOn " ").head!.splitOn " :").head!
                let mut depth : Int := 0
                let mut cut : Option Nat := none
                let mut idx := 0
                for c in afterLet.toList do
                  if cut.isNone then
                    if c == '(' || c == '{' || c == '[' || c == '⟨' then depth := depth + 1
                    else if c == ')' || c == '}' || c == ']' || c == '⟩' then depth := depth - 1
                    else if c == ';' && depth == 0 then cut := some idx
                  idx := idx + 1
                match cut with
                | none => fuel := 0
                | some cutIdx =>
                  if nm.isEmpty then fuel := 0
                  else
                    slots := slots ++ [(some [nm], true)]
                    namedSeen := namedSeen ++ [nm]
                    restTy := (afterLet.drop (cutIdx + 1)).trimLeft
              else
                match splitAtTopLevelArrow restTy with
                | some (_, rest) =>
                  slots := slots ++ [(none, false)]
                  restTy := rest.trimLeft
                | none => fuel := 0
            -- only refs WITHOUT a known source type go through slot
            -- assignment; the rest are recovered by type after the intros
            let recov := revertNames.filter (fun nm => (refTypeOf nm).isSome && !namedSeen.contains nm)
            let walkRefs := revertNames.filter (fun nm => !recov.contains nm)
            let arrowRefs := walkRefs.filter (fun nm => !namedSeen.contains nm)
            -- BACK-ALIGN the arrow refs: `revert` pulls each ref's
            -- dependency closure, and pulled deps land BEFORE the refs in
            -- the telescope (context order) — front-aligned assignment gave
            -- hc to the FIRST arrow while its true slot was the last
            -- (observed: hbad_eq, `intro ... hc hpulled_1 ... hpulled_4`).
            -- Pad the front with fresh names instead.
            let arrowSlotCount := slots.foldl (fun acc (sl, _) => if sl.isNone then acc + 1 else acc) 0
            let frontPad := arrowSlotCount - arrowRefs.length
            let mut arrowQueue := arrowRefs
            let mut arrowsSeen := 0
            let mut remaining := walkRefs
            let mut out : List String := []
            let mut freshIdx := 0
            -- Stop rule: with all refs covered, LET slots are still consumed
            -- (the chain must be re-introduced for the body to see the
            -- ldecls); ∀/arrow slots stop the walk only when the body's own
            -- leading `intro` will handle them — otherwise they belong to
            -- the captured closure and must be introduced here too (e.g.
            -- `∀ (enc ...) (henc_inj ...)` bound AFTER a let they depend
            -- on, with a calc-led body). Wrong choices can't commit — the
            -- declaration gate rejects them.
            let bodyLeadsIntro :=
              (((proofBody.splitOn "\n").head!).trim.startsWith "intro")
            for (slot, isLet) in slots do
              -- with pending type-recovered refs, keep consuming: their
              -- arrow-hypotheses must be introduced (as fresh names) for
              -- the recovery `by assumption` to find them
              if remaining.isEmpty && !isLet && bodyLeadsIntro && recov.isEmpty then break
              match slot with
              | some nms =>
                out := out ++ nms
                remaining := remaining.filter (fun nm => !nms.contains nm)
              | none =>
                arrowsSeen := arrowsSeen + 1
                if arrowsSeen ≤ frontPad then
                  -- an unlisted pulled Prop (dependency closure) — fresh
                  -- inaccessible-safe name, unreferenced by the body
                  freshIdx := freshIdx + 1
                  out := out ++ [s!"hpulled_{freshIdx}"]
                else
                  match arrowQueue with
                  | nm :: rest =>
                    out := out ++ [nm]
                    arrowQueue := rest
                    remaining := remaining.filter (· != nm)
                  | [] =>
                    freshIdx := freshIdx + 1
                    out := out ++ [s!"hpulled_{freshIdx}"]
            let recovLines := recov.filterMap (fun nm =>
              (refTypeOf nm).map (fun t =>
                "have " ++ nm ++ " : " ++ collapseToOneLine t ++ " := by assumption"))
            return (out, recovLines)
          -- A reverted-context PARAMETER (e.g. `h_gowers_norm_pow`, a prior have now in
          -- scope) has the exact same ascription-dropping problem as the return type, but
          -- `extract_goal` gives us no "source text" for it. Its true, correctly-ascribed
          -- type is sitting right there in `lines` though: the one-liner this same
          -- extractor inserted when IT was extracted. Substitute that back in per-group —
          -- UNLESS the captured type is already LONGER than the one-liner's: that means an
          -- intervening tactic (e.g. `simp_all` rewriting via some OTHER hypothesis, like
          -- `hg.2 : lift_pm1 g = fun x => ...`) legitimately expanded/mutated this
          -- hypothesis's type IN PLACE at this exact point in the original proof, and
          -- `extract_goal`'s capture correctly reflects that live, current type — the
          -- one-liner's declared-at-extraction-time type would be STALE here, not more
          -- complete, and overriding with it would reintroduce the very mismatch this
          -- substitution exists to prevent.
          -- FORWARD-REFERENCE guard: a substituted one-liner type that
          -- mentions one of THIS signature's own binder names — where the
          -- captured type didn't — can place a reference BEFORE its binder
          -- ("Unknown identifier `x`" at an early column; the dominant
          -- SmolenskyAlgebra rejection class). Skip such substitutions.
          let ownBinderNames : List String := groups.toList.foldl (fun acc g =>
            if !g.startsWith "(" then acc else
            let inner := collapseToOneLine ((g.drop 1).dropRight 1)
            match inner.splitOn " : " with
            | nm :: _ :: _ => acc ++ (nm.trim.splitOn " " |>.filter (·.length > 0))
            | _ => acc) []
          let fixedGroups := groups.map fun g =>
            if !g.startsWith "(" then g
            else
              let inner := collapseToOneLine ((g.drop 1).dropRight 1)
              match inner.splitOn " : " with
              | name :: rest =>
                let capturedTy := " : ".intercalate rest
                match findPriorOneLinerType lines span.bodyStart haveIdx name.trim with
                | some fixedTy =>
                  let introducesForwardRef := ownBinderNames.any (fun nm =>
                    nm != name.trim && containsWord fixedTy nm && !containsWord capturedTy nm)
                  if fixedTy.length > capturedTy.length && !introducesForwardRef then
                    "(" ++ name.trim ++ " : " ++ fixedTy ++ ")"
                  else g
                | none => g
              | _ => g
          -- Rebuild the signature from the captured PARAMS (reliable) plus the have's
          -- own source-level type text (also reliable, and unlike the captured return
          -- type, never drops bound-variable ascriptions like `∑ x : hypercube n, ...`
          -- — see `parseExtractedSignature`'s docstring). If the have's own type has a
          -- leading `∀`, that header is ALREADY represented as a real parameter group in
          -- `paramsOnlyText` (via `revert`'s prenexing) — so it must be stripped from the
          -- return-type text here, or those names get bound TWICE.
          let returnTypeText :=
            if leadingNames.isEmpty then effectiveType else dropLeadingForallHeader effectiveType
          -- Term-mode haves (`have h : T := someTerm`) must stay term-mode: `someTerm`
          -- is a TERM, not a tactic, so `:= by\n someTerm` would be invalid syntax.
          let proofPart :=
            if isTacticHave then
              -- `extract_goal` already "pre-introduced" `leadingNames` as lemma parameters
              -- (see above) — so if the copied proof body's FIRST tactic is exactly the
              -- `intro`/`intros` that used to introduce them, it's now redundant (there's
              -- nothing left to introduce) and must be dropped, or the extracted lemma
              -- itself fails with "no additional binders ... to introduce".
              let rawProofLines := proofBody.splitOn "\n"
              -- Accept both `intro`/`intros` spellings and an optional trailing
              -- same-line `;` (e.g. `intro x;`), since either can appear verbatim
              -- in the copied proof body but neither affects what's being matched.
              let stripIntroPunct (s : String) : String :=
                let t := s.trim
                if t.endsWith ";" then t.dropRight 1 |>.trim else t
              -- The FIRST tactic's `intro`/`intros` names might cover MORE than just
              -- `leadingNames` — e.g. a have of type `∀ {T}, (hyp) → concl` intros both
              -- `T` (already a lemma param, via `leadingNames`) AND `hT` (the `→`'s own
              -- antecedent, genuinely still needing to be introduced here) in one
              -- `intros T hT`. Only the LEADING PREFIX matching `leadingNames` is
              -- redundant; whatever names follow it must stay as a (shorter) `intro`.
              --
              -- The intro clause can ALSO share its line with unrelated same-line
              -- continuation tactics via `;` (e.g. `intro x hs; split_ifs;`) — the
              -- intro clause itself ends at the FIRST `;`, not the line's LAST one
              -- (that trailing `;` belongs to the continuation tactic, not to
              -- `intro`). Splitting on the first `;` up front, rather than only
              -- trimming one off the very end of the whole line, keeps the two
              -- apart: `names` come from before it, `continuation` is everything
              -- from it onward, verbatim (empty if `intro` was the whole line).
              let introNamesOf (l : String) : Option (List String × String) :=
                let t := l.trim
                let afterKw :=
                  if t.startsWith "intros " then some (t.drop 7)
                  else if t.startsWith "intro " then some (t.drop 6)
                  else none
                match afterKw with
                | none => none
                | some rest =>
                  match rest.splitOn ";" with
                  | namesText :: contParts =>
                    let names := namesText.trim.splitOn " " |>.filter (·.length > 0)
                    let continuation := if contParts.isEmpty then "" else (";".intercalate contParts).trim
                    some (names, continuation)
                  | [] => some ([], "")
              -- Same redundancy, different shape: `exact fun S => term` (a TACTIC
              -- whose TERM is a lambda re-binding a name `leadingNames` already
              -- covers). Left alone, the lambda's type is a `∀`/Pi type but the
              -- actual goal (S already fixed as a real param) isn't — a type
              -- mismatch. Strips the matching leading `fun`-binders from the term,
              -- same prefix-match/keep-remainder logic as the `intro` case.
              let exactFunStrippedOf (l : String) : Option String :=
                let t := stripIntroPunct l
                let hadSemi := l.trim.endsWith ";"
                if !t.startsWith "exact " then none
                else
                  let afterExact := (t.drop 6).trim
                  let afterFun :=
                    if afterExact.startsWith "fun " then some (afterExact.drop 4)
                    else if afterExact.startsWith "λ " then some (afterExact.drop 2)
                    else none
                  match afterFun with
                  | none => none
                  | some rest =>
                    match rest.splitOn " => " with
                    | binderPart :: (restParts@(_ :: _)) =>
                      let lambdaNames := binderPart.trim.splitOn " " |>.filter (·.length > 0)
                      if lambdaNames.take leadingNames.length == leadingNames then
                        let remaining := lambdaNames.drop leadingNames.length
                        let bodyTerm := " => ".intercalate restParts
                        let rebuilt :=
                          if remaining.isEmpty then "exact " ++ bodyTerm
                          else "exact fun " ++ " ".intercalate remaining ++ " => " ++ bodyTerm
                        some (rebuilt ++ (if hadSemi then ";" else ""))
                      else none
                    | _ => none
              let strippedProofLines :=
                if !leadingNames.isEmpty then
                  match rawProofLines with
                  | first :: rest =>
                    match introNamesOf first with
                    | some (names, continuation) =>
                      if names.take leadingNames.length == leadingNames then
                        let remaining := names.drop leadingNames.length
                        let newIntro := if remaining.isEmpty then "" else "intro " ++ " ".intercalate remaining
                        match newIntro.isEmpty, continuation.isEmpty with
                        | true, true => rest
                        | true, false => continuation :: rest
                        | false, true => newIntro :: rest
                        | false, false => (newIntro ++ "; " ++ continuation) :: rest
                      else rawProofLines
                    | none =>
                      match exactFunStrippedOf first with
                      | some newFirst => newFirst :: rest
                      | none => rawProofLines
                  | [] => rawProofLines
                else rawProofLines
              let withRevertIntro :=
                if revertIntroNames.isEmpty then strippedProofLines
                else ("intro " ++ " ".intercalate revertIntroNames) :: (recoveryLines ++ strippedProofLines)
              let proofLines := withRevertIntro.map (fun l => "  " ++ l)
              " := by\n" ++ "\n".intercalate proofLines
            else
              -- Term-mode has the SAME leading-binder redundancy as tactic-mode
              -- `exact fun` (bug #23), on the bare proof term: a have with
              -- leading-∀ type proved by `fun t => ...` now has `t` as a
              -- pre-introduced lemma PARAMETER, so the lambda must shed those
              -- binders or its ∀-type mismatches the parameter-fixed goal
              -- (observed: `hedge_regret_bound`'s `hstep`,
              -- `fun t => log_potential_step ... t (by omega)`).
              let tb := proofBody.trim
              let strippedTerm : Option String :=
                if leadingNames.isEmpty then none
                else
                  let afterFun :=
                    if tb.startsWith "fun " then some (tb.drop 4)
                    else if tb.startsWith "λ " then some (tb.drop 2)
                    else none
                  match afterFun with
                  | none => none
                  | some rest =>
                    match rest.splitOn " => " with
                    | binderPart :: (restParts@(_ :: _)) =>
                      let lambdaNames := binderPart.trim.splitOn " " |>.filter (·.length > 0)
                      if lambdaNames.take leadingNames.length == leadingNames then
                        let remaining := lambdaNames.drop leadingNames.length
                        let bodyTerm := " => ".intercalate restParts
                        some (if remaining.isEmpty then bodyTerm
                              else "fun " ++ " ".intercalate remaining ++ " => " ++ bodyTerm)
                      else none
                    | _ => none
              match strippedTerm with
              | some s => " :=\n  " ++ s
              | none =>
                if revertIntroNames.isEmpty then " :=\n  " ++ proofBody
                else
                  -- telescope return needs the closure introduced first; the
                  -- term body becomes an `exact` under it
                  " := by\n  intro " ++ " ".intercalate revertIntroNames ++ "\n" ++
                  (recoveryLines.foldl (fun acc l => acc ++ "  " ++ l ++ "\n") "") ++
                  "  exact " ++ proofBody
          -- `extract_goal`'s captured context can include a parameter this have's
          -- OWN proof never actually needs (`MVarId.cleanup` erring conservative) —
          -- and if some UNRELATED sibling extraction later mutates its own copy of
          -- that same-named hypothesis (e.g. via `simp_all`) before calling this
          -- lemma, the argument passed won't match this signature's captured type.
          -- Dropping a provably-unused parameter sidesteps that — but "provably
          -- unused" can't be decided by checking whether its NAME appears in the
          -- return type/proof text: tactics like `omega`/`simp_all`/`aesop` consult
          -- every hypothesis in context regardless of whether it's named anywhere,
          -- so a hypothesis can be load-bearing while textually invisible (confirmed
          -- empirically: dropping one this way broke a downstream `omega` call in
          -- testing). The sound alternative is to not GUESS at all — actually
          -- attempt to drop each candidate parameter and RE-ELABORATE the resulting
          -- lemma for real; keep the drop only if it still verifies with zero
          -- errors, exactly the same test a human would run. `leadingNames` params
          -- are never candidates (they're the have's own quantified variables, not
          -- reverted context — removing them would change the type, not just prune
          -- an unused hyp).
          --
          -- Empirical verification alone isn't quite enough either: it tests whether
          -- the CANDIDATE LEMMA'S OWN DECLARATION still elaborates, which is NOT the
          -- same as testing whether its CALL SITES still work — an implicit
          -- parameter (e.g. `{d : Nat}`) needs no textual "evidence" to declare a
          -- lemma (it's just a bound variable there), only to be INFERRED later at a
          -- use site from the explicit arguments/expected type actually supplied.
          -- Dropping every explicit parameter that happens to mention `d` (each
          -- individually looking "safe" by the standalone-elaboration test) silently
          -- orphans `d` at the CALL SITE instead ("don't know how to synthesize
          -- implicit argument") — confirmed as a real regression, not hypothetical.
          -- So: first apply a cheap, EXACT syntactic pre-filter — never even
          -- consider dropping a parameter if doing so would leave some implicit name
          -- with no remaining mention anywhere (return type, proof, or another KEPT
          -- parameter's type) — before spending an elaboration attempt on it at all.
          -- This is fully decidable from text (implicit-argument inference depends
          -- mechanically on what's textually present), unlike the omega/simp_all
          -- case above, which genuinely isn't.
          let namesOfGroup (g : String) : List String :=
            let inner := collapseToOneLine ((g.drop 1).dropRight 1)
            match inner.splitOn " : " with
            | first :: _ => first.trim.splitOn " " |>.filter (·.length > 0)
            | _ => inner.trim.splitOn " " |>.filter (·.length > 0)
          let typeOfGroup (g : String) : String :=
            let inner := collapseToOneLine ((g.drop 1).dropRight 1)
            match inner.splitOn " : " with
            | _ :: rest => " : ".intercalate rest
            | _ => ""
          let implicitNames : List String :=
            fixedGroups.toList.foldl (fun acc g => if g.startsWith "(" then acc else acc ++ namesOfGroup g) []
          let directUseText := returnTypeText ++ " " ++ proofBody
          -- USAGE-ORACLE SEEDING (see `binderUsage` / `collectHaveRedexUsage`):
          -- elaborate the FULL candidate lemma ONCE and read per-parameter usage
          -- off the stored type+proof term. A parameter whose variable occurs in
          -- neither the remaining type nor the proof body is the only kind worth
          -- spending a drop-trial elaboration on — proof-term usage is
          -- authoritative even for context-sweeping tactics (omega/simp_all/...):
          -- their reconstructed proofs reference exactly what they consumed.
          -- USED parameters are skipped outright: dropping them either fails (a
          -- wasted heavy elaboration — previously the COMMON case, one whole-lemma
          -- trial per parameter) or "succeeds" via silent rederivation, changing
          -- the proof route for no benefit. Each remaining candidate is STILL
          -- empirically verified before committing (the oracle seeds, the
          -- elaborator decides). Falls back to trying every candidate when the
          -- probe yields no usable term.
          let fullParamsText := fixedGroups.toList.foldl (fun acc g => acc ++ " " ++ collapseToOneLine g) ""
          let utrialName := externalName ++ "__utrial"
          let utrialText := lemmaPrefix ++ "lemma " ++ utrialName ++ univSpec ++ fullParamsText ++ " : " ++
            collapseToOneLine returnTypeText ++ proofPart
          let paramUsage : Array (Name × Bool) ←
            match ← elabGetDeclInfo utrialText (Name.mkSimple utrialName) with
            | some info => pure (binderUsage info.type info.value? #[])
            | none => pure #[]
          let provenUnused (nm : String) : Bool :=
            match paramUsage.find? (fun (n, _) => n.eraseMacroScopes.toString == nm) with
            | some (_, used) => !used
            | none => false
          let mut keep : Array Bool := fixedGroups.map fun _ => true
          for i in [0:fixedGroups.size] do
            let g := fixedGroups[i]!
            let isCandidate := g.startsWith "(" && !(namesOfGroup g).any leadingNames.contains &&
              (paramUsage.isEmpty || (namesOfGroup g).all provenUnused)
            if isCandidate then
              let trialGroups := (Array.range fixedGroups.size).filterMap fun j =>
                if j == i then none
                else if keep[j]! then some fixedGroups[j]! else none
              let wouldOrphanImplicit := implicitNames.any fun im =>
                !containsWord directUseText im &&
                !trialGroups.any fun g' => containsWord (typeOfGroup g') im
              if !wouldOrphanImplicit then
                let trialParamsText := trialGroups.toList.foldl (fun acc g' => acc ++ " " ++ collapseToOneLine g') ""
                let trialSigLine := externalName ++ univSpec ++ trialParamsText ++ " : " ++ collapseToOneLine returnTypeText
                let trialLemmaText := "private lemma " ++ trialSigLine ++ proofPart
                let ok ← elabCheckOk (lemmaPrefix ++ trialLemmaText)
                if ok then
                  keep := keep.set! i false
          let finalGroups := (Array.range fixedGroups.size).filterMap fun j =>
            if keep[j]! then some fixedGroups[j]! else none
          let finalKeptNames : List String :=
            finalGroups.toList.foldl (fun acc g => if g.startsWith "(" then acc ++ namesOfGroup g else acc) []
          let callArgNames := callArgNames.filter (fun n => finalKeptNames.contains n)
          let paramsOnlyText := finalGroups.toList.foldl (fun acc g => acc ++ " " ++ collapseToOneLine g) ""
          let finalSigLine := externalName ++ univSpec ++ paramsOnlyText ++ " : " ++ collapseToOneLine returnTypeText
          -- SHIPPED-ERROR GATES (#51, mirrored in rung T): a captured
          -- signature carrying a pp-elided proof rendered as `sorry`, or a
          -- match-compiler auxiliary reference (`<thm>.match_N`), elaborates
          -- green in probes (sorry is a valid term; the aux constant resolves
          -- via the IMPORTED compiled module) but ships breakage in the
          -- standalone written file. Reject the variant — safe-direction.
          if containsWord finalSigLine "sorry" || (finalSigLine.splitOn ".match_").length ≥ 2 ||
             (finalSigLine.splitOn "._simp_").length ≥ 2 || (finalSigLine.splitOn "._proof_").length ≥ 2 || (finalSigLine.splitOn "._eq_").length ≥ 2 then
            plogInfo s!"[extract-probe] '{haveName}' variant rejected: captured sig carries sorry/match-aux"
            continue
          -- SELF-RECURSION GATE (#56): see the anonymous branch — a
          -- self-call in the have's proof forward-references the decl from
          -- the spliced aux lemma; probe-green via the imported module.
          if containsWord proofPart span.name || containsWord finalSigLine span.name then
            plogInfo s!"[extract-probe] '{haveName}' variant rejected: self-recursive (references enclosing decl '{span.name}')"
            continue
          -- CHECK-CONTEXT = WRITE-CONTEXT (the #36 lesson, once more): the
          -- gate elaborates under lemmaPrefix (set_options + opens +
          -- classicalPrefix), but the WRITTEN file only has file-level
          -- opens — a lemma that gate-passed via scoped-classical instances
          -- or a raised heartbeat cap then FAILS in the output (observed:
          -- Fintype Kˣ synthesize failures + whnf timeout shipping 12
          -- in-file errors). Bake both into the written text.
          let lemmaText := renameUnivs (setOptPrefix ++ classicalPrefix ++ "private lemma " ++ finalSigLine ++ proofPart)
          -- Revert-closure callsite is TYPE-DIRECTED: `apply` unifies the
          -- lemma's conclusion with the have's stated type (recovering pulled
          -- DATA vars — x, i, … — from their occurrences in it), and
          -- `assumption` discharges every hypothesis antecedent by matching
          -- the local context BY TYPE — recovering names (`by_cases`/`intro`
          -- locals, pulled priors) that no textual chain-parse can, with no
          -- boundary ambiguity between pulled arrows and the type's own.
          let call :=
            if wonTele then
              -- ZERO explicit args: positional captured-param names can be
              -- out of scope at the callsite (branch-scoped props like
              -- `hall` captured as PARAM groups — observed unknown-id at
              -- the gate); unification recovers data params from the stated
              -- type, `assumption` closes hypothesis goals, instances
              -- synthesize.
              "by apply " ++ externalName ++ " <;> assumption"
            else if callArgNames.isEmpty then externalName
            else "(" ++ externalName ++ " " ++ " ".intercalate callArgNames ++ ")"
          let oneLinerIndent := bulletIndentStr ++ (if isBulletAttached then "  " else "")
          -- Include the TYPE annotation (not just `have NAME := call`): otherwise this
          -- one-liner is itself indistinguishable from an un-extracted `have` on the
          -- NEXT scan of this theorem (it still starts with `have NAME`), and worse,
          -- lacks an explicit type — so if it WERE picked up again, `extract_goal`
          -- would see the have's type as an unresolved metavariable, not the real type.
          -- the one-liner states the have's ORIGINAL type: the type-directed
          -- `apply … <;> assumption` peels the lemma's closure telescope off
          let oneLinerTy := if wonTele && !originalTypeText.isEmpty then originalTypeText else effectiveType
          let oneLiner := oneLinerIndent ++ "have " ++ haveName ++ " : " ++ scrubUnivs (collapseToOneLine oneLinerTy) ++ " := " ++ call
          let replacementLines : Array String :=
            (if isBulletAttached then #[bulletIndentStr ++ "·"] else #[]) ++
            (if termContinuation.isEmpty then #[oneLiner] else #[oneLiner, oneLinerIndent ++ termContinuation])
          let newLines := lines.extract 0 haveIdx ++ replacementLines ++ lines.extract relEnd lines.size
          -- `lemmaText` contains embedded "\n"s (it's a whole multi-line declaration) —
          -- MUST be split into one array element per physical line before insertion, or
          -- every later line-based scan over `lines` (`findAllDeclSpans`, `blockEnd`,
          -- `findAllHaveHeaders`, ...) treats this whole declaration as a single
          -- (degenerate, 1-line) array slot, silently never looking inside it again.
          let lemmaLines := (lemmaText.splitOn "\n").toArray
          let insAt := spliceLineAbove newLines span.headerStart
          let finalLines := newLines.extract 0 insAt ++ lemmaLines ++ #[""] ++
                             newLines.extract insAt newLines.size
          -- Verify the ASSEMBLED lemma AND the REWRITTEN THEOREM before
          -- committing (bug #11's lesson, extended to the declaration level —
          -- see `elabCheckFirstErrorSeq`); reject to the next variant on
          -- failure, logging the real reason (the rejection-reasons rule).
          let newBodyEnd := span.bodyEnd - (relEnd - haveIdx) + replacementLines.size
          let gateDecl := ambientPrefix ++ renamedHeader ++ "\n" ++
            "\n".intercalate (newLines.extract span.bodyStart newBodyEnd).toList
          match ← elabCheckFirstErrorSeq [lemmaPrefix ++ lemmaText, gateDecl] with
          | some err =>
            plogInfo s!"[extract-probe] '{haveName}' assembled lemma or rewritten decl rejected: {err.take 300}"
            if true then
              -- dump on EVERY rejection during the per-decl campaign — the
              -- synthesize/coercion/mismatch classes carried the decisive
              -- evidence three separate times while the narrow condition
              -- (PARSE/unknownIdentifier) hid them
              plogInfo s!"[extract-probe] '{haveName}' lemma text: {(collapseToOneLine lemmaText).take 2500}"
              plogInfo s!"[extract-probe] '{haveName}' decl text: {(collapseToOneLine gateDecl).take 2500}"
            -- INACCESSIBLE-ARGS retry: `extract_goal` prints inaccessible
            -- hypotheses (split/cases-arm scrutinees and their equations —
            -- `t✝`, `heq✝` in a `next fl fls _ =>` arm) under clean
            -- accessible-LOOKING names, so the positional callsite passes
            -- identifiers that do not exist in the tactic context ("Unknown
            -- identifier `t`" — EncodingProperties 0/3). Undetectable from
            -- the sig (the names look ordinary), so detect from the GATE
            -- error and retry the SAME lemma with the type-directed
            -- callsite: `apply` unifies data args from the have's stated
            -- type, `assumption` discharges hypothesis args by type —
            -- inaccessible hyps included.
            let unkName := match err.splitOn "identifier `" with
              | _ :: rest :: _ => (rest.splitOn "`").headD ""
              | _ => ""
            if !wonTele && !inaccRetried && !unkName.isEmpty && callArgNames.contains unkName then
              inaccRetried := true
              let call2 := "by apply " ++ externalName ++ " <;> assumption"
              let oneLiner2 := oneLinerIndent ++ "have " ++ haveName ++ " : " ++
                scrubUnivs (collapseToOneLine oneLinerTy) ++ " := " ++ call2
              let replacement2 : Array String :=
                (if isBulletAttached then #[bulletIndentStr ++ "·"] else #[]) ++
                (if termContinuation.isEmpty then #[oneLiner2]
                 else #[oneLiner2, oneLinerIndent ++ termContinuation])
              let newLines2 := lines.extract 0 haveIdx ++ replacement2 ++ lines.extract relEnd lines.size
              let lemmaLines2 := (lemmaText.splitOn "\n").toArray
              let insAt2 := spliceLineAbove newLines2 span.headerStart
              let finalLines2 := newLines2.extract 0 insAt2 ++ lemmaLines2 ++ #[""] ++
                                 newLines2.extract insAt2 newLines2.size
              let newBodyEnd2 := span.bodyEnd - (relEnd - haveIdx) + replacement2.size
              let gateDecl2 := ambientPrefix ++ renamedHeader ++ "\n" ++
                "\n".intercalate ((newLines2.extract span.bodyStart newBodyEnd2).toList)
              match ← elabCheckFirstErrorSeq [lemmaPrefix ++ lemmaText, gateDecl2] with
              | none =>
                elabPersistCommand (lemmaPrefix ++ lemmaText)
                plogInfo s!"[extract-probe] '{haveName}' INACC-ARGS retry committed (type-directed callsite)"
                return some finalLines2
              | some err2 =>
                plogInfo s!"[extract-probe] '{haveName}' inacc-args retry rejected: {err2.take 240}"
            -- LET-REPLAY retry (see `letDefsInPrefix`): the lemma's proof
            -- references let/set-bound names it can only use via delta
            -- unfolding, which an opaque parameter cannot provide — re-
            -- assemble with equation params `(hXdef : X = RHS)`, the proof's
            -- simp/rw bracket references rewritten to them (same rewrite
            -- direction as the delta), and `rfl` at the callsite, where the
            -- ldecl IS transparent.
            if (← letReplayEnabledRef.get) && !letReplayTried &&
               (err.splitOn "is not a proposition or let-declaration").length ≥ 2 then
              letReplayTried := true
              let replayDefs := (letDefsInPrefix prefixText contentIndentN).filter
                (fun (x, _) => containsWord proofBody x)
              if !replayDefs.isEmpty then
                let eqParams := replayDefs.foldl (fun acc (x, rhs) =>
                  acc ++ " (h" ++ x ++ "def : " ++ x ++ " = " ++ collapseToOneLine rhs ++ ")") ""
                let rewriteBrackets (l : String) : String :=
                  if (l.splitOn "simp").length ≥ 2 || (l.splitOn "rw [").length ≥ 2 then
                    replayDefs.foldl (fun acc (x, _) =>
                      (((acc.replace ("[" ++ x ++ ",") ("[h" ++ x ++ "def,")).replace
                        ("[" ++ x ++ "]") ("[h" ++ x ++ "def]")).replace
                        (", " ++ x ++ ",") (", h" ++ x ++ "def,")).replace
                        (", " ++ x ++ "]") (", h" ++ x ++ "def]")) l
                  else l
                let proofPart2 := "\n".intercalate ((proofPart.splitOn "\n").map rewriteBrackets)
                let sigLine2 := externalName ++ univSpec ++ paramsOnlyText ++ eqParams ++
                  " : " ++ collapseToOneLine returnTypeText
                let lemmaText2 := setOptPrefix ++ classicalPrefix ++ "private lemma " ++ sigLine2 ++ proofPart2
                let rfls := String.join (replayDefs.map (fun _ => " rfl"))
                -- under the revert-closure variant the callsite is TYPE-
                -- DIRECTED (see the main `call`): telescope hyps close by
                -- `assumption`, the replay's equation params by `rfl` (the
                -- ldecl IS transparent at the callsite)
                let call2 :=
                  if wonTele then
                    "by apply " ++ externalName ++ " <;> first | assumption | rfl"
                  else
                    "(" ++ externalName ++
                    (if callArgNames.isEmpty then "" else " " ++ " ".intercalate callArgNames) ++
                    rfls ++ ")"
                let oneLiner2 := oneLinerIndent ++ "have " ++ haveName ++ " : " ++
                  scrubUnivs (collapseToOneLine oneLinerTy) ++ " := " ++ call2
                let replacement2 : Array String :=
                  (if isBulletAttached then #[bulletIndentStr ++ "·"] else #[]) ++
                  (if termContinuation.isEmpty then #[oneLiner2]
                   else #[oneLiner2, oneLinerIndent ++ termContinuation])
                let newLines2 := lines.extract 0 haveIdx ++ replacement2 ++ lines.extract relEnd lines.size
                let lemmaLines2 := (lemmaText2.splitOn "\n").toArray
                let insAt2 := spliceLineAbove newLines2 span.headerStart
                let finalLines2 := newLines2.extract 0 insAt2 ++ lemmaLines2 ++ #[""] ++
                                   newLines2.extract insAt2 newLines2.size
                let newBodyEnd2 := span.bodyEnd - (relEnd - haveIdx) + replacement2.size
                -- the retry's THEOREM gate is capped too: caps on gates are
                -- safe-direction (a heavy-but-valid rewrite times out and gets
                -- REJECTED — a lost conversion, never shipped breakage), and
                -- the uncapped replay wedged two runs at 110+ CPU-minutes
                let gateDecl2 := ambientPrefix ++ "set_option maxHeartbeats 200000 in\n" ++
                  renamedHeader ++ "\n" ++
                  "\n".intercalate ((newLines2.extract span.bodyStart newBodyEnd2).toList)
                -- FINITE heartbeat cap on the LEMMA probe only: the replayed
                -- prefix sets `maxHeartbeats 0` for faithfulness, which also
                -- removes the divergence bound — a rewritten simp with
                -- equation args wedged a run at 120+ CPU-minutes. Innermost
                -- `set_option ... in` wins, so appending the cap after the
                -- prefix overrides it for this command alone; slow-but-valid
                -- conversions gate-reject (safe), runaways get bounded. The
                -- THEOREM gate keeps the faithful unbounded budget.
                let cappedLemma := lemmaPrefix ++ "set_option maxHeartbeats 200000 in\n" ++ lemmaText2
                match ← elabCheckFirstErrorSeq [cappedLemma, gateDecl2] with
                | none =>
                  elabPersistCommand (lemmaPrefix ++ lemmaText2)
                  plogInfo s!"[extract-probe] '{haveName}' LET-REPLAY committed ({replayDefs.length} defs)"
                  return some finalLines2
                | some err2 =>
                  plogInfo s!"[extract-probe] '{haveName}' let-replay rejected: {err2.take 240}"
            continue
          | none => pure ()
          -- Persist the REAL lemma (not a `:= sorry` stub) so LATER probes (for
          -- other haves in this same theorem, whose prefix text now calls
          -- `externalName`) resolve the identifier AND see the actual proof —
          -- closing the stub-vs-real behavioral gap in downstream probe
          -- verdicts. Same `open ... in` reasoning as the probe: the TEXT can
          -- contain unqualified references to the file's own definitions
          -- (extract_goal rendered it that way BECAUSE the probe had the same
          -- opens in scope), so persisting needs those opens too — `open ... in`
          -- only affects name resolution DURING elaboration, not where the
          -- declaration lands.
          elabPersistCommand (lemmaPrefix ++ lemmaText)
          return some finalLines
    -- All variants exhausted without a committed lemma. Each SPECIFIC
    -- rejection (unparseable sig, assembled-lemma error) was already logged
    -- per variant above; this covers the pure capture-failure case, which
    -- has no per-variant log — the rejection-reasons rule.
    match lastMsgs.find? (fun m => (m.splitOn "error").length ≥ 2) with
    | some e => plogInfo s!"[extract-probe] '{haveName}' all variants exhausted; last probe error: {e.take 300}"
    | none => plogInfo s!"[extract-probe] '{haveName}' all variants exhausted ({lastMsgs.size} msgs in last probe)"
    return none

-- ══ PROOF-TERM-BASED EXTRACTION (rung T) ═══════════════════════════════════
--
-- The residual class that defeats every text-replay mechanism (SmolenskyAlgebra's
-- rootCube/split lattices: interleaved by_cases/∑-binder structure under five
-- tactic-`let`s) fails at exactly one point: reconstructing the have's CONTEXT
-- by replaying source-prefix text into an `extract_goal` probe. This rung skips
-- prefix replay entirely. The WHOLE declaration — the current working-file text,
-- known to compile — is elaborated ONCE (rolled back); the stored proof term is
-- walked to the have's own redex (`(fun h : T => rest) v`, `letFun v (fun h =>
-- rest)`, or `.letE`); and the lemma signature is assembled from the TERM: the
-- have's type `T` and proof `v` instantiated in the exact local context of the
-- enclosing binders on the redex path, with the parameter list computed as the
-- transitive fvar closure of `T` and `v` (the AXLE insight: an elaborated proof
-- references exactly the hypotheses it consumed — even for context-sweeping
-- tactics like `simp_all` whose syntax names none of them). Tactic-`let`s stay
-- in the signature as a let-telescope with values printed IN FULL
-- (pp.proofs/pp.deepTerms — no `⋯`), so the proof-body TEXT, replayed verbatim
-- under an `intro` of the closure, keeps ldecl transparency, and the callsite
-- closes definitionally against the theorem's own identical lets. Gating and
-- writing follow the established discipline exactly: assembled lemma AND
-- rewritten declaration through `elabCheckFirstErrorSeq` before committing,
-- `set_option`/classical prefixes baked into the WRITTEN text
-- (check-context = write-context, the #36/#48 lesson).

/-- One enclosing binder on the path from a declaration's proof-term root to a
    target have-redex. `ty`/`val?` are still in loose-bvar (de Bruijn) form
    relative to the binders BEFORE this one in the stack. -/
private structure TBinder where
  name : Name
  ty   : Expr
  val? : Option Expr
  bi   : BinderInfo
  deriving Inhabited

/-- Pure syntactic search for the have-redex bound as `target`, accumulating the
    enclosing binder stack. Returns `(stack, T, v)` with `T`/`v` in loose-bvar
    form relative to `stack`. Mirrors `collectHaveRedexUsage`'s shape coverage:
    beta-redex tactic haves, `letFun` term haves, and `.letE` lets. -/
private partial def findHaveRedexStack (target : String) (e : Expr)
    (stack : Array TBinder) : Option (Array TBinder × Expr × Expr) :=
  let matchesName (n : Name) : Bool := n.eraseMacroScopes.toString == target
  if e.isAppOfArity ``letFun 4 then
    let args := e.getAppArgs
    let v := args[2]!
    match args[3]!.consumeMData with
    | .lam n ty b bi =>
      if matchesName n then some (stack, ty, v)
      else
        findHaveRedexStack target v stack <|>
        findHaveRedexStack target b (stack.push ⟨n, ty, none, bi⟩)
    | f =>
      findHaveRedexStack target v stack <|> findHaveRedexStack target f stack
  else
    match e with
    | .app f v =>
      match f.consumeMData with
      | .lam n ty b bi =>
        if matchesName n then some (stack, ty, v)
        else
          findHaveRedexStack target v stack <|>
          findHaveRedexStack target b (stack.push ⟨n, ty, none, bi⟩)
      | f' =>
        findHaveRedexStack target f' stack <|> findHaveRedexStack target v stack
    | .letE n ty v b _ =>
      if matchesName n then some (stack, ty, v)
      else
        findHaveRedexStack target v stack <|>
        findHaveRedexStack target b (stack.push ⟨n, ty, some v, .default⟩)
    | .lam n ty b bi => findHaveRedexStack target b (stack.push ⟨n, ty, none, bi⟩)
    | .forallE n ty b bi => findHaveRedexStack target b (stack.push ⟨n, ty, none, bi⟩)
    | .mdata _ b => findHaveRedexStack target b stack
    | .proj _ _ b => findHaveRedexStack target b stack
    | _ => none

/-- Rename every binder in `e` that would pretty-print unusably (macro-scoped/
    inaccessible names, `✝`, `this`, `_`-prefixed, compound) or that collides
    with an already-used name — pp's shadow-disambiguation would otherwise stamp
    `✝` marks that don't re-parse, and duplicate names re-parse with WRONG
    capture — to fresh `np_K` names. The first `spine` binders along the leading
    forall/let chain (the closure telescope, whose names the `intro` line and
    callsite must match) are kept verbatim; the caller pre-seeds the used-set
    with them. Binder names are display-only (bvars carry the semantics), so
    this is always sound. -/
private partial def renameNestedBindersGo (spine : Nat) (e : Expr) :
    StateM (Nat × List String) Expr := do
  let freshFor (n : Name) : StateM (Nat × List String) Name := do
    let (k, used) ← get
    let raw := n.eraseMacroScopes.toString
    let isSimpleOk := !n.hasMacroScopes &&
      (match n.eraseMacroScopes with | .str .anonymous _ => true | _ => false) &&
      raw.length > 0 && !raw.startsWith "_" && !(raw.toList.any (· == '✝')) &&
      raw != "this" && !used.contains raw
    if isSimpleOk then
      set (k, raw :: used)
      return n.eraseMacroScopes
    else
      let mut k' := k
      let mut nm := s!"np_{k'}"
      while used.contains nm do
        k' := k' + 1
        nm := s!"np_{k'}"
      set (k' + 1, nm :: used)
      return Name.mkSimple nm
  match e with
  | .forallE n ty b bi =>
    if spine > 0 then
      let ty' ← renameNestedBindersGo 0 ty
      let b' ← renameNestedBindersGo (spine - 1) b
      return .forallE n ty' b' bi
    else
      let n' ← freshFor n
      let ty' ← renameNestedBindersGo 0 ty
      let b' ← renameNestedBindersGo 0 b
      return .forallE n' ty' b' bi
  | .letE n ty v b nd =>
    if spine > 0 then
      let ty' ← renameNestedBindersGo 0 ty
      let v' ← renameNestedBindersGo 0 v
      let b' ← renameNestedBindersGo (spine - 1) b
      return .letE n ty' v' b' nd
    else
      let n' ← freshFor n
      let ty' ← renameNestedBindersGo 0 ty
      let v' ← renameNestedBindersGo 0 v
      let b' ← renameNestedBindersGo 0 b
      return .letE n' ty' v' b' nd
  | .lam n ty b bi =>
    let n' ← freshFor n
    let ty' ← renameNestedBindersGo 0 ty
    let b' ← renameNestedBindersGo 0 b
    return .lam n' ty' b' bi
  | .app f a => return .app (← renameNestedBindersGo 0 f) (← renameNestedBindersGo 0 a)
  | .mdata d b => return .mdata d (← renameNestedBindersGo spine b)
  | .proj t i b => return .proj t i (← renameNestedBindersGo 0 b)
  | _ => return e

/-- The term-derived signature data for one have: the printed closed statement
    under each rendering, the `intro` slot names (closure binders in order),
    the positional callsite argument names, and universe params. -/
private structure TermSigResult where
  sigTexts   : Array (String × String)
  introNames : Array String
  argNames   : Array String
  argsUsable : Bool
  univNames  : List String

/-- Rebuild the redex's binder stack as real fvars and run `k`. Prop-valued
    `.letE` binders are DEMOTED to plain hypotheses (value dropped): by
    definitional proof irrelevance nothing can depend on a prop-let's VALUE,
    and dropping it keeps giant proof terms (e.g. a converted one-liner's
    `by apply aux <;> assumption` elaboration) out of the printed signature.
    Data lets keep their values — the whole point of the let-telescope form. -/
private partial def withStackFVarsAux (stack : Array TBinder) (finalNames : Array Name)
    (i : Nat) (fvars : Array Expr) (isLets : Array Bool)
    (k : Array Expr → Array Bool → MetaM (Option TermSigResult)) :
    MetaM (Option TermSigResult) := do
  if i < stack.size then
    let b := stack[i]!
    let nm := finalNames[i]!
    let ty := b.ty.instantiateRev fvars
    match b.val? with
    | some v =>
      if ← Meta.isProp ty then
        Meta.withLocalDecl nm .default ty fun x =>
          withStackFVarsAux stack finalNames (i+1) (fvars.push x) (isLets.push false) k
      else
        Meta.withLetDecl nm ty (v.instantiateRev fvars) fun x =>
          withStackFVarsAux stack finalNames (i+1) (fvars.push x) (isLets.push true) k
    | none =>
      Meta.withLocalDecl nm b.bi ty fun x =>
        withStackFVarsAux stack finalNames (i+1) (fvars.push x) (isLets.push false) k
  else
    k fvars isLets

/-- From a redex's binder stack and its (loose-bvar) type/value, compute the
    closed lemma statement and its printable renderings. `proofText`/`typeText`
    are the have's SOURCE proof body and declared type, used to WIDEN the
    term-derived closure: a proof that unfolds an ldecl via `simp [x]` can
    leave no fvar trace of `x` in the term (zeta reduction) while the replayed
    TEXT still needs `x` bound — any binder whose (kept) name the source text
    mentions joins the closure. -/
private def buildTermClosure (stack : Array TBinder) (tyL vL : Expr)
    (proofText typeText : String) : MetaM (Option TermSigResult) := do
  let n := stack.size
  -- Final binder names: unique + accessible. The LAST occurrence of a
  -- duplicated source name keeps it (shadowing semantics — that's what the
  -- proof text's references resolve to); earlier duplicates and inaccessible
  -- names get fresh `tp_K` names.
  let rawName (b : TBinder) : Option String :=
    -- an anonymous-have binder is `this` WITH hygiene macro scopes — it must
    -- still be kept as the literal name `this` (the replayed proof text
    -- references it that way), so test the erased name BEFORE the
    -- hasMacroScopes exclusion
    if b.name.eraseMacroScopes.toString == "this" then some "this"
    else if b.name.hasMacroScopes then none
    else match b.name.eraseMacroScopes with
      | .str .anonymous s =>
        -- `this` is KEPT: `∀ (this : T), ...` parses and `intro this` works
        -- (verified by hand-probe), and the have's replayed proof TEXT may
        -- reference an enclosing anonymous hypothesis by exactly that name —
        -- renaming it to `tp_K` shipped "Unknown identifier `this`" across
        -- every rendering on Switching.lean's card_filter_numFree_eq. The
        -- last-occurrence dedup already ensures only the innermost (textually
        -- referencable) `this` keeps the name.
        if s.length > 0 && !s.startsWith "_" && !(s.toList.any (· == '✝')) then
          some s
        else none
      | _ => none
  let raws := stack.map rawName
  let mut keep : Array (Option String) := #[]
  for i in [0:n] do
    match raws[i]! with
    | some s =>
      let mut laterDup := false
      for j in [i+1:n] do
        if raws[j]! == some s then laterDup := true
      keep := keep.push (if laterDup then none else some s)
    | none => keep := keep.push none
  let keptSet : List String := keep.toList.filterMap id
  let mut finalNames : Array Name := #[]
  let mut origKept : Array Bool := #[]
  let mut ctr := 1
  for i in [0:n] do
    match keep[i]! with
    | some s =>
      finalNames := finalNames.push (Name.mkSimple s)
      origKept := origKept.push true
    | none =>
      let mut nm := s!"tp_{ctr}"
      while keptSet.contains nm do
        ctr := ctr + 1
        nm := s!"tp_{ctr}"
      ctr := ctr + 1
      finalNames := finalNames.push (Name.mkSimple nm)
      origKept := origKept.push false
  withStackFVarsAux stack finalNames 0 #[] #[] fun fvars isLets => do
    let T := tyL.instantiateRev fvars
    let V := vL.instantiateRev fvars
    let st := Lean.collectFVars (Lean.collectFVars {} T) V
    let mut needed : FVarIdSet := st.fvarSet
    -- text-referenced widening (see docstring)
    for i in [0:n] do
      if origKept[i]! then
        let s := finalNames[i]!.toString
        if containsWord proofText s || containsWord typeText s then
          needed := needed.insert fvars[i]!.fvarId!
    -- transitive dependency closure — ONE reverse pass suffices: an fvar's
    -- type/value only references EARLIER fvars (lctx well-formedness)
    for ri in [0:n] do
      let i := n - 1 - ri
      let id := fvars[i]!.fvarId!
      if needed.contains id then
        let d ← id.getDecl
        let mut s2 := Lean.collectFVars {} d.type
        if d.isLet then
          s2 := Lean.collectFVars s2 d.value
        for dep in s2.fvarIds do
          needed := needed.insert dep
    let closureIdx := (Array.range n).filter (fun i => needed.contains fvars[i]!.fvarId!)
    let closureFVars := closureIdx.map (fvars[·]!)
    let stmt0 ← Meta.mkForallFVars closureFVars T (usedLetOnly := false)
    if stmt0.hasFVar then
      logInfo "[term-extract] closure incomplete: statement still has free variables"
      return none
    let spineNames := (closureIdx.map (fun i => finalNames[i]!.toString)).toList
    let stmt := (renameNestedBindersGo closureIdx.size stmt0).run' (1, spineNames)
    let univNames := ((Lean.collectLevelParams {} stmt).params.toList.map (·.toString))
    let baseOpts (o : Options) : Options :=
      o.setBool `pp.proofs true |>.setBool `pp.deepTerms true
        |>.setBool `pp.letVarTypes true |>.setNat `pp.maxSteps 5000000
    let renderers : List (String × (Options → Options)) :=
      [("plain", baseOpts),
       ("funBinderTypes", fun o => (baseOpts o).setBool `pp.funBinderTypes true),
       ("explicit", fun o =>
         ((((baseOpts o).setBool `pp.explicit true).setBool `pp.notation false)
           |>.setBool `pp.universes true).setBool `pp.fullNames true)]
    let mut sigTexts : Array (String × String) := #[]
    for (label, f) in renderers do
      let fmt ← withOptions f (Meta.ppExpr stmt)
      sigTexts := sigTexts.push (label, collapseToOneLine (fmt.pretty 100000))
    let introNames := closureIdx.map (fun i => finalNames[i]!.toString)
    let mut argNames : Array String := #[]
    let mut argsUsable := true
    for i in closureIdx do
      if !(isLets[i]!) && stack[i]!.bi.isExplicit then
        argNames := argNames.push (finalNames[i]!.toString)
        if !origKept[i]! then argsUsable := false
    return some { sigTexts, introNames, argNames, argsUsable, univNames }

/-- Rung T driver: proof-term-based extraction of ONE have (see the block
    comment above). Tried by `#extract_haves_iter_decl` when
    `extractOneHaveViaGoal`'s probe-replay variants are all exhausted.
    Returns the updated lines on commit, `none` (with logged reasons) otherwise. -/
private def extractOneHaveViaTerm
    (lines : Array String) (span : ThmSpan) (haveIdx : Nat) (haveName : String)
    (counter : Nat) : CommandElabM (Option (Array String)) := do
  let (proofBody, relEnd) := extractHaveBody lines haveIdx
  let haveLineText := lines[haveIdx]!
  let isBulletAttached := haveLineText.trimLeft.startsWith "· "
  let bulletIndentStr := String.mk (List.replicate (lineIndent haveLineText) ' ')
  let haveBlockText := "\n".intercalate (lines.extract haveIdx relEnd).toList
  let topSplit := splitAtTopLevelAssign haveBlockText
  let isTacticHave := match topSplit with
    | some (_, body) =>
      let b := body.trimLeft
      b == "by" || b.startsWith "by " || b.startsWith "by\n"
    | none => false
  let headerBeforeAssign := match topSplit with
    | some (h, _) => h.trimRight
    | none        => haveLineText.trimRight
  let originalTypeText : String :=
    match (collapseToOneLine headerBeforeAssign).splitOn " : " with
    | _ :: rest => (" : ".intercalate rest).trim
    | []        => ""
  if originalTypeText.isEmpty then
    plogInfo s!"[term-extract] '{haveName}' skipped: no source type annotation"
    return none
  let termContinuation : String :=
    if isTacticHave then ""
    else
      match splitAtTopLevelAssign haveLineText.trimLeft with
      | some (_, body) =>
        match splitAtOuterSemi body.trimLeft with
        | some (_, cont) => cont.trim
        | none => ""
      | none => ""
  let nsPathT := enclosingNamespacePathFor lines span.headerStart
  let tempThmName := (if nsPathT.isEmpty then "" else nsPathT ++ ".") ++ s!"__term_probe_{counter}__"
  let headerText := "\n".intercalate (lines.extract span.headerStart span.bodyStart).toList
  let headerNoPriv :=
    if headerText.startsWith "private " then headerText.drop "private ".length else headerText
  let kw := if headerNoPriv.startsWith "theorem " then "theorem " else "lemma "
  let afterKw := headerNoPriv.drop kw.length
  let afterName := afterKw.drop span.name.length
  let renamedHeader := kw ++ tempThmName ++ afterName
  let opens := enclosingOpensFor lines span.headerStart
  let openPrefix := if opens.isEmpty then "" else "open " ++ " ".intercalate opens ++ " in\n"
  let setOptPrefix :=
    (enclosingSetOptionsFor lines span.headerStart).foldl
      (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") ""
  let ambientPrefix := setOptPrefix ++ openPrefix ++
    (enclosingVariablesFor lines span.headerStart).foldl (fun acc v => acc ++ v ++ " in\n") ""
  let classicalPrefix :=
    -- decl-scoped `open ... in` names must be BAKED into written lemmas
    -- (splices land above the `open ... in` line — see declScopedOpensFor)
    (let dOpens := declScopedOpensFor lines span.headerStart
     if dOpens.isEmpty then "" else "open " ++ " ".intercalate dOpens ++ " in\n") ++
    (if (maskCommentLines (lines.extract span.bodyStart span.bodyEnd)).toList.any
        (fun l => l.trim == "classical") then
      "open scoped Classical in\n"
    else "")
  let lemmaPrefix := setOptPrefix ++ openPrefix ++ classicalPrefix
  let externalName := span.name ++ "_aux_" ++ haveName
  -- ── the one full-declaration elaboration ──
  let bodyText := "\n".intercalate (lines.extract span.bodyStart span.bodyEnd).toList
  let probeSrc := ambientPrefix ++ renamedHeader ++ "\n" ++ bodyText
  let info? ← elabGetDeclInfo probeSrc tempThmName.toName
  match info? with
  | none =>
    -- diagnose only on failure (a second elaboration, but the failure path
    -- is where the evidence matters — the rejection-reasons rule)
    let err? ← elabCheckFirstError probeSrc
    plogInfo s!"[term-extract] '{haveName}' decl probe yielded no info: {((err?.getD "no error message").take 300)}"
    return none
  | some info =>
    match info.value? with
    | none =>
      plogInfo s!"[term-extract] '{haveName}' decl probe has no stored value"
      return none
    | some val =>
      match findHaveRedexStack haveName val #[] with
      | none =>
        plogInfo s!"[term-extract] '{haveName}' redex not found in the stored proof term"
        return none
      | some (stack, tyL, vL) =>
        let res? ← liftTermElabM (buildTermClosure stack tyL vL proofBody originalTypeText)
        match res? with
        | none =>
          plogInfo s!"[term-extract] '{haveName}' closure construction failed"
          return none
        | some r =>
          -- collision-proof universe names for the WRITTEN lemma (the #36
          -- class-7 lesson): rename after assembly so gate and file see
          -- identical text; longest-first so `u_1` never clobbers `u_10`
          let univSorted := (r.univNames.toArray.qsort (fun a b => a.length > b.length)).toList
          let renU (s : String) : String :=
            univSorted.foldl (fun acc nm => acc.replace nm ("ul" ++ nm.drop 1)) s
          let univSpecRaw :=
            if r.univNames.isEmpty then ""
            else ".{" ++ ", ".intercalate r.univNames ++ "}"
          let introLine :=
            if r.introNames.isEmpty then ""
            else "  intro " ++ " ".intercalate r.introNames.toList ++ "\n"
          let proofPart :=
            if isTacticHave then
              " := by\n" ++ introLine ++
              "\n".intercalate ((proofBody.splitOn "\n").map (fun l => "  " ++ l))
            else
              " := by\n" ++ introLine ++ "  exact (" ++ collapseToOneLine proofBody ++ ")"
          -- callsite variants: positional-by-name first (every closure binder
          -- is, by construction, a source binder in scope at the callsite),
          -- then the type-directed zero-args form
          let callV1? : Option String :=
            if r.argsUsable then
              some (if r.argNames.isEmpty then "(" ++ externalName ++ ")"
                    else "(" ++ externalName ++ " " ++ " ".intercalate r.argNames.toList ++ ")")
            else none
          let callV2 := "by apply " ++ externalName ++ " <;> assumption"
          let calls : List String :=
            (match callV1? with | some c => [c] | none => []) ++ [callV2]
          let oneLinerIndent := bulletIndentStr ++ (if isBulletAttached then "  " else "")
          let mut declDumped := false
          for (label, sigText) in r.sigTexts do
            -- SHIPPED-ERROR GATES (the Switching.lean lesson, #51): a printed
            -- signature can (a) reference a MATCH-COMPILER AUXILIARY
            -- (`<thm>.match_N`) — resolvable in the probe env via the IMPORTED
            -- compiled module, but a forward/unstable reference in the
            -- standalone written file (probes are blind to the difference:
            -- imported-env vs in-file-env); or (b) contain a pp-elided proof
            -- rendered as `sorry` inside a let-value — the lemma ELABORATES
            -- (sorry is a valid term) so every gate passes, while the written
            -- callsite becomes unsatisfiable. Both are text-detectable and
            -- both rejections are safe-direction (a lost conversion, never
            -- shipped breakage).
            if containsWord sigText "sorry" || (sigText.splitOn ".match_").length ≥ 2 ||
               (sigText.splitOn "._simp_").length ≥ 2 || (sigText.splitOn "._proof_").length ≥ 2 || (sigText.splitOn "._eq_").length ≥ 2 then
              plogInfo s!"[term-extract] '{haveName}' rendering {label} rejected: printed sig carries sorry/match-aux"
            -- SORRY-IN-PROOF GATE (#58, Derandomization checkpoint, 16
            -- shipped errors): rung T's PRINTED PROOF can carry pp-elided
            -- instance terms rendered as `sorry` (`fun ω => sorry`,
            -- `∑ i, sorry` — Decidable instances) — the sig-only sorry
            -- gate is blind to them and sorry elaborates green in probes.
            else if containsWord proofPart "sorry" then
              plogInfo s!"[term-extract] '{haveName}' rendering {label} rejected: printed PROOF carries sorry"
            -- SELF-RECURSION GATE (#56): the printed term of a
            -- `termination_by` decl's recursive have carries the decl's own
            -- (qualified) name — forward reference once spliced above it.
            else if containsWord proofPart span.name || containsWord sigText span.name then
              plogInfo s!"[term-extract] '{haveName}' rendering {label} rejected: self-recursive (references enclosing decl '{span.name}')"
            else
            for call in calls do
              let lemmaText := renU (setOptPrefix ++ classicalPrefix ++
                "private lemma " ++ externalName ++ univSpecRaw ++ " : " ++ sigText ++ proofPart)
              let oneLiner := oneLinerIndent ++ "have " ++ haveName ++ " : " ++
                collapseToOneLine originalTypeText ++ " := " ++ call
              let replacementLines : Array String :=
                (if isBulletAttached then #[bulletIndentStr ++ "·"] else #[]) ++
                (if termContinuation.isEmpty then #[oneLiner]
                 else #[oneLiner, oneLinerIndent ++ termContinuation])
              let newLines := lines.extract 0 haveIdx ++ replacementLines ++
                lines.extract relEnd lines.size
              let lemmaLines := (lemmaText.splitOn "\n").toArray
              let insAt := spliceLineAbove newLines span.headerStart
              let finalLines := newLines.extract 0 insAt ++ lemmaLines ++ #[""] ++
                newLines.extract insAt newLines.size
              let newBodyEnd := span.bodyEnd - (relEnd - haveIdx) + replacementLines.size
              let gateDecl := ambientPrefix ++ renamedHeader ++ "\n" ++
                "\n".intercalate (newLines.extract span.bodyStart newBodyEnd).toList
              match ← elabCheckFirstErrorSeq [lemmaPrefix ++ lemmaText, gateDecl] with
              | none =>
                elabPersistCommand (lemmaPrefix ++ lemmaText)
                plogInfo s!"[term-extract] '{haveName}' COMMITTED (render {label}, call {if callV1?.isSome && call != callV2 then "positional" else "apply-assumption"})"
                return some finalLines
              | some err =>
                plogInfo s!"[term-extract] '{haveName}' rejected (render {label}): {err.take 300}"
                plogInfo s!"[term-extract] '{haveName}' lemma text: {(collapseToOneLine lemmaText).take 2500}"
                if !declDumped then
                  declDumped := true
                  plogInfo s!"[term-extract] '{haveName}' decl text: {(collapseToOneLine gateDecl).take 2500}"
          plogInfo s!"[term-extract] '{haveName}' all renderings/callsites exhausted"
          return none

/-- Inject `term` into bare `linarith`/`nlinarith` calls in `line` (only ones
    with no explicit `[...]`/`only` list already — naive appending onto those
    would produce `linarith [t] [xs]`). These tactics consume the local
    context implicitly, so a fact REMOVED from the context by have-elimination
    must be re-supplied explicitly or they lose it. `nlinarith` is processed
    first; the later `linarith` pass can't re-match inside the result because
    `replaceWord` requires word boundaries and `nlinarith`'s leading `n` is an
    identifier character. -/
private def injectIntoLinarithCalls (line term : String) : String := Id.run do
  let mut out := line
  for kw in ["nlinarith", "linarith"] do
    if containsWord out kw &&
       (out.splitOn (kw ++ " [")).length < 2 &&
       (out.splitOn (kw ++ " only")).length < 2 then
      out := replaceWord out kw (kw ++ " [" ++ term ++ "]")
  return out

/-- The shared probe-context construction for FINAL-pass declaration probes:
    ambient prefixes (`set_option`s, `open`s, `variable`s — every kind of
    context a faithful probe must replay, per the bug-#31 saga), the
    declaration HEADER above the body-only `findAllDeclSpans` span (without it
    every trial fails at parse — the inert-verifier bug), with the declared
    name renamed (`__vtrial`, `private ` stripped) so probes neither collide
    with persisted declarations nor defeat by-name env lookups. Returns
    `(prefixText, headerText, declNm)`, or `none` when no header is found. -/
private def declProbeParts (lines : Array String) (bStart : Nat) :
    Option (String × String × String) := Id.run do
  let openPrefix :=
    match enclosingOpensFor lines bStart with
    | [] => ""
    | opens => "open " ++ " ".intercalate opens ++ " in\n"
  let setOptPrefix := (enclosingSetOptionsFor lines bStart).foldl
    (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") ""
  let varPrefix := (enclosingVariablesFor lines bStart).foldl
    (fun acc v => acc ++ v ++ " in\n") ""
  let prefixText := setOptPrefix ++ openPrefix ++ varPrefix
  let declKws : List String := ["private theorem ", "private lemma ", "theorem ", "lemma "]
  let headerStart := Id.run do
    let mut k := bStart
    while k > 0 do
      k := k - 1
      let l := lines[k]!
      if !l.startsWith "  " && declKws.any l.startsWith then
        return k
    return bStart
  if headerStart == bStart then return none
  let declNm : String := Id.run do
    let l := lines[headerStart]!
    match declKws.find? l.startsWith with
    | none => return ""
    | some kw =>
      let rest := l.drop kw.length
      let stop := rest.find (fun c => c == ' ' || c == '(' || c == '{' || c == '[' || c == ':' || c == '⦃')
      let nm := String.Pos.Raw.extract rest ⟨0⟩ stop
      -- a universe-spec'd name (`foo.{ul_1, ...}`) stops the scan at `{`,
      -- leaving a trailing dot — strip it (aux lemmas from earlier
      -- extractions carry specs, and their INNER haves were unreachable:
      -- every probe parse-failed on the mangled rename)
      return if nm.endsWith "." then nm.dropRight 1 else nm
  let renameHeaderLine (l : String) : String :=
    let l := if l.startsWith "private " then l.drop "private ".length else l
    match (["theorem ", "lemma "] : List String).find? l.startsWith with
    | none => l
    | some kw =>
      let rest := l.drop kw.length
      let stop := rest.find (fun c => c == ' ' || c == '(' || c == '{' || c == '[' || c == ':' || c == '⦃')
      let nm := String.Pos.Raw.extract rest ⟨0⟩ stop
      -- universe-spec'd names: `foo.{ul_1} ...` must become
      -- `foo__vtrial.{ul_1} ...`, NOT `foo.__vtrial{ul_1}` (parse garbage —
      -- this silently made the whole ladder inert for every aux lemma with
      -- a spec, 0-msg probe failures throughout)
      if nm.endsWith "." then
        kw ++ nm.dropRight 1 ++ "__vtrial." ++ rest.drop nm.length
      else
        kw ++ nm ++ "__vtrial" ++ rest.drop nm.length
  let headerText :=
    match (lines.extract headerStart bStart).toList with
    | h :: rest => "\n".intercalate (renameHeaderLine h :: rest) ++ "\n"
    | [] => ""
  return some (prefixText, headerText, declNm)

/-- `convertHavesToLet`'s `simp_all +decide`/specialize-use guard is a BLANKET,
    conservative refusal — the text alone can't tell whether a specific
    one-liner `have` is safe to transform. Rather than accepting that refusal,
    this pass empirically tries a LADDER of candidate transformations per
    blocked have (most have-eliminating first), re-elaborating the WHOLE
    containing declaration via `elabCheckOk` for each, and committing the
    first that verifies clean.

    WHY a ladder, not just have→let — the `simp_all` fixpoint semantics: a
    hypothesis participating in `simp_all` plays two distinct roles. (1) As a
    REWRITE RULE applied to the goal and the other hypotheses — this role
    survives the have's removal if the underlying term is re-supplied
    explicitly in the simp set (`simp_all [.., (term)]`), since simp treats
    hypothesis-rules and argument-rules alike when rewriting OTHERS. (2) As a
    TARGET being itself iteratively simplified by the other hypotheses, with
    the MUTATED form then used (by later `simp_all` passes, `at h` tactics,
    `convert h`, ...) — this role has no textual substitute: an injected
    argument is a fixed term, not a fixpoint participant, so only a real
    context binder preserves it. Which role dominates for a given have is
    undecidable from text — but trivially decidable by the elaborator, so:
    · Candidate A0 (full elimination, no injections), A (full elimination +
      term injection into `simp_all`/`linarith`), B (let + name injection),
    · C (plain let) — tried in that order, first verified wins.
    Injection scope ends at the first less-indented nonblank line. Runs AFTER
    `convertHavesToLet`, so everything still literally `have` here is exactly
    the guard-blocked set. Blanking (not deleting) the have line keeps the
    array size constant (see the stale-`bEnd` crash at the call site). -/
private def verifyAndConvertBlockedHaves
    (lines : Array String) (bStart bEnd : Nat) : CommandElabM (Array String) := do
  let some (prefixText, headerText, declNm) := declProbeParts lines bStart
    | return lines
  -- USAGE ORACLE: elaborate the UNMODIFIED declaration once and walk its
  -- stored proof term for have-redex consumption verdicts (see
  -- `collectHaveRedexUsage`). This detects "taken in through `simp_all`"
  -- directly — the reconstructed proof references exactly the hypotheses the
  -- tactic needed, even though its SYNTAX names none of them. The verdict is
  -- logged with each ladder outcome and doubles as a baseline sanity check
  -- that the probe context itself is sound (if the unmodified decl doesn't
  -- elaborate in the probe, every rejection below is suspect — the inert-
  -- verifier lesson).
  let baselineText := prefixText ++ headerText ++
    "\n".intercalate ((lines.extract bStart bEnd).toList)
  let usageMap : Array (Name × Bool) ←
    if declNm.isEmpty then pure #[]
    else do
      match ← elabGetDeclInfo baselineText (Name.mkSimple (declNm ++ "__vtrial")) with
      | some info =>
        match info.value? with
        | some val => pure (collectHaveRedexUsage val #[])
        | none => pure #[]
      | none => pure #[]
  let usageVerdict (h : String) : String :=
    match usageMap.find? (fun (n, _) => n.eraseMacroScopes.toString == h) with
    | some (_, true) => "USED"
    | some (_, false) => "UNUSED"
    | none => "unknown"
  -- Rung D's aux2 lemmas must land in the WRITTEN FILE, not merely in the
  -- probe environment: the first committed D persisted its lemma (so the gate
  -- and all later probes resolved it) but never spliced it into `lines` — the
  -- written output then failed with "Unknown identifier ..._aux2_hj" at the
  -- callsite. The #36 lesson yet again: check-context ≠ write-context.
  -- Accumulate here; spliced above the declaration header at return.
  let mut pendingLemmas : Array String := #[]
  let mut lines := lines
  for i in [bStart:bEnd] do
    let l := lines[i]!
    let lt := l.trimLeft
    -- A SINGLE-LINE tactic have (`have h : T := by positivity`) is a complete
    -- term once parenthesized (`(by positivity)`), so the ladder — rung E's
    -- tail-lift especially — handles it exactly like a one-liner call; only
    -- MULTI-line by-blocks (the next nonblank line still inside the block)
    -- stay excluded. Hedge.lean's last two binders (`hlhs_nn := by
    -- positivity`) were invisible to the whole ladder purely because of the
    -- blanket `:= by` filter.
    let isByHave := (lt.splitOn ":= by").length ≥ 2
    let byIsSingleLine := !isByHave || Id.run do
      for j in [i+1:bEnd] do
        if !isBlankLine lines[j]! then
          return lineIndent lines[j]! ≤ lineIndent l
      return true
    if lt.startsWith "have " && (lt.splitOn ":=").length ≥ 2 && byIsSingleLine then
      let indentStr := String.mk (l.toList.takeWhile Char.isWhitespace)
      let haveIndent := lineIndent l
      let afterHave := lt.drop "have ".length
      let nameStop  := afterHave.find (fun c => c == ' ' || c == ':' || c == '=')
      let hName     := String.Pos.Raw.extract afterHave ⟨0⟩ nameStop
      -- RHS term and any same-line `;`-continuation tactics after it.
      let rhs := match lt.splitOn ":=" with
        | _ :: rest => (":=".intercalate rest).trim
        | [] => ""
      -- a same-line `;` after `by` belongs INSIDE the by-block — no outer split
      let (termText, contText) :=
        if isByHave then (rhs, "")
        else match splitAtOuterSemi rhs with
          | some (t, c) => (t.trim, c.trim)
          | none => (rhs, "")
      let paren := "(" ++ termText ++ ")"
      -- Injections/references can't outlive the have's block: stop at the
      -- first nonblank line indented LESS than the have itself.
      let scopeEnd := Id.run do
        for j in [i+1:bEnd] do
          if !isBlankLine lines[j]! && lineIndent lines[j]! < haveIndent then
            return j
        return bEnd
      let letLine := indentStr ++ "let" ++ lt.drop "have".length
      let contLine :=
        if contText.isEmpty then ""
        else indentStr ++ (if containsWord contText hName then replaceWord contText hName paren else contText)
      -- Sharing guard (anti-blowup), mirroring `inlineOneLiners`': candidates
      -- A0/A copy `paren` into EVERY textual occurrence in scope — and with a
      -- large accumulated call term that trades one binder for kilobytes of
      -- duplicated text (observed: a 63,814-char `rw [(...)]` line produced
      -- by rung A after upstream inlining had grown `hsq`'s term; the probe
      -- only checks that the result COMPILES, not that it's sane). When the
      -- expansion exceeds the budget, skip the inlining rungs — B/C keep the
      -- binder as a `let`, which preserves sharing.
      let occCount := Id.run do
        let mut n := if contText.isEmpty then 0
                     else (contText.splitOn hName).length - 1
        for j in [i+1:scopeEnd] do
          n := n + ((lines[j]!.splitOn hName).length - 1)
        return n
      let inlineOversized := occCount * paren.length > 400
      -- Candidate A0 — delete the have with NO injections at all (explicit
      -- name references still inlined to the parenthesized term). This is the
      -- correct move for the two shapes the injection-based candidates MISS:
      -- a have `simp_all` merely PROCESSED but never needed (proof-term
      -- verdict UNUSED — injecting its term can itself derail simp, where
      -- plain removal succeeds), and a have `simp_all` used only because it
      -- was AVAILABLE but can rederive without (USED per the proof term, yet
      -- removable — usage ≠ necessity). Tried first since it eliminates the
      -- most; the empirical check, not the oracle, is still the committer.
      let candA0 : Option (Array String) :=
        if hName.isEmpty || termText.isEmpty || inlineOversized then none
        else Id.run do
          let mut t := lines.set! i contLine
          for j in [i+1:scopeEnd] do
            let lj := t[j]!
            if containsWord lj hName then
              t := t.set! j (replaceWord lj hName paren)
          return some t
      let candA : Option (Array String) :=
        if hName.isEmpty || termText.isEmpty || inlineOversized then none
        else Id.run do
          let mut t := lines.set! i contLine
          for j in [i+1:scopeEnd] do
            let lj := t[j]!
            let lj' :=
              if containsWord lj hName then replaceWord lj hName paren
              else injectIntoLinarithCalls (injectIntoSimpCalls lj paren) paren
            t := t.set! j lj'
          return some t
      let candB : Option (Array String) :=
        if hName.isEmpty then none
        else Id.run do
          let mut t := lines.set! i letLine
          for j in [i+1:scopeEnd] do
            let lj := t[j]!
            if !containsWord lj hName then
              t := t.set! j (injectIntoLinarithCalls (injectIntoSimpCalls lj hName) hName)
          return some t
      let candC : Array String := lines.set! i letLine
      let cands : List (String × Array String) :=
        (candA0.toList.map (fun c => ("A0", c))) ++
        (candA.toList.map (fun c => ("A", c))) ++
        (candB.toList.map (fun c => ("B", c))) ++ [("C", candC)]
      let usage := usageVerdict hName
      let mut committed := false
      for (tag, cand) in cands do
        if !committed then
          let trialDeclText := headerText ++ "\n".intercalate (cand.extract bStart bEnd).toList
          match ← elabCheckFirstError (prefixText ++ trialDeclText) with
          | none =>
            plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand {tag} COMMITTED"
            lines := cand
            committed := true
          | some err =>
            -- Deliberate diagnostic (not temporary debug noise): a candidate the
            -- elaborator rejects is INFORMATION — seeing the real reason is how
            -- probe-context mismatches (heartbeats, autoImplicit, opens, ...)
            -- get caught instead of silently masquerading as "genuinely unsafe".
            plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand {tag} rejected: {err.take 240}"
      -- Rung E — TAIL LIFTING (λ-lift the binder into a lemma PARAMETER).
      -- `have h : T := v; ⟨tail⟩` is the SAME PROOF as `exact (aux_tail args
      -- v)` where aux_tail binds `h` as a real parameter and its body is the
      -- tail verbatim: every consumer — `simp_all` fixpoints, `cases`
      -- specialization, `at h` mutations — sees `h` as an fvar hypothesis in
      -- BOTH forms, so the target-role/entanglement walls that block A0-D
      -- don't exist here by construction. The binder disappears from the
      -- theorem entirely (the goal: no haves, not just verified ones). The
      -- revert-probe's captured signature IS the needed lemma signature:
      -- `(params) (h : T) : G` with G the goal right after the have.
      if !committed && !hName.isEmpty then
        let baseIndentStrE := String.mk (List.replicate (lineIndent lines[bStart]!) ' ')
        let mut committedE := false
        -- the 4th rendering is maximally explicit: `pp.explicit` spells out
        -- instance/implicit arguments (curing `OfNat (Fin ?m)` stuck-instance
        -- drops on Fin-indexed goals) and `pp.proofs` prints proof terms
        -- instead of `⋯` (curing "don't know how to synthesize placeholder
        -- for argument `isLt`" on elided Fin.mk bounds) — verbose, but every
        -- rendering faces the same empirical gate
        for renderPrefix in ["",
            "set_option pp.funBinderTypes true in\n",
            "set_option pp.fullNames true in\nset_option pp.notation false in\nset_option pp.funBinderTypes true in\n",
            "set_option pp.explicit true in\nset_option pp.proofs true in\n"] do
         if !committedE then
          let synthetic := renderPrefix ++ prefixText ++ headerText ++
            "\n".intercalate ((lines.extract bStart (i+1)).toList) ++ "\n" ++
            indentStr ++ "revert " ++ hName ++ "\n" ++
            indentStr ++ "extract_goal using __sig__\n" ++
            indentStr ++ "sorry\n" ++
            baseIndentStrE ++ "all_goals sorry\n"
          let msgs ← captureWithDependencyRetry lines prefixText synthetic
          match findExtractedSignature msgs with
          | none =>
            match msgs.find? (fun mg => (mg.splitOn "error").length ≥ 2) with
            | some e => plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand E capture failed: {e.take 240}"
            | none =>
              -- 0 msgs = the synthetic PARSE-failed (elabCaptureMessages
              -- returns #[] on parse errors) — show the cut window, since a
              -- parse failure leaves no message to quote
              let cutWindow := Id.run do
                let upto := prefixText ++ headerText ++
                  "\n".intercalate ((lines.extract bStart (i+1)).toList)
                let s := upto.takeRight 200
                return s.replace "\n" " ⏎ "
              plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand E capture failed ({msgs.size} msgs); cut window: ...{cutWindow}"
          | some sig0 =>
            let sig := sig0.replace "ℕ" "Nat"
            let (univSpecE, sig) :=
              if sig.startsWith "__sig__.{" then
                match (sig.drop "__sig__".length).splitOn "}" with
                | spec :: rest => (spec ++ "}", "__sig__" ++ "}".intercalate rest)
                | [] => ("", sig)
              else ("", sig)
            let _ := univSpecE  -- spec now derived from the assembled text below
            -- keep-h parse: ALL groups become lemma params; the call passes
            -- the have's own (parenthesized) term at h's position
            let restAfterName := sig.drop "__sig__".length
            let (groups, remainder) := scanBinderGroups restAfterName
            let goalTy := (remainder.trim.drop 1).trim  -- strip leading ':'
            if goalTy.isEmpty || !(groups.any (fun g =>
                 g.startsWith "(" &&
                 ((((collapseToOneLine ((g.drop 1).dropRight 1)).splitOn " : ").headD
                   "").trim.splitOn " ").contains hName)) then
              plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand E sig unparseable"
            else
              let fixedGroupsE := groups.map fun g =>
                if !g.startsWith "(" then g
                else
                  let inner := collapseToOneLine ((g.drop 1).dropRight 1)
                  match inner.splitOn " : " with
                  | nm :: rest =>
                    let capturedTy := " : ".intercalate rest
                    if (nm.trim.splitOn " ").contains hName then g
                    else
                      match findPriorOneLinerType lines bStart i nm.trim with
                      | some fixedTy =>
                        if fixedTy.length > capturedTy.length then
                          "(" ++ nm.trim ++ " : " ++ fixedTy ++ ")"
                        else g
                      | none => g
                  | _ => g
              let paramsTextE := fixedGroupsE.foldl (fun acc g => acc ++ " " ++ collapseToOneLine g) ""
              let callArgsE : List String := fixedGroupsE.toList.foldl (fun acc g =>
                if !g.startsWith "(" then acc
                else
                  let inner := collapseToOneLine ((g.drop 1).dropRight 1)
                  let names := (inner.splitOn " : " |>.headD "").trim.splitOn " " |>.filter (·.length > 0)
                  acc ++ names.map (fun nm => if nm == hName then paren else nm)) []
              let tailName := declNm ++ "_tail_" ++ hName
              let tailBody := Id.run do
                let mut acc : List String := if contText.isEmpty then [] else [contText]
                for j in [i+1:scopeEnd] do
                  let l := lines[j]!
                  if l.trim.isEmpty then acc := acc ++ [""]
                  else
                    let rel := lineIndent l - haveIndent
                    acc := acc ++ [String.mk (List.replicate (2 + rel) ' ') ++ l.trim]
                return acc
              -- derive the universe spec from the ASSEMBLED text: substituted
              -- one-liner param types can mention levels from OTHER captures'
              -- numbering, which extract_goal's own spec cannot know about
              -- (the #36 "unknown universe level ul_6" gap, hit by rung E on
              -- Entropy.lean)
              let rawLemmaText :=
                "private lemma " ++ tailName ++ paramsTextE ++ " : " ++
                collapseToOneLine goalTy ++ " := by\n" ++ "\n".intercalate tailBody
              -- collect BOTH `u_k` (fresh, to be renamed) and `ul_k`
              -- (already renamed — substituted one-liner types from earlier
              -- aux lemmas carry these) so the spec declares every level
              let univTokens : List String := Id.run do
                let chars := rawLemmaText.toList.toArray
                let n := chars.size
                let isIdentC (c : Char) := c.isAlphanum || c == '_'
                let mut res : List String := []
                let mut k := 0
                while k + 1 < n do
                  let boundary := k == 0 || !isIdentC chars[k-1]!
                  let isU := chars[k]! == 'u' && chars[k+1]! == '_'
                  let isUl := chars[k]! == 'u' && chars[k+1]! == 'l' &&
                              k + 2 < n && chars[k+2]! == '_'
                  if boundary && (isU || isUl) then
                    let dStart := if isU then k + 2 else k + 3
                    let mut e := dStart
                    while e < n && (chars[e]!).isDigit do e := e + 1
                    if e > dStart then
                      let tok := String.mk ((chars.extract k e).toList)
                      if !res.contains tok then res := res ++ [tok]
                      k := e
                    else k := k + 1
                  else k := k + 1
                return res
              let toUl (t : String) : String :=
                if t.startsWith "ul_" then t else "ul" ++ t.drop 1
              let freshTokens := univTokens.filter (fun t => !t.startsWith "ul_")
              let univSorted2 := freshTokens.toArray.qsort (fun a b => a.length > b.length) |>.toList
              let renameAll (s : String) : String :=
                univSorted2.foldl (fun acc t => acc.replace t (toUl t)) s
              let specNames := (univTokens.map toUl).eraseDups
              let fullSpec :=
                if specNames.isEmpty then ""
                else ".{" ++ ", ".intercalate specNames ++ "}"
              let auxTailText := renameAll <|
                "private lemma " ++ tailName ++ fullSpec ++ paramsTextE ++ " : " ++
                collapseToOneLine goalTy ++ " := by\n" ++ "\n".intercalate tailBody
              let newLinesE := Id.run do
                let mut t := lines.set! i (indentStr ++ "exact (" ++ tailName ++ " " ++
                  " ".intercalate callArgsE ++ ")")
                for j in [i+1:scopeEnd] do
                  t := t.set! j ""
                return t
              let lemmaPfxE :=
                (enclosingSetOptionsFor lines bStart).foldl
                  (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") "" ++
                (match enclosingOpensFor lines bStart with
                  | [] => ""
                  | opens => "open " ++ " ".intercalate opens ++ " in\n")
              let trialDeclTextE := headerText ++ "\n".intercalate (newLinesE.extract bStart bEnd).toList
              match ← elabCheckFirstErrorSeq [lemmaPfxE ++ auxTailText, prefixText ++ trialDeclTextE] with
              | none =>
                elabPersistCommand (lemmaPfxE ++ auxTailText)
                plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand E COMMITTED"
                lines := newLinesE
                pendingLemmas := pendingLemmas ++ (auxTailText.splitOn "\n").toArray ++ #[""]
                committedE := true
              | some err =>
                plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand E rejected: {err.take 240}"
        if committedE then
          committed := true
      -- Rung D — POST-MUTATION RE-EXTRACTION. A TARGET-role have (mutated in
      -- place via `at hName` tactics, its final form then consumed) defeats
      -- every candidate above: deletion moves the term past the mutations
      -- (type mismatch), and let-conversion breaks the `at`-mutations. But
      -- the have→lemma swap can be REDONE at the have's post-mutation point:
      -- capture the fully-mutated type there with a revert-probe (the window
      -- replayed verbatim, so the capture is faithful), build a SECOND aux
      -- lemma re-deriving that form — pure `at hName` lines replayed
      -- verbatim; context-wide `simp_all ...` rewritten to the targeted
      -- `simp ... [.., *] at hName` (same hypothesis-rules, no goal
      -- interference inside the lemma); other context-wide lines skipped —
      -- then move the one-liner to the post-mutation point (its captured
      -- args only exist in their post-mutation forms THERE) and delete the
      -- now-redundant pure `at hName` lines. Both pieces empirically gated.
      if !committed && !hName.isEmpty then
        let mutIdx? := Id.run do
          let mut r : Option Nat := none
          for j in [i+1:scopeEnd] do
            if (lines[j]!.splitOn ("at " ++ hName)).length ≥ 2 then
              r := some j
          return r
        match mutIdx? with
        | none => pure ()
        | some m =>
          let baseIndentStr := String.mk (List.replicate (lineIndent lines[bStart]!) ' ')
          -- same rendering-fallback ladder as the extraction branches: the
          -- default ppExpr render drops binder ascriptions, leaving stuck
          -- typeclass metavariables in aux2's params (observed on `hj` and
          -- the line-947 `h_anon_1` the first time rung D ran)
          let mut committedD := false
          for renderPrefix in ["",
              "set_option pp.funBinderTypes true in\n",
              "set_option pp.fullNames true in\nset_option pp.notation false in\nset_option pp.funBinderTypes true in\n"] do
           if !committedD then
            let synthetic := renderPrefix ++ prefixText ++ headerText ++
              "\n".intercalate ((lines.extract bStart (m+1)).toList) ++ "\n" ++
              indentStr ++ "revert " ++ hName ++ "\n" ++
              indentStr ++ "extract_goal using __sig__\n" ++
              indentStr ++ "sorry\n" ++
              baseIndentStr ++ "all_goals sorry\n"
            let msgs ← captureWithDependencyRetry lines prefixText synthetic
            match findExtractedSignature msgs with
            | none =>
              match msgs.find? (fun mg => (mg.splitOn "error").length ≥ 2) with
              | some e => plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand D capture failed: {e.take 240}"
              | none => plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand D capture failed ({msgs.size} msgs)"
            | some sig0 =>
              let sig := sig0.replace "ℕ" "Nat"
              let (univSpec, sig) :=
                if sig.startsWith "__sig__.{" then
                  match (sig.drop "__sig__".length).splitOn "}" with
                  | spec :: rest => (spec ++ "}", "__sig__" ++ "}".intercalate rest)
                  | [] => ("", sig)
                else ("", sig)
              let univNames := (if univSpec.isEmpty then [] else
                  ((univSpec.drop 2).dropRight 1).splitOn "," |>.map String.trim)
                |>.filter (·.length > 0)
              let univSorted := univNames.toArray.qsort (fun a b => a.length > b.length) |>.toList
              let renameU (s : String) : String :=
                univSorted.foldl (fun acc n => acc.replace n ("ul" ++ n.drop 1)) s
              let scrubU (s : String) : String :=
                univSorted.foldl (fun acc n =>
                  (acc.replace ("Type " ++ n) "Type _").replace ("Sort " ++ n) "Sort _") s
              match parseRevertedSignature sig hName with
              | none =>
                plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand D sig unparseable"
              | some (ty', callArgNames, paramsText0) =>
                -- bug #24's parameter-ascription substitution (span-bounded,
                -- see the extraction branches): a reverted-context param that
                -- is an EARLIER one-liner have re-renders with dropped
                -- ascriptions; its correct type text is that one-liner's own.
                let (pGroups, _) := scanBinderGroups paramsText0
                let paramsText := pGroups.foldl (init := "") fun acc g =>
                  let fixed :=
                    if !g.startsWith "(" then g
                    else
                      let inner := collapseToOneLine ((g.drop 1).dropRight 1)
                      match inner.splitOn " : " with
                      | nm :: rest =>
                        let capturedTy := " : ".intercalate rest
                        match findPriorOneLinerType lines bStart i nm.trim with
                        | some fixedTy =>
                          if fixedTy.length > capturedTy.length then
                            "(" ++ nm.trim ++ " : " ++ fixedTy ++ ")"
                          else g
                        | none => g
                      | _ => g
                  acc ++ " " ++ collapseToOneLine fixed
                -- pure `at hName` line: every `;`-chained segment targets hName
                let isPureAtH (l : String) : Bool := Id.run do
                  let mut rest := l.trim
                  let mut allAt := !rest.isEmpty
                  while !rest.isEmpty do
                    let (seg, cont) := match splitAtOuterSemi rest with
                      | some (s, c) => (s, c)
                      | none => (rest, "")
                    if !(seg.trim.endsWith ("at " ++ hName)) then
                      allAt := false
                    rest := cont
                  return allAt
                -- window replay inside aux2 (see the rung comment)
                let windowProof : List String := Id.run do
                  let mut acc : List String := []
                  for j in [i+1:m+1] do
                    let t := lines[j]!.trim
                    if t.isEmpty then pure ()
                    else if isPureAtH lines[j]! then
                      acc := acc ++ [t]
                    else if t.startsWith "simp_all" then
                      let rest0 := (t.drop "simp_all".length).trim
                      let rest := if rest0.endsWith ";" then (rest0.dropRight 1).trim else rest0
                      let core :=
                        if rest.endsWith "]" then
                          (rest.dropRight 1) ++ ", * ] at " ++ hName
                        else
                          rest ++ " [ * ] at " ++ hName
                      acc := acc ++ ["simp " ++ core]
                  return acc
                let aux2Name := declNm ++ "_aux2_" ++ hName
                let haveLineTrim := lt
                let proofLines :=
                  ([haveLineTrim] ++ windowProof ++ ["exact " ++ hName]).map ("  " ++ ·)
                let aux2Text := renameU <|
                  "private lemma " ++ aux2Name ++ univSpec ++ paramsText ++ " : " ++
                  collapseToOneLine ty' ++ " := by\n" ++ "\n".intercalate proofLines
                let call := if callArgNames.isEmpty then aux2Name
                            else "(" ++ aux2Name ++ " " ++ " ".intercalate callArgNames ++ ")"
                let newOneLiner := indentStr ++ "have " ++ hName ++ " : " ++
                  scrubU (collapseToOneLine ty') ++ " := " ++ call
                -- D1 deletes the original binder; D2 KEEPS it and SHADOWS
                -- the name at the post-mutation point instead — for the
                -- ENTANGLED shape where the have itself participates in the
                -- context-wide mutation (a simp_all fixpoint) that produces
                -- its final form: deleting it changes that very mutation, so
                -- the captured context and the trial context diverge
                -- (observed: line-947 `h_anon_1`, whose `hfar` argument
                -- mutated differently once the have was gone). The shadow
                -- keeps the fixpoint intact while the downstream consumers
                -- get the lemma-backed final form; the re-ladder pass can
                -- then attack the original binder, whose only remaining
                -- consumer is the mutation itself.
                let mkCand (keepOriginal : Bool) : Option (Array String) := Id.run do
                  -- slot `m` is only free to overwrite when it is a PURE
                  -- `at hName` line (about to be deleted anyway); a mixed
                  -- line (e.g. `simp ... at hName ⊢`) must survive, so skip.
                  if !isPureAtH lines[m]! then return none
                  let mut t := if keepOriginal then lines else lines.set! i ""
                  for j in [i+1:m+1] do
                    if isPureAtH t[j]! then
                      t := t.set! j ""
                  t := t.set! m newOneLiner
                  return some t
                let dCands : List (String × Array String) :=
                  ((mkCand false).toList.map (fun c => ("D", c))) ++
                  ((mkCand true).toList.map (fun c => ("D2", c)))
                for (dTag, cand) in dCands do
                 if !committedD then
                  let lemmaPfx :=
                    (enclosingSetOptionsFor lines bStart).foldl
                      (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") "" ++
                    (match enclosingOpensFor lines bStart with
                      | [] => ""
                      | opens => "open " ++ " ".intercalate opens ++ " in\n")
                  let trialDeclText := headerText ++ "\n".intercalate (cand.extract bStart bEnd).toList
                  match ← elabCheckFirstErrorSeq [lemmaPfx ++ aux2Text, prefixText ++ trialDeclText] with
                  | none =>
                    elabPersistCommand (lemmaPfx ++ aux2Text)
                    plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand {dTag} COMMITTED"
                    lines := cand
                    pendingLemmas := pendingLemmas ++ (aux2Text.splitOn "\n").toArray ++ #[""]
                    committedD := true
                  | some err =>
                    plogInfo s!"[have-ladder] '{hName}' line {i+1} usage={usage} cand {dTag} rejected: {err.take 240}"
  if pendingLemmas.isEmpty then
    return lines
  else
    -- splice committed aux2 lemmas immediately above the declaration header
    -- (mirrors declProbeParts' upward header scan)
    let declKws : List String := ["private theorem ", "private lemma ", "theorem ", "lemma "]
    let headerStart := Id.run do
      let mut k := bStart
      while k > 0 do
        k := k - 1
        let l := lines[k]!
        if !l.startsWith "  " && declKws.any l.startsWith then
          return k
      return bStart
    return lines.extract 0 headerStart ++ pendingLemmas ++ lines.extract headerStart lines.size

/--
One declaration's final-cleanup pass (heuristic inlining + verified ladder),
shared by the whole-file (`#extract_haves_iter_to`) and per-declaration
(`#extract_haves_iter_decl`) commands. Returns the updated lines and whether
the ladder SPLICED lemmas above the declaration — the caller must then
reprocess the same index (whole-file) or requeue by name (per-decl), since
the splice now occupies the declaration's old position.
-/
private def finalPassOneDecl (lines0 : Array String) (bStart bEnd : Nat) :
    CommandElabM (Array String × Bool) := do
  let mut lines := lines0
  let bodyLines := lines.extract bStart bEnd
  let processed := convertHavesToLet (inlineOneLiners bodyLines)
  -- `inlineOneLiners`/`convertHavesToLet` are the OLD pipeline's
  -- HEURISTIC passes — they commit textual transformations with NO
  -- verification, which was survivable while their inputs were the narrow
  -- shapes they were tuned on, but the newly-extracted typed one-liner
  -- calls (e.g. from anonymous-have extraction) can match their Case-A/E
  -- patterns and get inlined into `simp_all` argument lists in ways that
  -- break the proof (observed for real: an equation-typed `have h_anon_1
  -- : ... = 1 := (aux ...)` inlined into `simp_all [..., (aux ...)]` +
  -- `convert (aux ...)` produced "simp_all made no progress" in the
  -- written file). Gate them like everything else: verify the processed
  -- declaration; on failure, revert to the unprocessed body (the
  -- extraction output, which is verified at extraction time) and let the
  -- verified ladder below take its shot instead.
  let processed ←
    if processed == bodyLines then pure processed
    else
      match declProbeParts lines bStart with
      | none => pure processed
      | some (prefixText, headerText, _) => do
        let trial := prefixText ++ headerText ++ "\n".intercalate processed.toList
        if ← elabCheckOk trial then pure processed
        else do
          logInfo s!"[final-pass] heuristic inlining rejected for decl at line {bStart+1}; reverted to unprocessed body"
          pure bodyLines
  lines := lines.extract 0 bStart ++ processed ++ lines.extract bEnd lines.size
  -- `convertHavesToLet` only rewrites existing lines' text (never inserts/
  -- removes one), but `inlineOneLiners` (run first, above) CAN shrink the
  -- declaration via its full-elimination case — so the true end boundary
  -- after splicing is `bStart + processed.size`, NOT the original (now
  -- possibly-stale) `bEnd`. Using the stale `bEnd` here indexes past the
  -- array's new end for the LAST declaration in the file whenever this
  -- iteration shrank it — confirmed as a real crash ("index out of
  -- bounds"), not a hypothetical: this was live-tested on
  -- `ReproNestedHaveDirectTest.lean` and panicked the Lean interpreter.
  let newBEnd := bStart + processed.size
  let beforeLadder := lines
  lines ← verifyAndConvertBlockedHaves lines bStart newBEnd
  -- Rung D NORMALIZES a target-role have (post-mutation one-liner) rather
  -- than eliminating it — the normalized form may now be eliminable by
  -- the A0-C rungs, but this pass already moved past it. One re-run of
  -- the ladder when anything changed gives those a second look (committed
  -- lets/deletions from the first pass no longer match `have `, so the
  -- re-run only re-probes still-blocked haves). Rung D's aux2 splice
  -- inserts ABOVE the declaration header, shifting the body by the size
  -- delta — adjust both bounds for the second call.
  if lines != beforeLadder then
    let delta := lines.size - beforeLadder.size
    lines ← verifyAndConvertBlockedHaves lines (bStart + delta) (newBEnd + delta)
  return (lines, lines.size != beforeLadder.size)

/--
`#extract_haves_iter_to "src/File.lean" "dst/Output.lean"`

Like `#extract_haves_file_to`, but extracts `have`s one at a time (innermost
first) using `extract_goal` to derive each signature, instead of a single
up-front MetaM walk. See the section comment above for the rationale.
-/
elab "#extract_haves_iter_to " srcLit:str dstLit:str : command => do
  let inputPath  := srcLit.getString
  let outputPath := dstLit.getString
  letReplayEnabledRef.set false  -- whole-file runs can't afford it (see the ref's docstring)
  let src ← IO.FS.readFile inputPath
  probeAutoImplicitRef.set (!(((src.splitOn "\n").map String.trim).contains "set_option autoImplicit false"))
  -- LIVE PROGRESS: the InfoView only shows this command's messages when the
  -- WHOLE command finishes (one elaboration snapshot), so stream progress to
  -- a sidecar file (`tail -f <output>.progress`) and to the server's stderr
  -- (visible in VS Code's Lean output channel) instead.
  let progressPath := outputPath ++ ".progress"
  IO.FS.writeFile progressPath ""
  let progress (msg : String) : CommandElabM Unit := do
    IO.eprintln s!"[extract-haves] {msg}"
    IO.FS.withFile progressPath .append fun h => h.putStrLn msg
  progress s!"START {inputPath}"
  let mut lines := src.splitOn "\n" |>.toArray
  let mut counter := 0
  let mut succeeded := 0
  let mut debugLog : Array String := #[]
  let initialSpans := findTheorems lines
  for thmSpan0 in initialSpans do
    let thmName := thmSpan0.name
    -- Names to exclude from further consideration: both haves whose probe already
    -- FAILED (no point retrying the identical text) and haves already SUCCESSFULLY
    -- extracted. The latter is essential, not just an optimization: a successfully
    -- extracted have becomes a one-liner `have NAME : TYPE := (call)`, which still
    -- starts with `have ` and (having no further nested `have`) still qualifies as
    -- a "leaf" — so without exclusion, the tool would re-"extract" its own output
    -- forever, each time trying to redeclare the same `externalName`.
    let mut doneNames : List String := []
    let mut keepGoing := true
    while keepGoing do
      keepGoing := false
      let curSpans := findTheorems lines
      match curSpans.toList.find? (fun s => s.name == thmName) with
      | none => pure ()
      | some span =>
        lines := renameShadowedHaveNames lines span
        lines := nameAnonymousHaves lines span
        -- Mid-line haves are split onto their own lines BEFORE scanning —
        -- splitting GROWS the array, so `span` is stale afterward: commit the
        -- split and re-enter the loop (spans recompute at the top) rather
        -- than scanning against invalidated bounds.
        let (splitLines, didSplit) := splitMidLineHavesInSpan lines span
        if didSplit then
          lines := splitLines
          keepGoing := true
        else
          let headers := (findAllHaveHeaders lines span.bodyStart span.bodyEnd).filter
            (fun (_, n) => !doneNames.contains n)
          match findLeafHave lines headers doneNames with
          | none => pure ()
          | some (haveIdx, haveName) =>
            -- A have whose body already CALLS its own aux lemma is a
            -- previously-converted one-liner (`:= by apply *_aux_NAME ...`)
            -- re-read from the output file: re-extracting it would redeclare
            -- the same aux name ("has already been declared" — a permanent
            -- FAILED loop). Skip it as done.
            let marker := "_aux_" ++ haveName
            let alreadyConverted :=
              match lines[haveIdx]!.splitOn marker with
              | _ :: rest :: _ => rest.isEmpty || !isIdentChar (rest.get! 0)
              | _ => false
            if alreadyConverted then
              doneNames := haveName :: doneNames
              keepGoing := true
            else
            counter := counter + 1
            progress s!"attempt {counter}: {thmName}.{haveName} ..."
            match ← extractOneHaveViaGoal lines span haveIdx haveName counter with
            | none =>
              doneNames := haveName :: doneNames
              debugLog := debugLog.push s!"{thmName}:{haveName}:PROBE_FAILED"
              progress s!"attempt {counter}: {thmName}.{haveName} FAILED"
              keepGoing := true
            | some newLines =>
              lines := newLines
              doneNames := haveName :: doneNames
              succeeded := succeeded + 1
              progress s!"attempt {counter}: {thmName}.{haveName} EXTRACTED ({succeeded}/{counter})"
              keepGoing := true
  -- Extraction leaves a `have NAME : TYPE := (call)` one-liner in place for every
  -- SUCCESSFUL extraction — it pulls the PROOF out, but never eliminates the have
  -- statement itself. Reuse the OLD pipeline's inlining passes (already proven on
  -- `#extract_haves_file`) to collapse what's left: fold `have h := call; ...; exact h`
  -- down to `exact (call)` where the use is simple enough (Case A), or otherwise
  -- convert to `let h := call` (Case C) so `rw [...] at h`-style continuations still
  -- work without a bare `have`. Runs over EVERY top-level declaration (`findAllDeclSpans`,
  -- unlike `findTheorems`, does NOT skip `private` ones) — an extracted private lemma's
  -- own body can itself contain a now-inlineable have (e.g. a call to a SIBLING extracted
  -- lemma), and only gets this cleanup if it's included too. Recomputes spans fresh each
  -- iteration since `inlineOneLiners`'s full-elimination case shrinks the line count,
  -- shifting every later declaration's position.
  let mut declIdx := 0
  let mut moreDecls := true
  while moreDecls do
    let declSpans := findAllDeclSpans lines
    if declIdx < declSpans.size then
      let (bStart, bEnd) := declSpans[declIdx]!
      progress s!"final pass: decl {declIdx + 1}/{declSpans.size}"
      let (newLines, spliced) ← finalPassOneDecl lines bStart bEnd
      lines := newLines
      -- Spliced aux lemmas (rung E tails, rung D aux2s) occupy the CURRENT
      -- span index after insertion — hold declIdx so the next iteration
      -- processes THEM (their bodies carry the relocated haves; E can lift
      -- within them recursively, and termination holds because every commit
      -- strictly reduces the have count). Without this, an E-lifted tail
      -- lemma's internal one-liners were never ladder-processed (observed:
      -- ZkFourier's parseval tail kept h_substitute/h_inner_sum).
      if !spliced then
        declIdx := declIdx + 1
    else
      moreDecls := false
  progress s!"DONE attempts={counter} succeeded={succeeded} — writing {outputPath}"
  IO.FS.writeFile outputPath ("\n".intercalate lines.toList)
  logInfo s!"#extract_haves_iter_to: written to {outputPath} | attempts={counter} succeeded={succeeded} | {" ".intercalate debugLog.toList}"

/-- Persist every `private lemma`/`private theorem` present as TEXT in the
working file into the session env — a fresh server has no declarations for
aux lemmas committed by PREVIOUS invocations, and probes/gates that reference
them die at capture ("Unknown identifier `..._aux_...`").
Scans header LINES directly — NOT via `findAllDeclSpans`, which only records
`:= by` (tactic-mode) declarations and silently skips term-mode lemmas
(`... := term`); the very aux the probes kept dying on (`aux_hωm1`, 383
unknown-identifier errors in one run) was term-mode. And NOT via
`declProbeParts`'s headerText, which is RENAMED (`NAME__vtrial`, `private `
stripped) for probe use. Prefix is opens+set_options ONLY: ambient `Type*`
variable lines auto-declare `u_k` universes that COLLIDE with the aux
lemmas' explicit `.{ul_k}` specs (the same lemma-vs-probe distinction as
`lemmaPrefix`). The env canary checks `mkPrivateName` — private declarations
land MANGLED (`_private.<module>.0.name`). -/
private def persistFileAuxLemmas (lines : Array String)
    (progress : String → CommandElabM Unit) : CommandElabM Unit := do
  let mut persisted := 0
  let mut pi := 0
  -- ALSO persist private DEFS/ABBREVS: a privacy-heavy source file
  -- (Switching.lean: 51 private decls, with `private def parseAux` etc.
  -- referenced by nearly every theorem) makes EVERY probe and gate fail with
  -- "Unknown identifier" — Lean privacy is per-module, so the driver can
  -- never resolve them without a local copy. File order is dependency order
  -- for defs, so persisting in one forward sweep resolves chains (the same
  -- reason the private-LEMMA persists used to fail here: their bodies
  -- reference the defs, which were never persisted first).
  let kws : List String := ["private lemma ", "private theorem ", "private def ",
    "private noncomputable def ", "private abbrev "]
  -- Namespace tracking: a source file can reference its own private decls by
  -- FULLY-QUALIFIED name (`SwitchingLemma2.canonicalDTree_depth_zero_of_fixed`
  -- in Switching.lean line 1046) — an unqualified top-level copy can never
  -- satisfy that reference, wiping every probe of the containing decl. So
  -- copies of decls that live inside namespaces are persisted PUBLIC under
  -- their QUALIFIED name (privacy of a probe-session copy protects nothing,
  -- a public dotted name never collides with the imported module's mangled
  -- private original, and the probes' `open NS in` prefix still resolves the
  -- unqualified references exactly as before).
  let mlines := maskCommentLines lines
  let mut nsStack : List String := []
  while pi < lines.size do
    let l := lines[pi]!
    let t := mlines[pi]!.trim
    if t.startsWith "namespace " then
      nsStack := nsStack ++ [(t.drop "namespace ".length).trim]
      pi := pi + 1
    else if t.startsWith "end " && nsStack.getLast? == some ((t.drop "end ".length).trim) then
      nsStack := nsStack.dropLast
      pi := pi + 1
    else
    match kws.find? l.startsWith with
    | none => pi := pi + 1
    | some kw =>
      let mut pj := pi + 1
      while pj < lines.size && (lines[pj]!.startsWith "  " || lines[pj]!.trim.isEmpty) do
        pj := pj + 1
      let openPrefix :=
        match enclosingOpensFor lines pi with
        | [] => ""
        | opens => "open " ++ " ".intercalate opens ++ " in\n"
      let setOptPrefix := (enclosingSetOptionsFor lines pi).foldl
        (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") ""
      let afterKw := l.drop kw.length
      let nameTok := (((afterKw.splitOn " ").head!).splitOn ".{").head!
      -- Source-authored private decls can use ambient `variable`s (Trees.lean:
      -- `variable {X Y α : Type*}` — persists died with "Unknown identifier
      -- `α`"); replay them — but ONLY for spec-free decls: tool-authored aux
      -- lemmas carry explicit `.{ul_k}` specs that collide with variable-in
      -- auto-bound levels (the #36 class-6 hazard).
      let varPrefix :=
        if (((afterKw.splitOn " ").head!).splitOn ".{").length ≥ 2 then ""
        else (enclosingVariablesFor lines pi).foldl (fun acc v => acc ++ v ++ " in\n") ""
      let declText := "\n".intercalate ((lines.extract pi pj).toList)
      let (persistText, canaryName) :=
        if nsStack.isEmpty then
          (declText, nameTok)
        else
          let qual := ".".intercalate nsStack ++ "." ++ nameTok
          let kwPublic := kw.drop "private ".length
          let restAfterName := l.drop (kw.length + nameTok.length)
          let header := kwPublic ++ qual ++ restAfterName
          (header ++ (if pj > pi + 1 then "\n" ++
            "\n".intercalate ((lines.extract (pi+1) pj).toList) else ""), qual)
      elabPersistCommand (setOptPrefix ++ openPrefix ++ varPrefix ++ persistText)
      let nm := canaryName.toName
      let envNow ← getEnv
      if envNow.contains nm || envNow.contains (mkPrivateName envNow nm) then
        persisted := persisted + 1
      else
        progress s!"persist FAILED for {nm}"
      pi := pj
  if persisted > 0 then
    progress s!"persisted {persisted} pre-existing aux lemmas into the session env"

/--
`#extract_haves_iter_decl "src/File.lean" "dst/Output.lean" "declName"`

Per-DECLARATION variant of `#extract_haves_iter_to`, for out-of-band
driving: each invocation processes ONE declaration (matched by name) and
writes the whole file back to the output path. When the output file already
exists it is the INPUT — progress accumulates across invocations (the
source path is only read the first time). Restart the server between
invocations: that resets elaboration memory, which is what makes the
LET-REPLAY machinery affordable — it is enabled for this command only.
The progress sidecar is opened in APPEND mode (never truncated) so a
multi-declaration campaign keeps one continuous log.
-/
elab "#extract_haves_iter_decl " srcLit:str dstLit:str declLit:str : command => do
  let inputPath  := srcLit.getString
  let outputPath := dstLit.getString
  let declName   := declLit.getString
  letReplayEnabledRef.set true
  let outExists ← System.FilePath.pathExists outputPath
  let readPath := if outExists then outputPath else inputPath
  let src ← IO.FS.readFile readPath
  let progressPath := outputPath ++ ".progress"
  probeLogPathRef.set (some (outputPath ++ ".probelog"))
  let progress (msg : String) : CommandElabM Unit := do
    IO.eprintln s!"[extract-haves] {msg}"
    IO.FS.withFile progressPath .append fun h => h.putStrLn msg
  progress s!"START-DECL {declName} (input: {readPath})"
  let mut lines := src.splitOn "\n" |>.toArray
  -- probe autoImplicit mode follows the SOURCE file (see the ref's docstring):
  -- forced OFF only when the file turns it off itself; ON for files that rely
  -- on auto-binding (Circuit.lean's `(c : Circuit n)` with no `variable`).
  probeAutoImplicitRef.set (!(lines.any (fun l => l.trim == "set_option autoImplicit false")))
  -- PRIVATE DEPS FROM IMPORTED MODULES (#52 follow-up): a decl can reference
  -- a private lemma of an IMPORTED file (dtDepth_le_implies_small_dnf_cnf →
  -- `canonicalDTree_depth_zero_of_fixed`, private in
  -- Switching/CanonicalDTree.lean) — per-module privacy makes it
  -- unresolvable in every probe AND gate, wiping the decl. Persist private
  -- decls from directly imported TCSlib modules first (one level, file
  -- order = dependency order within each module; best-effort).
  for l in lines do
    if l.startsWith "import TCSlib." then
      let modPath := ((l.drop "import ".length).trim.replace "." "/") ++ ".lean"
      if ← System.FilePath.pathExists modPath then
        let msrc ← IO.FS.readFile modPath
        persistFileAuxLemmas (msrc.splitOn "\n").toArray progress
  -- Aux lemmas committed by PREVIOUS invocations exist only as TEXT in the
  -- working file — this fresh server has no declarations for them, and the
  -- target's prefix references them via one-liner calls, so every probe
  -- dies at capture ("Unknown identifier `..._aux_...`", observed on the
  -- second per-decl run). Persist each into the session env up front,
  -- exactly as extraction-time commits do.
  persistFileAuxLemmas lines progress
  let mut counter := 0
  let mut succeeded := 0
  -- Target lookup that ALSO accepts `private` declarations: `findTheorems`
  -- skips them by design (whole-file iteration), but per-decl campaigns must
  -- reach the haves living inside SPLICED aux lemmas (rung E tails, rung D
  -- aux2s) — extraction never targeted those otherwise.
  let findAnySpan (lns : Array String) (nm : String) : Option ThmSpan := Id.run do
    match (findTheorems lns).find? (fun s => s.name == nm) with
    | some s => return some s
    | none =>
      let mut i := 0
      while i < lns.size do
        let l := lns[i]!
        if l.startsWith "private lemma " || l.startsWith "private theorem " then
          let rest :=
            if l.startsWith "private lemma " then l.drop "private lemma ".length
            else l.drop "private theorem ".length
          let nameEnd := rest.find (fun c => c == ' ' || c == '{' || c == '(' || c == ':' || c == '.')
          let name := String.Pos.Raw.extract rest ⟨0⟩ nameEnd
          if name == nm then
            let mut j := i
            let mut found := false
            while j < lns.size && !found do
              if (lns[j]!.splitOn ":= by").length ≥ 2 then found := true
              else
                j := j + 1
                if j < lns.size && !isBlankLine lns[j]! && lineIndent lns[j]! == 0 && j > i then
                  j := lns.size
            if found then
              let bodyStart := j + 1
              return some { name := nm, fullName := nm, headerStart := i,
                            bodyStart, bodyEnd := blockEnd lns bodyStart 0 }
            else
              return none
        i := i + 1
      return none
  -- ── extraction loop, restricted to the one named declaration ──
  let mut doneNames : List String := []
  let mut keepGoing := true
  -- BASELINE PROBE (#56): elaborate the UNMODIFIED decl in the gate context
  -- once, before any attempt. SATTo3SAT's transformClause_soundness fails
  -- this: a `let`-match inside the theorem REUSES an earlier in-file
  -- definition's matcher constant when elaborated in-file, but mints a
  -- FRESH matcher in the probe env (module imported) — leaving `X = X`
  -- goals between pp-identical-but-DISTINCT matcher constants that `simp`'s
  -- rfl-closing cannot equate. Such a decl is in-file-only elaborable:
  -- every gate falsely rejects (safe direction, nothing ships), so burn
  -- zero attempts and report the real reason instead of N misleading
  -- per-have errors (and instead of blaming the pre-pass renames, whose
  -- revert-gate probe fails for the same baseline reason).
  match findAnySpan lines declName with
  | none => pure ()
  | some span =>
    let headerText0 := "\n".intercalate (lines.extract span.headerStart span.bodyStart).toList
    let headerText :=
      if headerText0.startsWith "private " then headerText0.drop "private ".length else headerText0
    let kw := if headerText.startsWith "theorem " then "theorem " else "lemma "
    let nsPathB := enclosingNamespacePathFor lines span.headerStart
    let renHdr := kw ++ (if nsPathB.isEmpty then "" else nsPathB ++ ".") ++ "__baseline_check__" ++ ((headerText.drop kw.length).drop span.name.length)
    let opens := enclosingOpensFor lines span.headerStart
    let openPfx := if opens.isEmpty then "" else "open " ++ " ".intercalate opens ++ " in\n"
    let setPfx := (enclosingSetOptionsFor lines span.headerStart).foldl
      (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") ""
    let varPfx := (enclosingVariablesFor lines span.headerStart).foldl
      (fun acc v => acc ++ v ++ " in\n") ""
    let probeSrc := setPfx ++ openPfx ++ varPfx ++ renHdr ++ "\n" ++
      "\n".intercalate (lines.extract span.bodyStart span.bodyEnd).toList
    match ← elabCheckFirstError probeSrc with
    | some err =>
      keepGoing := false
      progress s!"DECL BASELINE FAILED — '{declName}' does not re-elaborate in the probe env (in-file-only elaboration, e.g. matcher-constant reuse); skipping extraction (err: {err.take 160})"
    | none => pure ()
  while keepGoing do
    keepGoing := false
    match findAnySpan lines declName with
    | none => pure ()
    | some span =>
      let preLines := lines
      lines := renameShadowedHaveNames lines span
      lines := nameAnonymousHaves lines span
      lines := destructuringHavesToObtain lines span
      -- GATE THE PRE-PASS RENAMES (#51): `nameAnonymousHaves`' scoped
      -- `this`-rename can lose references in deep bullet/case lattices
      -- (canonicalPath_preserve: the renamed body itself failed with
      -- "Unknown identifier `this`", so EVERY candidate gate on that body
      -- rejected — a 0/36 wipeout that looked like 36 verdicts). The renames
      -- were the only ungated text mutation left. Re-elaborate the renamed
      -- decl once; on error, revert to the untouched text — named haves
      -- still extract (their gates then replay the ORIGINAL body, whose
      -- `this` references are intact), only anonymous ones stay invisible.
      if !(lines == preLines) then
        -- pre-pass mutations can CHANGE LINE COUNT (destructuringHavesToObtain
        -- inserts an `obtain` line) — the pre-mutation span's bodyEnd would
        -- silently truncate the probe body. Re-derive; unresolvable ⇒ revert.
        match findAnySpan lines declName with
        | none =>
          progress "pre-pass mutations lost the decl span — REVERTED"
          lines := preLines
        | some spanM =>
          let headerText0 := "\n".intercalate (lines.extract spanM.headerStart spanM.bodyStart).toList
          let headerText :=
            if headerText0.startsWith "private " then headerText0.drop "private ".length else headerText0
          let kw := if headerText.startsWith "theorem " then "theorem " else "lemma "
          let nsPathP := enclosingNamespacePathFor lines spanM.headerStart
          let renHdr := kw ++ (if nsPathP.isEmpty then "" else nsPathP ++ ".") ++ "__prepass_check__" ++ ((headerText.drop kw.length).drop spanM.name.length)
          let opens := enclosingOpensFor lines spanM.headerStart
          let openPfx := if opens.isEmpty then "" else "open " ++ " ".intercalate opens ++ " in\n"
          let setPfx := (enclosingSetOptionsFor lines spanM.headerStart).foldl
            (fun acc (nm, v) => acc ++ "set_option " ++ nm ++ " " ++ v ++ " in\n") ""
          let varPfx := (enclosingVariablesFor lines spanM.headerStart).foldl
            (fun acc v => acc ++ v ++ " in\n") ""
          let probeSrc := setPfx ++ openPfx ++ varPfx ++ renHdr ++ "\n" ++
            "\n".intercalate (lines.extract spanM.bodyStart spanM.bodyEnd).toList
          match ← elabCheckFirstError probeSrc with
          | some err =>
            progress s!"pre-pass renames broke the decl — REVERTED (err: {err.take 120})"
            lines := preLines
          | none => pure ()
      -- span may be stale after a line-count-changing pre-pass — refresh
      let span := (findAnySpan lines declName).getD span
      let (splitLines, didSplit) := splitMidLineHavesInSpan lines span
      if didSplit then
        lines := splitLines
        keepGoing := true
      else
        let headers := (findAllHaveHeaders lines span.bodyStart span.bodyEnd).filter
          (fun (_, n) => !doneNames.contains n)
        match findLeafHave lines headers doneNames with
        | none => pure ()
        | some (haveIdx, haveName) =>
          -- see the whole-file loop: previously-converted one-liners call
          -- their own aux lemma — re-extraction would redeclare it
          let marker := "_aux_" ++ haveName
          let alreadyConverted :=
            match lines[haveIdx]!.splitOn marker with
            | _ :: rest :: _ => rest.isEmpty || !isIdentChar (rest.get! 0)
            | _ => false
          if alreadyConverted then
            doneNames := haveName :: doneNames
            keepGoing := true
          else
          -- STRUCT-FIELD HAVE (#58): a have inside a structure-literal
          -- field's by-block (`invFun := fun x => ⟨_, by have hfst := ...⟩`
          -- under `:= { toFun := ..., ... }`) sits inside an UNCLOSED `{`
          -- or `⟨` at its own line — prefix replay cannot reconstruct a
          -- tactic context there (nine 0-message captures observed, ~10 min
          -- wasted). Detect by brace/angle imbalance over the body prefix
          -- and skip honestly with one log line.
          let pref := lines.extract span.bodyStart haveIdx
          let cnt (c : Char) : Nat := pref.foldl (fun acc l => acc + (l.toList.filter (· == c)).length) 0
          if cnt '{' > cnt '}' || cnt '⟨' > cnt '⟩' then
            -- STRUCT-FIELD HAVE, ROUTED (#59): prefix replay can't reach a
            -- have inside an unclosed {/⟨ block, but rung T doesn't replay —
            -- it elaborates the WHOLE decl and walks the stored term, so
            -- struct-literal-field haves are perfectly reachable there. Go
            -- straight to rung T (skipping only the 9 doomed goal-route
            -- probes this used to burn, and the outright skip it briefly
            -- became).
            counter := counter + 1
            progress s!"attempt {counter}: {declName}.{haveName} (struct-field → rung T) ..."
            match ← extractOneHaveViaTerm lines span haveIdx haveName counter with
            | none =>
              doneNames := haveName :: doneNames
              progress s!"attempt {counter}: {declName}.{haveName} FAILED (struct-field, rung-T only)"
              keepGoing := true
            | some newLines =>
              lines := newLines
              doneNames := haveName :: doneNames
              succeeded := succeeded + 1
              progress s!"attempt {counter}: {declName}.{haveName} TERM-EXTRACTED (struct-field) ({succeeded}/{counter})"
              IO.FS.writeFile outputPath ("\n".intercalate lines.toList)
              progress s!"checkpoint written ({succeeded} commits)"
              keepGoing := true
          else
          counter := counter + 1
          progress s!"attempt {counter}: {declName}.{haveName} ..."
          match ← extractOneHaveViaGoal lines span haveIdx haveName counter with
          | none =>
            -- rung T fallback: proof-term-based extraction (no prefix replay)
            match ← extractOneHaveViaTerm lines span haveIdx haveName counter with
            | none =>
              doneNames := haveName :: doneNames
              progress s!"attempt {counter}: {declName}.{haveName} FAILED"
              keepGoing := true
            | some newLines =>
              lines := newLines
              doneNames := haveName :: doneNames
              succeeded := succeeded + 1
              progress s!"attempt {counter}: {declName}.{haveName} TERM-EXTRACTED ({succeeded}/{counter})"
              -- CHECKPOINT (#58): write the working text after EVERY commit,
              -- not only at DONE-DECL — a disk auto-stop mid-decl then loses
              -- only the in-flight attempt; the next run's output-as-input
              -- resumes from here (committed one-liners skip re-extraction,
              -- persistFileAuxLemmas re-persists their aux lemmas).
              IO.FS.writeFile outputPath ("\n".intercalate lines.toList)
              progress s!"checkpoint written ({succeeded} commits)"
              keepGoing := true
          | some newLines =>
            lines := newLines
            doneNames := haveName :: doneNames
            succeeded := succeeded + 1
            progress s!"attempt {counter}: {declName}.{haveName} EXTRACTED ({succeeded}/{counter})"
            IO.FS.writeFile outputPath ("\n".intercalate lines.toList)
            progress s!"checkpoint written ({succeeded} commits)"
            keepGoing := true
  -- ── final cleanup, queue-based: the target decl plus every lemma the
  -- ladder splices during THIS invocation (identified by header-name diff;
  -- splices from other invocations are their own targets) ──
  -- RAW header names — NOT via declProbeParts, whose headerText is RENAMED
  -- to `NAME__vtrial` for probe use: matching against it made this whole
  -- queue loop a silent no-op (the target name never matched, so the
  -- per-decl final pass — heuristic inlining AND the ladder — never ran;
  -- zero "final pass (decl-mode)" lines across the entire campaign).
  let headersOf (lns : Array String) : Array String :=
    (findAllDeclSpans lns).map (fun (bs, _) => Id.run do
      let kws : List String := ["private theorem ", "private lemma ", "theorem ", "lemma "]
      let mut k := bs
      while k > 0 do
        k := k - 1
        let l := lns[k]!
        if !l.startsWith "  " then
          match kws.find? l.startsWith with
          | some kw =>
            let rest := l.drop kw.length
            return (((rest.splitOn " ").head!).splitOn ".{").head!
          | none => pure ()
      return "")
  let mut queue : List String := [declName]
  let mut fuel := 200
  while !queue.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let target := queue.head!
    queue := queue.tail!
    let mut processing := true
    while processing && fuel > 0 do
      fuel := fuel - 1
      let declSpans := findAllDeclSpans lines
      let names := headersOf lines
      let mut foundIdx : Option Nat := none
      for i in [0:names.size] do
        if foundIdx.isNone && names[i]! == target then
          foundIdx := some i
      match foundIdx with
      | none => processing := false
      | some i =>
        let (bStart, bEnd) := declSpans[i]!
        progress s!"final pass (decl-mode): {target}"
        let namesBefore := names
        let (newLines, spliced) ← finalPassOneDecl lines bStart bEnd
        lines := newLines
        -- requeue anything the ladder spliced (they carry relocated haves)
        for h in headersOf lines do
          if h.length > 0 && !namesBefore.contains h && !queue.contains h && h != target then
            queue := queue ++ [h]
        -- reprocessing the (name-relocated) target after a splice mirrors
        -- the whole-file hold-index rule; no splice → this target is done
        if !spliced then
          processing := false
  progress s!"DONE-DECL {declName} attempts={counter} succeeded={succeeded} — writing {outputPath}"
  IO.FS.writeFile outputPath ("\n".intercalate lines.toList)
  logInfo s!"#extract_haves_iter_decl {declName}: written to {outputPath} | attempts={counter} succeeded={succeeded}"

/--
`#extract_haves_final_pass "dst/Output.lean"`

Final-cleanup-ONLY pass over EVERY declaration of an existing output file:
heuristic inlining + the verified ladder (rungs A0-E), no extraction. Use
after a per-decl campaign — `#extract_haves_iter_decl`'s queue-based final
pass only covers its target declaration, so committed one-liners in other
declarations (e.g. `:= by apply *_aux_* <;> assumption` callsites) never
get laddered into `let`s/inlined otherwise.
-/
elab "#extract_haves_final_pass " dstLit:str : command => do
  let outputPath := dstLit.getString
  letReplayEnabledRef.set false
  let src ← IO.FS.readFile outputPath
  probeAutoImplicitRef.set (!(((src.splitOn "\n").map String.trim).contains "set_option autoImplicit false"))
  let progressPath := outputPath ++ ".progress"
  let progress (msg : String) : CommandElabM Unit := do
    IO.eprintln s!"[extract-haves] {msg}"
    IO.FS.withFile progressPath .append fun h => h.putStrLn msg
  progress s!"START-FINALPASS {outputPath}"
  let mut lines := src.splitOn "\n" |>.toArray
  persistFileAuxLemmas lines progress
  let mut declIdx := 0
  let mut moreDecls := true
  while moreDecls do
    let declSpans := findAllDeclSpans lines
    if declIdx < declSpans.size then
      let (bStart, bEnd) := declSpans[declIdx]!
      progress s!"final pass (file-mode): decl {declIdx + 1}/{declSpans.size}"
      let (newLines, spliced) ← finalPassOneDecl lines bStart bEnd
      lines := newLines
      if !spliced then
        declIdx := declIdx + 1
    else
      moreDecls := false
  progress s!"DONE-FINALPASS — writing {outputPath}"
  IO.FS.writeFile outputPath ("\n".intercalate lines.toList)
  logInfo s!"#extract_haves_final_pass: written to {outputPath}"

end ExtractHavesFile
