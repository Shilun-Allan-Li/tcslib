# Static Lean API evidence and native validation checklist

All reads used the repository's actual Lean toolchain v4.25.0. No Lean, lake, Git or proof checker
was invoked by the agent. No live source file was edited. The Python driver was parsed with
Python `ast.parse` only; its main routine and read-only Git/native subprocess paths were not run.

## Exact API sources read

- `Lean/Parser/Module.lean:82`: `parseHeader : InputContext -> IO (HeaderSyntax × state × log)`.
- `Lean/Parser/Module.lean:137`: `parseCommand` takes `ParserModuleContext` with env/options/
  namespace/open declarations, source parser state and message log. The test module parser at
  :183 demonstrates the same parse loop, but warns most modules need scoped parser updates.
- `Lean/Parser/Command.lean:166`: `declValSimple` has `:=` atom, `declBody`, termination suffix,
  optional where-declarations. Theorem at :193 has declId, declSig and declVal as separate direct
  components. Declarations at :279 pair declModifiers with that core declaration.
- `Lean/Parser/Command.lean:125`: declSig is binders followed by Term.typeSpec, which parses the
  entire return type. Native declValSimple selection excludes every nested term-let delimiter.
- `Lean/Parser/Term.lean:91`: namespace `Parser.Command.docComment`, source includes `/--` and
  comment body/closing token. `Parser.Term.let` at :511 has its continuation as its final arg.
- `Mathlib/Tactic/Lemma.lean:17-28`: top syntax kind is global `lemma`; its modifiers/core shape
  matches declaration/theorem, and expandLemma changes kind without changing that shape.
- `Lean/Syntax.lean:406`: native `getRange?` comes from getPos?/getTailPos?. The tool stores
  `String.Pos.Raw.byteIdx` and Python slices UTF-8 BYTES, never Unicode code-point positions.
- `Lean/Elab/Frontend.lean:31-44`: direct `CommandElabM` invocation/context and StateRefT.run
  through EIO.toIO'. The tool uses this only for the scope/notation allowlist.
- `Lean/Elab/Frontend.lean:59-74`: current scope supplies parser options, namespace/openDecls.
- `Lean/Elab/Command.lean:95`: `Command.mkState`; :595 `elabCommandTopLevel` resets per-command
  messages and performs elaboration. The audit never calls this on audited declarations.
- `Lean/Elab/BuiltinCommand.lean:89/94/228/299/501`: namespace, section, end, open and set_option.
  Namespace entry activates the corresponding scoped parser state automatically.
- `Lean/Parser/Syntax.lean:92/95`: `mixfix` and `notation` command syntax. Current owned files
  use `open scoped Matrix/BigOperators` and several local notation abbreviations; ignoring these
  would not be a reliable native parser. No new source syntax/macro/elab definition is silently
  accepted; unsupported extension commands fail for review.
- `Lean/Environment.lean:2315`: `importModules` with `loadExts := true`; imports are checked
  existing current modules. Each source version is parsed with the same imported environment.
- `Lean/Util/Path.lean:102`: initSearchPath uses explicit sysroot plus LEAN_PATH. `findSysroot`
  would spawn `lean --print-prefix` if no env was set; the tool deliberately DOES NOT use it.
- `Lean/Message.lean:582/602`: hasErrors and toList for fail-closed diagnostics.
- `Lean/Data/Json/FromToJson/Basic.lean:217`: getObjValAs? exists, but request decoding instead
  uses derived FromJson and the standard Json.parse/fromJson? APIs.

## Native-run risks to check first

This is uncompiled tool source. Root should check the core-only tool before running the audit:

- That `Parser.ParserModuleContext`, `env.setMainModule`, `source.utf8ByteSize`, Syntax array
  indexing and the explicit EIO StateRefT invocation elaborate as written in v4.25.
- That the exact theorem value is indeed the DIRECT declValSimple child on all original
  theorem syntax, and its index1 is the complete proof term (the APIs support this shape).
- That `sourceSpan doc` excludes trailing whitespace so its bytes end at `-/`; Python asserts
  this and fails otherwise instead of stripping a guessed range.
- That local notation elaborates in the imported current-module environment without audited
  variable declarations. Notation RHS is syntax, not a typechecked user proof. If any supported
  scope command needs a small state/context repair, preserve the no-declaration-elaboration
  boundary; do not solve it by elaborating whole source files.
- That source modules containing `lemma` get the global `lemma` syntax kind shown by Mathlib.
- That original 1171 names from 74 files reproduce natively. Any old textual-namespace parser
  discrepancy must be explained; no missing frozen entry may silently be ignored.
- That all five actual-source mutation controls pass natively. Parser errors do not count as
  successful negative controls. In particular, the post-let character must belong to the type
  continuation's native syntax span, not merely lie textually after the first `:=`.

Keep every native compile/check invocation slot-wrapped. Do not overwrite the original M0
checkpoint manifest, its controls or the documented textual-parser limitation. The stronger
baseline should carry a new filename and provenance pointing to the same exact checkpoint Git
commit. A successful syntax audit is separate from the final native elaborated type comparison.
