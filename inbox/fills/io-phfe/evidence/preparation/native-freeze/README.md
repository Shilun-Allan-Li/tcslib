# Native syntax freeze draft

This tool replaces the textual first-top-level-`:=` heuristic with actual Lean command syntax.
It is an audit tool only. It changes no user theorem, original manifest, live source or Git state.

Status: the Python file passes `ast.parse`; the Lean tool has NOT been compiled or run by the
agent. Root must run its native compilation/parser invocations through the authorized slot.
The original checkpoint manifest remains `evidence/freeze/checkpoint0.json` at exact source Git
`70b85f9ba83f27393d98fa5bf88505aea3d22a8d`; it is read only for scope and coverage metadata.

## Files

- `NativeFreeze.lean`: core-Lean executable, 249 lines, no theorem/proof elaboration.
- `native_freeze.py`: read-only Git/source staging, parser orchestration, manifest comparison,
  source-mutation controls and immutable provenance output.
- `API-NOTES.md`: exact statically reviewed Lean 4.25 APIs and validation risks.

## Caller-controlled execution

The executable interface is:

```
NativeFreeze SYSROOT MODULE REQUESTS_JSON
```

`REQUESTS_JSON` is an array of `{ "id": "baseline", "path": "/absolute/file.lean" }` objects.
The tool imports the checked current `MODULE` once for parser/name availability, then parses all
requested source copies in independent fresh scope states with that SAME imported environment.
It emits one `NATIVE_FREEZE_JSON<TAB>{...}` line per request, and returns nonzero on any error.
Set `LEAN_PATH` to the existing checked source/module dependency path. SYSROOT must explicitly
name the repository's Lean 4.25 toolchain; the tool never spawns `lean --print-prefix`.

The driver chooses no Lean/lake command automatically. Root supplies a literal JSON argv array
containing the exact slot-wrapped parser executable or slot-wrapped `lean --run` command.
The driver appends the three interface arguments and invokes each batch sequentially with
`subprocess.run(..., shell=False)`. Do not substitute an unwrapped Lean command.

Example argument shape, with the parser prefix supplied by root's existing slot protocol:

```
python3 /private/tmp/io-phfe-drafts/native-freeze/native_freeze.py \
  --repo /Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange \
  --original-manifest /absolute/worktree/evidence/freeze/checkpoint0.json \
  --files-list /absolute/worktree/evidence/logs/owned-files.txt \
  --parser-source /private/tmp/io-phfe-drafts/native-freeze/NativeFreeze.lean \
  --parser-command-json '["SLOT_WRAPPED_PARSER_EXECUTABLE","ROOT_OWNED_ARGUMENTS"]' \
  --sysroot /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0 \
  --out /private/tmp/io-phfe-native-freeze-run-UNUSED
```

The example prefix is deliberately a placeholder; it must be replaced by root's approved slot
wrapper argv. No agent executed this driver or any command in this example.

## Native extraction and boundaries

`Parser.parseHeader` and `Parser.parseCommand` produce source syntax spans. For a theorem/lemma,
the extractor selects its DIRECT `Parser.Command.declValSimple` child. That child's `:=` atom
is the proof delimiter. Its separate `declSig` child contains the complete return type, including
all `let ... := ...` values and the proposition after them. Nested term delimiters cannot be
mistaken for the declaration body. Proof-term and return-let-body spans are exported separately.

The theorem header starts after its attached native doc-comment span and ends before the native
body delimiter, retaining modifiers, attributes, binders and the FULL type. Non-theorem
definitions, structures and their fields freeze the entire command after its outer docstring.
Opening doc prose is compared separately. As in the original policy, the first literal
`**Proof sketch.**` starts the permitted proof-sketch remainder; preceding prose is retained,
not discarded merely because a sketch is present.

Namespaces/scopes/options/open directives and notation/mixfix commands are the only source
commands elaborated, to reproduce parser scoping and local notation. Audited theorem/definition
commands and their bodies are NEVER elaborated. Variable/universe/attribute/etc. commands are
recorded as other syntax, not executed. In-file syntax/macro/elab extensions fail explicitly;
there is no textual parser fallback. All parse/recovery/scope errors fail the whole batch.

The current imported module supplies names needed by `open` and parser extensions needed by
existing tactics/notations. Its declaration types are not used as a substitute for comparing
source header bytes. This does NOT establish historical elaborated type equality or compare
all ambient variable/import semantics. Root's separate compiled-declaration type and axiom
census is still required. Other top-level command spans are retained for review.

## Immutable stronger baseline and controls

The driver requires the exact authorized Git commit to equal the original manifest's head,
reads source using only `git rev-parse`, `git ls-tree` and `git show`, and writes copies under a
NEW `--out` directory. It refuses an existing output directory. It never overwrites or derives
complete headers from the old truncated manifest. Original-name/kind/private/prose coverage
must agree before a stronger baseline is accepted; mismatches fail for review.

Outputs include:

- `native-checkpoint0.json`, reconstructed from the pinned Git source;
- `native-current.json`, parsed from snapshotted current files;
- `native-spans/`, exact source ranges and other command metadata;
- `negative-controls.json`, results from source mutations parsed again natively;
- `report.json`, full frozen differences, new-helper list and all provenance hashes;
- `sources/`, source-only snapshots and controls; `logs/`, raw slot/parser output and argv.

Required source controls (each must parse successfully before its comparison counts):

1. Change one ASCII character INSIDE a native return-type-let body, after its assignment and
   before the declaration proof delimiter: rejected as a frozen header edit.
2. Change opening prose in a docstring that still contains its unchanged sketch marker:
   rejected as a frozen prose edit.
3. Change the sketch marker itself: rejected, preventing accidental prose suppression.
4. Change only the sketch remainder: permitted.
5. Replace only the native theorem proof-term span with `sorry`: permitted.

Both the original manifest and parser source are hash-checked unchanged after the run. Current
live sources must still match their snapshots; concurrent proof edits cause a clear failed run
rather than a stale success. Re-run into another fresh output directory after the edits stop.

## Root native repairs and execution

The first smoke run exposed routine record layout/String.drop API errors, repaired in the
root copy with all attempt sources/logs retained. Empty optional non-theorem signatures now
record no signature span; their entire command remains frozen. Local notation quotation
prechecking is disabled ONLY in this syntax tool's command state because source variables
are intentionally not elaborated. Both historical/current sources receive the same option;
all declaration/return-type bytes are still parsed and compared. This is not a theorem
checking substitute. Original sources and manifest are unchanged. Full runs rerun every file.

The root may compile this audit-only module once under its slot, then use the one-line
RunNativeFreeze launcher with that exact hashed olean on LEAN_PATH, avoiding repeated tool
elaboration. Source/olean/launcher hashes and native compile/check logs must accompany it.
