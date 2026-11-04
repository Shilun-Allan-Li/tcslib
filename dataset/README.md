# The TCSlib theorem dataset

`tcslib_theorems.jsonl.gz` pairs every blueprint-bound theorem and lemma of the library
with an informal statement and an informal proof (each the cited passage of the text it was formalized from, or
prose written from the Lean when no text cites it), a self-contained formal statement,
and a flattened compiling proof file.  Only the `.gz` is tracked; the plain `.jsonl`
is regenerated locally and git-ignored.  Every reader goes through
`proofmatch/dataset_io.py`, which falls back to the `.gz` transparently.

`INSTRUCTIONS.md` is the two-step guide for contributors; `DESIGN.md` records the
intent, the rules the pipeline keeps, and the known gaps.

## Building it

One command updates the dataset from the Lean sources (and the text the new statements
were formalized from), incrementally:

```bash
python3 scripts/dataset_pipeline.py --check-env                       # what this machine has
python3 scripts/dataset_pipeline.py --estimate                        # report; spend nothing
python3 scripts/sources.py                                            # texts, tags, files: what is cited, what is missing
python3 scripts/sources.py add AB09=~/texts/arora-barak-ch09.pdf      # attach + match one text
python3 scripts/dataset_pipeline.py --build --yes \
    --source AB09=~/texts/arora-barak-ch09.pdf                        # after formalizing ch. 9
python3 scripts/dataset_pipeline.py --modules Complexity.Ch09 --yes   # only that module's records
python3 scripts/dataset_pipeline.py --only TCSlib.Foo.bar --from statements --to dataset
python3 scripts/dataset_pipeline.py --stages dataset,verify --lean-check 20
python3 scripts/dataset_pipeline.py --backend codex --model gpt-5 --yes   # on the Codex CLI
```

Nothing is ever rebuilt from nothing.  Every LLM product is cached per declaration and
reused (statement prose under `references/statements/`, keyed on the mathematical core
of the formal statement; ratings and citations in the blueprint `.tex`; proof notes under
`references/informalized/`); the deterministic stages take seconds; and the final
`dataset` stage **merges** the build into the shipped file rather than replacing it:

| A record of the current dataset ... | becomes |
|---|---|
| is in the build | **replaced** (every column) |
| is not in the build, but the run was a selection (`--only` / `--modules`) | **kept** untouched |
| belongs to a module that is not in `dep_graph.json` (not imported from `TCSlib.lean`, so never built) | **carried** over unchanged and reported; `dataset_check.py` lists it as `stale-module`; `--drop-unbuilt` drops it instead |
| is still declared in its module but the builder left it out (stale graph, no blueprint entry) | **skipped**: kept and reported |
| no longer exists under its name, but a *built* module declares the same short name under another full name (namespace or file rename) | **renamed**: dropped, the new name reported; the build adds the record under the new name once it has a blueprint entry, and the blueprint already carries citations under the new name |
| is no longer in its module but a Lean file that is *not* built still declares it | **moved**: kept and reported |
| is declared nowhere any more (deleted) | **dropped** |

Records the build adds are **added**.  The merge report is printed and saved to
`dataset/.pipeline/merge.json`; the dataset stays sorted by `id`.

`--only NAME...` and `--modules MODULE...` (a full module name, a dotted suffix, or an
area such as `Complexity`) restrict *every* stage to those records: the blueprint stubs,
the prose, the ratings, the citation matching, the proof notes and the final build.
That is the way to fix specific wrong records: regenerate just them, and the merge leaves
everything else byte-identical.

The stages, in order.  Each one is idempotent and caches per declaration, so an
interrupted run is resumed by running the same command again (or `--from <stage>`).

| Stage | LLM | What it does | Scripts |
|---|---|---|---|
| `graph` | no | `lake build` (with `--build`) and the declaration dependency graph. Reports modules imported from `TCSlib.lean` that the graph predates (run `--build`), modules on disk that nothing imports (add the import, then `--build`), graph modules whose source moved, and the records of the current dataset a merge will carry over. | `build_dep_graph.py` |
| `references` | yes | Every text under `blueprint/src/references/` without a validated `<name>.md` (a PDF dropped there, or one given as `--source TAG=PATH`) is OCR'd and cleaned into one (block-anchored, so citations can point into it); a `--source` tag is registered in `references/sources.json`. | `proofmatch.py extract`, `reference_coverage.py --register` |
| `blueprint` | no | Every documentable declaration without a blueprint entry gets one, with the binding `\lean{}`, `\leanok`, `\uses{}` and a marked placeholder body (an estimate only counts them). | `blueprint_enumerate.py`, `blueprint_stub.py`, `blueprint_assemble.py`, `blueprint_validate.py` |
| `citations` | yes | Statement-only pass-1 build, then the coverage report (below), then every reference document the blueprint does not cite yet (new texts, and older ones never matched) is matched against the dataset; proofs the text proves get `\proofsource`, statements it only states get `\statementsource`; the tag registry is re-derived from the citations. `--rematch` redoes matched documents too. A `\statementsource` is the record's informal statement and a `\proofsource` its informal proof, so it runs before anything is generated. | `reference_coverage.py`, `proofmatch.py match` |
| `statements` | yes | Pass 1 again, then the informal statement of every record whose *statement* nothing cites (and every stub definition) whose prose is not cached is written from the *formal* statement to handout standard, rubric-gated, cached under `references/statements/`, and applied into the blueprint. Statement-cited records are skipped: nothing is generated where a text can be quoted. | `build_dataset.py --no-proof`, `build_informal_statements.py`, `blueprint_restate.py --apply-only` |
| `difficulty` | yes | Unrated proofs get an intrinsic, tactic-only 1-7 rating written as `\difficulty{N}`. | `blueprint_difficulty_plan.py`, `rate_difficulty.py`, `blueprint_difficulty_apply.py` |
| `informalize` | yes | Every sorry-free proof that nothing cites and that has no note gets a prose account of its Lean proof under `references/informalized/<name>.md`, which becomes its `informal_proof` at build time. An account that is a tactic transcript (mostly code naming tactics) is rejected and retried once; notes parked under `informalized/rejected/` are ignored. Stops first if a *new* theorem cites a text nobody attached (below). | `reference_coverage.py --strict`, `informalize_proofs.py` |
| `dataset` | no | The full build with flattened proofs of the selected (or all built) records -- each record's informal statement from its `\statementsource` else the Lean prose, its informal proof from its `\proofsource` else the note (`informal_sources.py`) -- merged into the dataset as described above. | `build_dataset.py`, `dataset_splice.py --merge` |
| `verify` | no | Structural checks (every column present, no leaked docstring lines in formal statements, no stub prose, row loss against the previous dataset, carried-over rows, optionally N sampled formal statements compiled with `scripts/lean_check.sh`), prose checks, blueprint integrity. | `dataset_check.py --strict`, `dataset_hygiene.py`, `statement_quality.py`, `blueprint_validate.py --strict --allow-orphans` |

State, logs, the pass-1 build, the merge and coverage reports live in `dataset/.pipeline/`
(git-ignored); `state.json` records each stage's outcome and `logs/<stage>.log` its full
output.

### Reference texts: attach, then run

The builder never searches outside `blueprint/src/references/` for sources.  A theorem
receives a citation only when the text it was formalized from is there and has been
matched: the passage that states it is then its informal statement and the passage
that proves it its informal proof.  Whichever of the two no text covers is written from
the Lean: the statement as prose, the proof as an informalized account.
The contract has two steps:

1. **After formalizing something, attach the text it came from** to
   `blueprint/src/references/` if it is not there already: copy the PDF (or a validated
   `.md`) into the directory, or pass it as `--source TAG=PATH` where `TAG` is the `[TAG]`
   the new declarations' docstrings cite (policy.md §2: every result carries
   `[AB09, Thm 9.3]` or similar).
2. **Run the pipeline.**  `python3 scripts/dataset_pipeline.py --yes` (with `--build` after
   a `lake build` is needed).  It ingests every text that has no validated `.md` yet,
   decides which texts still have to be matched (those the blueprint cites nothing from),
   matches them against the whole dataset, and carries the new declarations through the
   remaining stages into the dataset.

```bash
cp ~/texts/cesa-bianchi-lugosi-ch07.pdf blueprint/src/references/
python3 scripts/dataset_pipeline.py --estimate      # what it would ingest, match and write
python3 scripts/dataset_pipeline.py --yes
```

`scripts/sources.py` is the status and the short form of the same contract:

```bash
python3 scripts/sources.py                         # status: texts, tags, Lean files, what each needs
python3 scripts/sources.py add CBL06=~/texts/cesa-bianchi-lugosi-ch07.pdf   # ingest, register, match now
python3 scripts/sources.py match vershynin-hdp-book                         # match one ingested text now
python3 scripts/sources.py register Ver18=vershynin-hdp-book                # tag -> document by hand
```

`status` lists every ingested text with the tags it covers and how many theorems the
blueprint cites it for (a text that was ingested but never matched says so; the next
pipeline run matches it); every docstring tag with its theorem count, how many are
cited, and whether its text is attached, attached but never matched, or `MISSING`
(with the `add` command to run); and every Lean module of the dataset that is not fully
cited, with what it waits for: a text to attach, a match to run, or docstring tags.

What the pipeline does to make that visible:

- `references/sources.json` maps each docstring tag to the ingested documents that cover
  it.  `--source TAG=PATH` registers the document; after each match run the registry is
  re-derived from the citations (`reference_coverage.py --rebuild-registry`), so a text
  dropped in without a tag is tied to its tag once three or more of its cited theorems
  agree; `reference_coverage.py --register TAG=doc` does it by hand.
- The `citations` stage prints which ingested documents it will match and why the others
  are skipped (the blueprint already cites them, or a reviewed match run exists under
  `.proofmatch-work/`), then per tag how many uncited theorems cite it, at which theorem
  numbers, and whether a document is `registered`, was just `attached`, or is `missing`,
  with the exact `--source` command to run.  The report is saved to
  `dataset/.pipeline/coverage.json`.
- The `informalize` stage refuses to write proof notes while a *new* theorem (absent from
  the previous dataset) cites a `missing` tag.  Attach the text and rerun from
  `references`, or pass `--without-sources` to acknowledge that these theorems get
  informalized notes rather than citations.  Theorems already in the dataset never block.
- A docstring without any `[TAG, ...]` is reported as untagged; such a theorem can only be
  informalized.

### Models and backends

Every LLM stage is one structured-output call to a coding-agent CLI, on either vendor:

| `--backend` | CLI | default model | spend |
|---|---|---|---|
| `claude` | Claude Code, `claude -p --json-schema` | `claude-opus-4-8` | read from the CLI's envelope |
| `codex` | OpenAI Codex, `codex exec --output-schema` | `gpt-5` | token usage from the CLI, priced by `proofmatch/budget.py` |

The backend is inferred from the model id (`gpt-5`, `o3`, `gpt-5-codex` run on Codex,
anything else on Claude) or forced with `--backend`; `$PROOFMATCH_BACKEND` and
`$PROOFMATCH_MODEL` set the same defaults for the per-stage scripts.  Both backends run
read-only in an empty temporary directory (no project `CLAUDE.md` / `AGENTS.md` leaks into
the call), and every answer is re-validated against the full schema in
`proofmatch/agents.py`.  Nothing in the pipeline depends on which one is used: the
caches, the blueprint and the dataset are the same files either way, so one contributor
may run on Claude and the next on Codex.

`--model` picks the model for every LLM stage, or a per-stage override such as
`--model-statements claude-fable-5-1`.  The prose stages (`statements`, `informalize`)
and the judgement stages (`difficulty`, `citations`) refuse a model below the opus /
gpt-5 tier; `references` (OCR cleanup) accepts sonnet / gpt-5-mini.  `--allow-weak-models`
waives the floor.  The policy is in `proofmatch/model_policy.py`; prices for the pre-flight
estimates are in `proofmatch/budget.py` (a model with no price row is estimated at opus
rates).

### Running it on another machine

Everything is in the repository; nothing is tied to one machine.  A clone needs:

- Python 3.10 or newer, standard library only; macOS or Linux.
- The Lean toolchain pinned in `lean-toolchain` (via elan) and one `lake build`: the
  dependency graph is read from the `.ilean` files it produces, and `--lean-check`
  compiles against its oleans.
- The CLI of the chosen backend, logged in: Claude Code (`npm install -g
  @anthropic-ai/claude-code`, then `claude`) or Codex (`npm install -g @openai/codex`,
  then `codex login`).  The spend lands on that account.
- Only for attaching a PDF: `pdf2txt.py` (pdfminer.six) and Ghostscript.  A Markdown
  source needs neither.

`python3 scripts/dataset_pipeline.py --check-env` checks all of this and says what is
missing.  Per-declaration caches travel with the repository, so a fresh clone pays only
for records that are new or changed.

Each LLM stage prints what is outstanding and asks before spending; `--yes` skips the
question, `--limit N` caps a stage at N items for a pilot, `--estimate` runs only the
no-LLM stages (the merge as a dry run) and reports the rest.

### After formalizing new statements

1. Register the new module(s) in `TCSlib.lean` (a module that is not imported from the root
   is never built, so it never enters the graph; its records, if any, are only carried over).
2. Put the text the statements came from under `blueprint/src/references/` (or pass it as
   `--source TAG=<text>`), then `python3 scripts/dataset_pipeline.py --build --yes`, or
   `--modules <the new module>` to touch nothing else.  (`python3 scripts/sources.py`
   before and after shows what the text covered and what is still waiting.)
3. Read `dataset/.pipeline/check.json` and `merge.json`; commit `dataset/tcslib_theorems.jsonl.gz`,
   the blueprint chapters, and the new files under `blueprint/src/references/`.

To repair a few records by hand without the pipeline (for example after a flattener fix):

```bash
python3 scripts/build_dataset.py --no-proof --only NAME... --out /tmp/patch.jsonl
python3 scripts/dataset_splice.py /tmp/patch.jsonl        # statement fields only
```

## Record schema

One JSON object per line, in this column order.

| Column | Type | Meaning |
|---|---|---|
| `id`, `lean_name` | string | Fully-qualified Lean name (identical). |
| `informal_statement` | string | The result in prose. When the blueprint entry cites the passage that states it (`\statementsource`), that passage verbatim from `references/<doc>.md`. Otherwise prose written from the Lean: a "Definitions:" block rendering `definitions`, then `Statement: <the claim>` (handout standard, LaTeX math); or the bare claim when it uses no library definition. |
| `statement_source` | string | `citation` or `lean`: which of the two the above is. |
| `informal_proof` | string | The proof in prose. When the entry cites the passage that proves it (`\proofsource`), that passage verbatim. Otherwise the informalized account of the Lean proof from `references/informalized/<name>.md` when one exists, else empty. |
| `proof_source` | string | `citation`, `lean` or `none`: which of the three the above is. |
| `title` | string | Short name of the result. |
| `definitions` | list of `{id, title, informal}` | Informal descriptions of the library definitions the statement uses, dependency order. |
| `formal_statement` | string | A standalone Lean file: the imports of the declaration's own module closure, the library definitions (and instances) the statement needs, the instances of its environment whose types those definitions mention (as `:= sorry` stubs, since only an instance's type matters for resolution), any lemma a definition body cites as a `:= sorry` stub, then the declaration itself with `:= sorry` (always the last declaration). |
| `upstream_defs`, `n_upstream_defs` | list, int | The definitions emitted in `formal_statement`. |
| `source_module`, `kind` | string | Module of the declaration; `theorem` or `lemma`. |
| `difficulty` | int or null | Intrinsic 1-7 rating of the proof script alone (null when unrated or the proof is a bare `sorry`). |
| `proof` | string | A standalone Lean file ending with the declaration proved for real: its full dependency closure flattened in compile order, with original proof bodies. |
| `proof_upstream_decls`, `n_proof_upstream_decls` | list, int | Declarations emitted in `proof`. |
| `proof_unresolved_deps` | list | Dependencies the flattener could not place (empty in a healthy build). |
| `proof_complete` | bool | False when `proof` still contains `sorry` (the library has not finished this proof or an upstream one). |

`formal_statement` is best-effort standalone: it reproduces the declaration's real
environment (imports, `open`/`universe`/notation context, `open … in` prefixes, the
instances its definitions need, namespace stubs, cited lemmas as sorry stubs), and
`dataset_check.py --lean-check N` compiles a sample to measure how many still fail.
`proof` is the verified column.

### The statement cache

`blueprint/src/references/statements/<lean_name>.json` holds each regenerated statement
under a key that hashes the *mathematical core* of its formal statement (definitions and
the declaration, with imports, context lines, instances, variable lines and lemma stubs
stripped and block order ignored -- `proofmatch/statements.py: core_text`).  A builder
improvement therefore never invalidates the prose; editing the declaration or a definition
it uses does.  `build_informal_statements.py --rekey OLD.jsonl ...` revalidates entries
written against an earlier build (the pipeline does this automatically against the
previous dataset), and `--trust-unknown` keeps entries whose key matches no known build.
