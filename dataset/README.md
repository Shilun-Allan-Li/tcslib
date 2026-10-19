# The TCSlib theorem dataset

`tcslib_theorems.jsonl.gz` pairs every blueprint-bound theorem and lemma of the library
with a self-contained informal statement, a self-contained formal statement, a
flattened compiling proof file, and the provenance of each half (textbook citation or an
informalized account of the Lean proof).  Only the `.gz` is tracked; the plain `.jsonl`
is regenerated locally and git-ignored.  Every reader goes through
`proofmatch/dataset_io.py`, which falls back to the `.gz` transparently.

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
| is in the build | **replaced** (every column, `proof_notes` included) |
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
| `references` | yes | Each `--source TAG=PATH` text is placed under `blueprint/src/references/` and registered for its tag in `references/sources.json`; a PDF is OCR'd and cleaned into a validated `<name>.md` (block-anchored, so citations can point into it). | `proofmatch.py extract`, `reference_coverage.py --register` |
| `blueprint` | no | Every documentable declaration without a blueprint entry gets one, with the binding `\lean{}`, `\leanok`, `\uses{}` and a marked placeholder body (an estimate only counts them). | `blueprint_enumerate.py`, `blueprint_stub.py`, `blueprint_assemble.py`, `blueprint_validate.py` |
| `statements` | yes | Statement-only pass-1 build, then the informal statement of every record (and every stub definition) whose prose is not cached is written from the *formal* statement to handout standard, rubric-gated, cached under `references/statements/`, and applied into the blueprint. | `build_dataset.py --no-proof`, `build_informal_statements.py`, `blueprint_restate.py --apply-only` |
| `difficulty` | yes | Unrated proofs get an intrinsic, tactic-only 1-7 rating written as `\difficulty{N}`. | `blueprint_difficulty_plan.py`, `rate_difficulty.py`, `blueprint_difficulty_apply.py` |
| `citations` | yes | Pass 1 again, then the coverage report (below), then each new reference document is matched against the dataset; proofs the text proves get `\proofsource`, statements it only states get `\statementsource`. Add `--cite-all` to match every reference document, `--rematch` to redo matched ones. | `reference_coverage.py`, `proofmatch.py match` |
| `informalize` | yes | Every uncited, sorry-free proof without a note gets a prose account of its Lean proof under `references/informalized/<name>.md`. Stops first if a *new* theorem cites a text nobody attached (below). | `reference_coverage.py --strict`, `informalize_proofs.py` |
| `dataset` | no | The full build with flattened proofs of the selected (or all built) records, `proof_notes` attached from the citations and notes, merged into the dataset as described above. | `build_dataset.py`, `build_proof_notes.py`, `dataset_splice.py --merge` |
| `verify` | no | Structural checks (every column present, no leaked docstring lines in formal statements, no stub prose, row loss against the previous dataset, carried-over rows, optionally N sampled formal statements compiled with `scripts/lean_check.sh`), prose checks, blueprint integrity. | `dataset_check.py --strict`, `dataset_hygiene.py`, `statement_quality.py`, `blueprint_validate.py --strict --allow-orphans` |

State, logs, the pass-1 build, the merge and coverage reports live in `dataset/.pipeline/`
(git-ignored); `state.json` records each stage's outcome and `logs/<stage>.log` its full
output.

### Reference texts: who attaches them

The builder does not look for sources.  A theorem receives a citation only when the text
it was formalized from has been ingested under `references/` and matched; every other
theorem receives an informalized account of its Lean proof instead.  The contract is
therefore:

> **Whoever submits a formalization attaches the text it came from, in the same change.**
> `python3 scripts/dataset_pipeline.py --source TAG=path.pdf` where `TAG` is the `[TAG]` the
> new declarations' docstrings cite (policy.md §2: every result carries `[AB09, Thm 9.3]`
> or similar).

`scripts/sources.py` is the short form of that contract:

```bash
python3 scripts/sources.py                         # status: texts, tags, Lean files, what each needs
python3 scripts/sources.py add CBL06=~/texts/cesa-bianchi-lugosi-ch07.pdf   # ingest, register, match
python3 scripts/sources.py match vershynin-hdp-book                         # match a text already ingested
python3 scripts/sources.py register Ver18=vershynin-hdp-book                # tag -> document by hand
```

`status` lists every ingested text with the tags it covers and how many theorems the
blueprint cites it for (a text that was ingested but never matched says so, with the
`match` command to run); every docstring tag with its theorem count, how many are cited,
and whether its text is `attached`, attached but never matched, or `MISSING` (with the
`add` command to run); and every Lean module of the dataset that is not fully cited,
with what it waits for: a text to attach, a match to run, or docstring tags.  `add`
runs the `references` and `citations` stages of the pipeline for that text and prints
the status again; the citations land in the blueprint, and the next `dataset` stage
carries them into the dataset.

What the pipeline does to make that visible:

- `references/sources.json` maps each docstring tag to the ingested documents that cover
  it.  `--source TAG=PATH` registers the document; `reference_coverage.py --register
  TAG=doc` does it by hand; `--rebuild-registry` derives pairs from existing citations.
- The `citations` stage prints, per tag, how many uncited theorems cite it, at which
  theorem numbers, and whether a document is registered (`registered`), was just attached
  (`attached`) or is `missing`, with the exact `--source` command to run.  The report is
  saved to `dataset/.pipeline/coverage.json`.
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
2. `python3 scripts/dataset_pipeline.py --build --yes --source TAG=<text the statements came from>`,
   or `--modules <the new module>` to touch nothing else.  (`python3 scripts/sources.py`
   before and after shows what the text covered and what is still waiting.)
3. Read `dataset/.pipeline/check.json` and `merge.json`; commit `dataset/tcslib_theorems.jsonl.gz`,
   the blueprint chapters, and the new files under `blueprint/src/references/`.

To repair a few records by hand without the pipeline (for example after a flattener fix):

```bash
python3 scripts/build_dataset.py --no-proof --only NAME... --out /tmp/patch.jsonl
python3 scripts/dataset_splice.py /tmp/patch.jsonl        # statement fields only, proof_notes kept
```

## Record schema

One JSON object per line, in this column order.

| Column | Type | Meaning |
|---|---|---|
| `id`, `lean_name` | string | Fully-qualified Lean name (identical). |
| `title` | string | Short name of the result. |
| `statement_informal` | string | The claim in prose, self-contained, handout standard (LaTeX math). |
| `definitions` | list of `{id, title, informal}` | Informal descriptions of the library definitions the statement uses, dependency order. |
| `informal_statement` | string | `definitions` rendered as a "Definitions:" block followed by `Statement: <statement_informal>`. |
| `statement_source` | string | `regenerated` when the prose came from `build_informal_statements.py`, `blueprint` when it is the document's own. |
| `formal_statement` | string | A standalone Lean file: the imports of the declaration's own module closure, the library definitions (and instances) the statement needs, the instances of its environment whose types those definitions mention (as `:= sorry` stubs, since only an instance's type matters for resolution), any lemma a definition body cites as a `:= sorry` stub, then the declaration itself with `:= sorry` (always the last declaration). |
| `upstream_defs`, `n_upstream_defs` | list, int | The definitions emitted in `formal_statement`. |
| `source_module`, `kind` | string | Module of the declaration; `theorem` or `lemma`. |
| `difficulty` | int or null | Intrinsic 1-7 rating of the proof script alone (null when unrated or the proof is a bare `sorry`). |
| `proof_sources` | list of `{document, blocks}` | `\proofsource` citations: the reference document *proves* this result in those blocks. |
| `proof_steps` | list | Approved `\proofstep` alignments between upstream declarations and document blocks. |
| `proof_notes` | object or null | `kind` (`proof_citation`, `statement_citation`, `informalized`, or a `+informalized` combination), the cited blocks with their text, and the informalized note's markdown. Null when the proof has neither. |
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
