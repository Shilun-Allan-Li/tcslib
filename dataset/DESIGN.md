# Dataset pipeline: design

This file records *why* the dataset pipeline is shaped the way it is and the rules it
must keep.  `INSTRUCTIONS.md` is the two-step guide for contributors; `README.md` is the
reference for every stage, flag and column.  When the code and this file disagree, this
file states the intent and the "Known gaps" section says where the code still deviates.

## Purpose

`dataset/tcslib_theorems.jsonl.gz` pairs every theorem of the library with an informal
statement, a standalone formal statement, a self-contained compiling proof, a difficulty
rating, and the provenance of the mathematics (a citation into the text it was
formalized from, or an account of the Lean proof).  The pipeline keeps that file in step
with the library as people formalize new things, without anyone rebuilding it by hand.

## The contract

Two steps, performed by whoever formalized something:

1. **Attach the text** it came from, under `blueprint/src/references/`, unless it is
   already there.  The docstrings already cite it by tag (policy.md §2).
2. **Run the pipeline.**  It decides what is missing and fills exactly that.

Everything the pipeline does follows from one rule: **the builder never searches for
sources.**  A citation can only come from a text a person attached.  A theorem with no
attached text gets an informalized account of its Lean proof, clearly labelled as such,
never an invented reference.

## What "in the dataset" means

A record is a `theorem` or `lemma` that

- is **built**: its module is imported from `TCSlib.lean`, so `lake build` produced its
  `.ilean` and it is in `dep_graph.json`; and
- is **bound**: a blueprint entry carries `\lean{<its name>}`.

A declaration that is not built is not in the dataset (its old record, if any, is
*carried* over unchanged and reported).  A built declaration without a blueprint entry is
not in the dataset until the `blueprint` stage gives it a stub entry.  Each column is
then owned by one stage:

| Column(s) | Owner | Persisted where |
|---|---|---|
| `formal_statement`, `proof`, `*_upstream_*`, `proof_complete` | `dataset` (deterministic build) | the dataset itself |
| `statement_informal`, `definitions`, `title` | blueprint entry; `statements` writes stub entries | the `.tex` entry (prose cache under `references/statements/`) |
| `difficulty` | `difficulty` | `\difficulty{N}` in the `.tex` entry |
| `proof_sources`, `statement_citation` | `citations` | `\proofsource` / `\statementsource` in the `.tex` entry |
| `proof_notes.informalized` | `informalize` | `references/informalized/<name>.md` |

Every model product therefore lives in the repository next to the thing it describes,
is committed with it, and is never regenerated while its input is unchanged.

## Checking what is and is not there

This is intentional and has one entry point per question.  No stage spends anything to
answer these.

| Question | Command |
|---|---|
| What would a run ingest, generate, rate, match, write and merge, and what would it cost? | `python3 scripts/dataset_pipeline.py --estimate` |
| Which texts are attached, which are cited, which have never been matched, which tags have no text, which Lean files wait for what? | `python3 scripts/sources.py` |
| Which declarations are built but have no blueprint entry, by area? | `python3 scripts/blueprint_validate.py --allow-orphans` (coverage table) |
| Which modules are imported but not in the graph, or on disk but not imported? | the `graph` stage report (`--stages graph`) |
| What did the last merge do to each record (replaced / added / carried / renamed / dropped)? | `dataset/.pipeline/merge.json` |
| Is the shipped file structurally sound (every column, no stub prose, no leaked Lean, row loss)? | `python3 scripts/dataset_check.py --strict` |
| What does this machine lack to run any of it? | `python3 scripts/dataset_pipeline.py --check-env` |

`--estimate` is the canonical pre-flight: it runs every stage in reporting mode and
writes `dataset/.pipeline/state.json`.

## Rules the pipeline keeps

1. **Author prose is never rewritten.**  A blueprint entry a person wrote is the
   statement of record, in the blueprint and in the dataset.  The pipeline writes
   informal statements only into entries it created itself (stubs from the `blueprint`
   stage, marked as such).  Regenerating an author's entry is an explicit, separate
   action (`blueprint_restate.py --replace-prose`), never part of a run.
2. **Citations come only from attached texts.**  A text is matched against the whole
   dataset once; "matched" means the blueprint cites it.  `--rematch` is the only way to
   match a cited text again.  Tags are tied to texts by the citations that result, or by
   an explicit `--source TAG=PATH` / `sources.py register`.
3. **Incremental, never from scratch.**  The `dataset` stage merges into the shipped
   file: records of built declarations are replaced or added; records of unbuilt modules
   are carried over and reported; a record is dropped only when its declaration exists
   nowhere, or has been renamed and the new name is built.  The file is never truncated
   by a partial run, and `--only` / `--modules` restrict every stage to a chosen set.
4. **A model call is a deliberate act.**  Every paid stage prints what is outstanding
   and the estimated cost before it starts, asks unless `--yes`, refuses a model below
   the tier floor, and runs read-only in an empty directory.  A script run on its own
   must not spend unless generation is explicitly requested (`--generate`): a flag that
   describes itself as a migration or a report is one.  Nobody, human or agent, runs a
   paid stage on someone else's behalf without being asked; the spend lands on the
   account of the CLI that is logged in.
5. **Persistence is keyed by content.**  A cached statement is keyed by the mathematical
   core of its formal statement (definitions and the declaration, with imports, context
   and instance stubs stripped), so a builder improvement never invalidates prose and a
   change to the mathematics always does.  Ratings, citations and notes are keyed by
   declaration name and live in the entry or file that carries them.
6. **Vendor-neutral.**  Every model stage is one structured-output call to a CLI; the
   Claude Code and OpenAI Codex CLIs are interchangeable (`--backend`), and the files a
   run produces are identical either way.
7. **The verified column is `proof`.**  `formal_statement` is best effort and its compile
   rate is measured, not assumed.  `verify` runs after every `dataset` stage.

## Known gaps (2026-10-19)

- **Rule 1 is not yet enforced in code.**  The `statements` stage regenerates the prose
  of every record whose statement is not in the cache, including entries whose prose a
  person wrote, and `blueprint_restate.py --apply-only` writes it into those entries.
  The fix is to restrict both to stub entries (and entries the pipeline wrote earlier),
  and to derive `statement_source` from whether the entry was a pipeline stub.
- **The prose cache duplicates the blueprint.**  With rule 1 in force, "needs a
  statement" is simply "the entry is still a stub", and the cache's remaining job is
  change detection (rule 5).  Decision pending: keep it as the persistence layer, or
  write statements straight into the entries with the statement key kept in the entry.
- **Coverage is one command per question**, not one status command.  A single
  `--status` that prints all seven answers would be the natural next step.
