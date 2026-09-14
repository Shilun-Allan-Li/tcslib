# TCSlib

A Lean 4 library for Theoretical Computer Science.

Official website at <https://shilun-allan-li.github.io/tcslib/>.

# What's TCSlib?

TCSlib formalizes results in Theoretical Computer Science using [Lean 4](https://lean-lang.org) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). Every theorem is machine-checked.

## Areas covered

- **Boolean Function Analysis** — Fourier analysis over the Boolean hypercube, hypercontractivity, Arrow's theorem, and more.
- **Error-Correcting Codes** — Singleton, Hamming, Gilbert–Varshamov, and Johnson bounds; linear codes; list decoding; quantum codes.

# Using TCSlib in your project

To add TCSlib as a dependency, add the following to your `lakefile.lean`:

```lean
require TCSlib from git "https://github.com/Shilun-Allan-Li/tcslib" @ "main"
```

## Matching PDF proofs to TCSlib

The repository includes an auditable Claude Code workflow for comparing a local
PDF or validated Markdown reference with TCSlib proofs. Agent stages run through
headless `claude -p` with `--json-schema` structured output (the `claude` CLI
must be installed and authenticated); model tiers are configured in
`proofmatch/agents.py` (`DEFAULT_MODEL` / `COMPARE_MODEL`, default
`claude-opus-4-8`) with matching prices in `proofmatch/budget.py`:

```bash
# Free local extraction only
python3 scripts/proofmatch.py extract notes.pdf --local-only

# Estimate before paid agent stages
python3 scripts/proofmatch.py estimate notes.pdf

# Full extraction, selective visual repair, search, and comparison
python3 scripts/proofmatch.py run notes.pdf

# Start downstream matching from existing validated Markdown
python3 scripts/proofmatch.py match notes.md
```

Runs are uncapped by default, so no stage is skipped for want of budget; spend
is still tracked and reported. `--max-cost N` optionally caps estimated spend
(capped runs degrade gracefully and persist partial reviews). Verdicts: `same` (proof matches →
`\proofsource` + `\proofstep`), `method_divergence` (statement in the text,
different proof → `\statementsource`), `not_in_text` (too granular for the text
or a bare exercise → queued in `informalize_queue.md` for a later LLM pass that
informalizes the Lean proof), `different`, `uncertain`.

The workflow stores both `notes.raw.md` and `notes.md`. It writes no blueprint
proof-source metadata until the user explicitly approves a generated review with
`python3 scripts/proofmatch.py review RUN_ID`.

Then run `lake update` to fetch the dependency.

## The informal/formal dataset

`dataset/tcslib_theorems.jsonl` pairs an **informal statement** with the
**formal** Lean statement of every documented theorem.  It is built from the
leanblueprint sources:

```bash
python3 scripts/blueprint_validate.py        # \lean / \uses <-> dep_graph.json
python3 scripts/build_informal_statements.py # LLM pass: regenerate the statements
python3 scripts/blueprint_restate.py         # write them into the chapter .tex
python3 scripts/build_dataset.py             # -> dataset/tcslib_theorems.jsonl(.gz)
python3 scripts/build_proof_notes.py         # attach proof_notes
python3 scripts/dataset_hygiene.py           # quality report
```

The contract for the informal half (also in `.claude/agents/blueprint-writer.md`)
is that it **states the claim and nothing else**: hypotheses, conclusion, the
definitions it needs.  It must not carry the proof, a proof plan, significance
commentary, formalisation notes, or repo status.  A pair whose informal half
gives the argument away cannot pose the task the dataset exists to pose.

`scripts/dataset_hygiene.py` enforces that.  It runs over the blueprint sources
by default and over a built `.jsonl` with `--dataset`; `--strict` exits non-zero
on the hard checks (`proof-leak`, `proof-env`, `repo-note`, `title-note`).  The
advisory checks (`identifier-title`, `mangled-title`, `no-statement`,
`lean-internals`) report blueprint entries whose `[title]` is only the Lean name,
or whose prose is thin -- worth fixing, but not defects that ship (a title that
is merely the declaration's own name is dropped from the composed statement by
`build_dataset.py`).

The twelve `blueprint/src/chapter/GraphTheory/Core/*.tex` chapters are generated
rather than hand-written: `python3 scripts/blueprint_restate.py` rebuilds each
entry's body from the statement sections of the declaration's Lean docstring
(the summary line plus the verbatim book statement), dropping the **Book proof**,
**Skeleton**, **Reading** and **Formalisation** sections.  Re-run it after
editing those docstrings; do not hand-edit the bodies, they will be overwritten.

### Regenerating the statements

Blueprint prose is written for someone reading the document in order, which
makes poor dataset prose: entries were anaphoric ("the embedding"), used
variables they never introduced, and spelled mathematics in Lean dot-notation.
`scripts/build_informal_statements.py` rewrites every theorem and lemma
statement from its **formal** statement -- the ground truth -- to the standard
of a handout: every object introduced, every hypothesis rendered, mathematics in
mathematical notation, no reference to anything outside the sentence.

Each result is graded against `scripts/statement_quality.py` before it is kept,
and a failure is re-asked once with the violated rules named. The checks are
`anaphora`, `lean-notation`, `unbound-variable`, `no-claim`, `typewriter`,
`imperative`, `latex-unsafe`, and `tautology` (the last is a fact about the Lean
-- it assumes its own conclusion -- so it is reported, not retried).

Output is cached one JSON file per declaration under
`blueprint/src/references/statements/`, keyed by a hash of the formal statement.
A run is therefore resumable, and a re-run revisits only declarations whose Lean
statement actually changed. `scripts/blueprint_restate.py` writes the cache into
the chapter `.tex` bodies and titles; `build_dataset.py` then picks them up like
any other blueprint prose and records which is which in `statement_source`.

Raise `PROMPT_VERSION` in `proofmatch/statements.py` to invalidate the whole
cache after changing `proofmatch/prompts/informalize_statement.md`.

The pass is resumable and safe to interrupt -- it skips anything already cached,
and stops as soon as it sees a usage limit rather than working through the queue
with every call failing.  To carry on where it left off:

```bash
python3 scripts/build_informal_statements.py --jobs 8   # generate what is missing
python3 scripts/build_informal_statements.py --regrade  # redo what the rubric now rejects
python3 scripts/blueprint_restate.py                    # write into the .tex
python3 scripts/build_dataset.py && python3 scripts/build_proof_notes.py
python3 scripts/statement_quality.py --dataset          # measure
```

Keep `--jobs` low -- 3 is what the full run was completed at.  Each job is a
full `claude -p` process; at 16 this machine paged, and more to the point the
account's usage window was exhausted in one burst and 1264 calls then failed.
At 3 the pass sustained ~14 declarations a minute and never hit the limit.

Applying is reversible.  The first time a regenerated statement displaces a
blueprint body, that body is stashed in the cache entry as `replaced`; if the
statement later stops passing the typesetting guard -- a macro the preamble does
not define, an unbalanced delimiter, a subscript on a brace-expanding macro like
`$x_\bbr$` -- the next run puts the blueprint's own words back instead of
leaving the bad version in the document.  So `blueprint_restate.py` is safe to
re-run at any time, and safe to run on top of itself.

# Building locally

Install Lean following the [setup instructions](https://leanprover-community.github.io/get_started.html), then run:

```
lake exe cache get
lake build
```

# Contributing and discussion

Contributions are welcome — please open an issue or pull request on [GitHub](https://github.com/Shilun-Allan-Li/tcslib).
