# Blueprint Extraction Pipeline

A multi-agent pipeline that documents every **compiling** Lean declaration in
`TCSlib/` as leanblueprint LaTeX — an informal mathematical description bound to its
formal `\lean{...}` reference and its `\uses{...}` upstream dependencies. The output
is meant to be mined into a dataset of *(informal statement, Lean statement, upstream
definitions)* triples.

## Why this shape

leanblueprint entries already encode exactly the three things the dataset needs:

```latex
\begin{theorem}[Singleton bound]
\lean{ErrorCorrectingCodes.Codeword.singleton_bound}   % formal reference
\leanok
\uses{ErrorCorrectingCodes.Codeword.dist_le_length}    % upstream dependency
Assuming $\alpha$ is nontrivial, a code $C\subseteq\alpha^n$ with minimum distance
$d$ satisfies $|C| \le |\alpha|^{\,n-d+1}$.                % informal statement
\end{theorem}
```

The exact Lean source and full transitive upstream set are always recoverable from the
`\lean{...}` name via `dep_graph.json` (line ranges) and `scripts/query_deps.py`.

## Source of truth: `dep_graph.json`

`dep_graph.json` (built by `scripts/build_dep_graph.py` from the compiler's `.ilean`
artifacts) lists, per module, every declaration with its line range and dependencies.
**A module appears in the graph iff it compiled.** Source files on disk that are absent
from the graph did not compile and are **excluded by design** — we only document real,
`\leanok`-able statements. The planner prints these under "Intentionally skipped" and
records them in `manifest.skipped_non_compiling`.

If you fix a previously-broken file, rebuild the graph so the pipeline picks it up:

```bash
lake build                                  # regenerate .ilean artifacts
python3 scripts/build_dep_graph.py          # refresh dep_graph.json
```

## Components

| Component | Role |
|---|---|
| `scripts/blueprint_enumerate.py` | **Plan.** From `dep_graph.json`, emit one work unit per module listing the documentable, not-yet-covered declarations (with docstring, signature, line range, and resolved `\uses`). |
| `.claude/agents/blueprint-writer.md` | **Write.** One subagent per module turns a work unit into LaTeX entries in the module's chapter `.tex`. Writes prose only — never edits Lean, never writes proofs. |
| `.claude/commands/blueprint-extract.md` (`/blueprint-extract`) | **Orchestrate.** Runs the planner, fans out `blueprint-writer` agents in parallel batches, then assembles + validates. |
| `scripts/blueprint_assemble.py` | **Assemble.** Wire newly-created chapter files into `blueprint/src/chapter/main.tex`. |
| `scripts/blueprint_validate.py` | **Validate.** Cross-check every `\lean`/`\uses` against `dep_graph.json`; report orphans, dangling refs, and per-area coverage. |

## Coverage policy

Documented kinds: `theorem`, `lemma`, `def`, `abbrev`, `structure`, `inductive`,
`class`. Skipped: `instance`, `example` (plumbing, not statements). The set is defined
once in `KIND_ENV` in `blueprint_enumerate.py`.

## Idempotency

The planner skips any declaration whose name already appears in a `\lean{...}` anywhere
in the blueprint, so re-running only documents **new** Lean. Use `--include-covered` to
re-emit everything.

## Usage

```bash
# Plan only — see the work list and what would be skipped, spawn nothing
/blueprint-extract --plan-only

# Full sweep: plan -> fan out subagents -> assemble main.tex -> validate
/blueprint-extract

# A single module
/blueprint-extract --module BooleanAnalysis.LMN.GateMerge
```

Or drive the deterministic steps directly (no agents):

```bash
python3 scripts/blueprint_enumerate.py        # writes blueprint/.work/
python3 scripts/blueprint_assemble.py         # after .tex files are written
python3 scripts/blueprint_validate.py         # coverage + integrity report
```

## Building the dataset

`scripts/dataset_pipeline.py` runs every step from the Lean sources (and the texts the
statements came from) to a verified `dataset/tcslib_theorems.jsonl.gz` -- graph, reference
ingestion, blueprint stubs, LLM-written statements, difficulty ratings, citations,
informalized proofs, the full build, and the checks -- *incrementally*: every LLM product
is cached per declaration, and the final build is merged into the shipped dataset (new and
changed records replaced, records of unbuilt modules carried over, only deleted
declarations dropped).  `--only` / `--modules` restrict every stage to chosen records.
`dataset/README.md` documents the stages, the merge rules, the model policy and the
record schema.

```bash
python3 scripts/dataset_pipeline.py --check-env           # toolchain on this machine
python3 scripts/dataset_pipeline.py --estimate            # report, spend nothing
python3 scripts/dataset_pipeline.py --build --yes --source AB09=texts/ch09.pdf
python3 scripts/dataset_pipeline.py --modules Complexity.Ch09 --yes
python3 scripts/dataset_pipeline.py --backend codex --model gpt-5 --yes   # Codex instead of Claude
```

The text a formalization came from is attached by whoever submits it (`--source
TAG=path`, `TAG` being the docstring citation tag of policy.md §2); the builder does not
search for sources.  `python3 scripts/sources.py` shows every text, tag and Lean file with
what it still needs, and `sources.py add TAG=path` attaches and matches a text.  Uncited
theorems get informalized proof notes instead of citations.  The LLM stages run on the
Claude Code CLI or the OpenAI Codex CLI (`--backend`, proofmatch/agents.py); the caches
and outputs are identical either way.

The deterministic core is still `scripts/build_dataset.py` (no LLM), one record per
theorem/lemma with `id`, `informal_statement` (the blueprint prose for the matching
`\lean{}`), `formal_statement` and `proof`:

```bash
python3 scripts/build_dataset.py            # -> dataset/tcslib_theorems.jsonl (+ .gz)
python3 scripts/build_dataset.py --limit 20 # quick sample
python3 scripts/build_dataset.py --no-proof # statements only (fast)
python3 scripts/build_dataset.py --only NAME ... --out patch.jsonl   # a few records,
python3 scripts/dataset_splice.py patch.jsonl                        # spliced back in
```

- `formal_statement` is a self-contained Lean file: the external imports of the
  declaration's module closure, the **upstream definitions** the statement depends on
  (full, topologically ordered, each in its namespace, with the instances they need and
  the `open ... in` prefixes written in front of them), then the theorem **statement with
  its proof replaced by `sorry`**.
- The dependency walk takes the transitive closure, over **definition-kind nodes only**,
  of the definitions that appear **in the statement text** -- so proofs are dropped and
  proof-only lemmas are excluded.
- `proof` is the full dependency closure flattened in compile order with the original
  proof bodies (the verified column).

The underlying graph is also queryable directly via
`python3 scripts/query_deps.py upstream NAME --tcslib-only`.

## Work-unit schema (`blueprint/.work/<Module>.json`)

```json
{
  "module": "TCSlib.BooleanAnalysis.LMN.GateMerge",
  "lean_file": "TCSlib/BooleanAnalysis/LMN/GateMerge.lean",
  "target_tex": "blueprint/src/chapter/BooleanAnalysis/LMN/GateMerge.tex",
  "target_exists": false,
  "chapter_title": "Gate Merge",
  "decls": [
    { "name": "LMN.mergeGates", "kind": "def", "env": "definition",
      "startLine": 21, "endLine": 25, "uses": [],
      "doc": "Merge two gate arrays ...", "signature": "def mergeGates ... :=" }
  ]
}
```

`blueprint/.work/` is regenerable and git-ignored.
