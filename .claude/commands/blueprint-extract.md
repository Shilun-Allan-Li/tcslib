# /blueprint-extract

Orchestrate many `blueprint-writer` subagents to document every Lean declaration in
`tcstcslib/` as leanblueprint LaTeX — informal description + `\lean{...}` formal
reference + `\uses{...}` upstream dependencies — so the result can be mined into a
dataset of (informal statement, Lean statement, upstream definitions).

## Usage
- `/blueprint-extract` — plan + fan out across all modules with undocumented declarations
- `/blueprint-extract --module <Name>` — only that module (e.g. `BooleanAnalysis.LMN.GateMerge`)
- `/blueprint-extract --plan-only` — run the planner and report the work list; spawn nothing
- `/blueprint-extract --include-covered` — re-document declarations even if already present

## Base directory

All data lives under `tcstcslib/` (it contains `dep_graph.json`, `TCSlib/`, `blueprint/`,
`scripts/`). Determine the base: if `dep_graph.json` exists in the current directory use
`.`, else use `tcstcslib`. Run every script and pass every path relative to that base.
Below, `BASE` denotes it.

## Instructions

Read the arguments after the command. Then:

### 1. Ensure the dependency graph is fresh (cheap check)
- Confirm `BASE/dep_graph.json` exists. If it does NOT, tell the user to build the
  project and run `python3 scripts/build_dep_graph.py` first, then stop.
- You do not need to rebuild it otherwise; it is the planner's source of truth.

### 2. Plan the sweep (deterministic, no LLM)
Run the planner, forwarding `--module` / `--include-covered` if present:
```bash
cd BASE && python3 scripts/blueprint_enumerate.py [--module <Name>] [--include-covered]
```
This (re)writes `blueprint/.work/manifest.json` and one `blueprint/.work/<Module>.json`
work unit per module that has undocumented declarations.

Read `blueprint/.work/manifest.json`. Show the user a short summary: number of modules
with work, total declarations to document, and which target files are NEW vs appended.

`dep_graph.json` is the source of truth and only contains modules that **compiled**.
Source files absent from it did not compile and are listed under
`manifest.skipped_non_compiling`; these are excluded **by design** (we only document
real, `\leanok`-able statements). Report that count, but treat it as expected, not an
error.

**If `--plan-only`**: stop here.

### 3. Fan out one `blueprint-writer` subagent per module
Iterate `manifest.units` (each has `module`, `work_file`, `target_tex`, `uncovered`).
Spawn `blueprint-writer` subagents **in parallel batches of up to 6** (multiple Agent
tool calls in a single message). Do not exceed ~6 concurrent — these write files and a
larger fan-out risks contention and rate limits. Wait for each batch to finish before
starting the next.

For each unit, the subagent prompt is:
```
Document module <module> as leanblueprint LaTeX.
Base directory: BASE
Work unit: BASE/<work_file>
Follow your agent instructions exactly: write/append BASE/<target_tex>, one entry per
declaration in the work unit, each with \lean{...}, \leanok, the given \uses{...}, and a
faithful informal description of the statement (never a proof). Report the labels added.
```
Collect each subagent's reported labels/counts. If a subagent reports a declaration it
could not describe, note it for the final summary (do not retry automatically).

### 4. Assemble main.tex
After all batches complete:
```bash
cd BASE && python3 scripts/blueprint_assemble.py
```
This appends `\input{chapter/...}` lines for any newly created chapter files. Report what
was wired in.

### 5. Validate
```bash
cd BASE && python3 scripts/blueprint_validate.py
```
Surface: orphan `\lean` labels, dangling `\uses`, and remaining uncovered declarations
per area. These are the quality signals for the dataset.

### 6. Final summary
Report:
- modules processed and total entries added,
- coverage before/after (from validate),
- any declarations subagents flagged as undescribable,
- any orphan/dangling issues to review,
- next step: rebuild the blueprint (`cd BASE/blueprint && ...` per its README) to view,
  or re-run `/blueprint-extract` to pick up newly added Lean.

## Notes
- The pipeline is **idempotent**: already-documented declarations (those with a
  `\lean{...}` anywhere in the blueprint) are skipped by the planner, so re-running only
  documents new Lean. Use `--include-covered` to override.
- Subagents only ever touch their own `target_tex`; they never edit Lean, `main.tex`, or
  each other's files.

$ARGUMENTS
