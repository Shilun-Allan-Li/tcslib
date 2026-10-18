# Maintainer tools (Seyoon's campaign workflow)

Small, standard-library tools for the formalization campaign's maintainer loop: elaborating
changed modules, freezing declarations, replaying downstream closures, screening for copied text,
and building audit bundles. None of them builds the library: Lean runs only through
`leanelab.sh`, and replays through `scripts/lean_check_tree.sh`.

Two environment variables locate the working areas:
- `TCSLIB_SCRATCH`: the scratch directory, holding worktrees, olean snapshots, logs and lock
  slots. Default `~/.tcslib-scratch`.
- `TCSLIB_REPO`: the main checkout. Default `~/tcslib`. The dispatch exchange is
  `$TCSLIB_REPO/exchange/`.

Run Python tools with `python3 -I`.

| Tool | What it does |
|---|---|
| `leanelab.sh <worktree> <olean dir> <file.lean>` | elaborate one file against an olean tree: at most 2 at once machine-wide (lock slots under `$TCSLIB_SCRATCH/locks`), `lean -j4` under `nice -n 10` |
| `declfreeze.py <base.lean> <head.lean> [authorized,…]` | compare declarations: publics added or removed, statement changes, body changes (authorized or not), private changes |
| `privstmt.py`, `stmtcheck.py`, `census.py`, `codeonly.py`, `imports.py`, `axprobe.py` | declaration statements, counts, comment-stripped code, imports, axiom-print probes |
| `pairdiff.py <head screen> <earlier screen>…` | new and removed pairs between copy-text screens (`scripts/copy-text-screen-v3.py`) |
| `mkdownmulti.py <repo> <graph dir> <out> <module>…` | the union of modules' downstream closures in topological order, without the root `TCSlib`; needs `graph.py` (its graph dir is this folder) |
| `staticsorry.py <worktree> <replay log>` | compare a replay log's sorry counts with a static count |
| `mkreplay.py …` | write a chained replay script: prechecks (the pushed head, a clean tree, pinned blobs, the previous replay's pass, the list count, no root, a fresh snapshot), then `lean_check_tree.sh` per module |
| `mkbundle-mixed.py <root> <lean-rev> <other-rev> <out> <order> [--verify]` | build an audit bundle: `TCSlib/` files from one revision, the records from another |
| `verifybundle.py <export root> <bundle> <order>` | check a bundle against a `git archive` export |
| `stage.sh <folder> <bundle> <lean-rev> <records-rev> <list> <readme intro> <findings name>` | build, verify and stage a gate folder in `exchange/outbox/gates/` |
| `mdreflow.py <file> <line>…` | reflow the Markdown list items or paragraphs containing the given lines to 100 columns, keeping backtick spans whole |
| `manifest.py <records worktree> <gate dispatches> <out>` | the 2026-10-18 restructure's dry-run manifest (kept as the record of how paths were mapped) |
| `issue2.py plan \| apply <base> \| dispatch <ancestor>` | wave 1's brief issuer, kept for reference (its draft paths are wave 1's) |
| `lean/` | the seed-inclusive definition inventory (`DefInventorySeeds.lean.part.txt`) |
