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
| `leanelab-o.sh <worktree> <olean dir> <file.lean> <overlay>` | the same, writing the module's `.olean` into the overlay (a copy-on-write clone of the snapshot, passed as both the olean dir and the overlay); used to compile a change into a clone before its replay |
| `mk-next.sh <name> <worktree dir> <branch> <snapshot-tree commit> <prev snap> <prev log> <new snap> "<base label>" "<label>" <n changed>` | merge the campaign into a PR branch (stopping before any push if a check fails), then write and precheck its merged-tree replay `$TCSLIB_SCRATCH/fills/replay/replay-<name>.sh`, chained from the previous snapshot |
| `bootstrap-snapshot.sh <worktree dir> <name> [--resume]` | build a first olean snapshot on a machine that has none: every module the root `TCSlib.lean` imports transitively (886 at 2026-11-04, the set of the earlier snapshots), in dependency order (`bootstrap_order.py`), one at a time through `scripts/lean_check_tree.sh` into `$TCSLIB_SCRATCH/<name>`; stops at the first failure. Modules that need a package with no oleans (on the cloud machine, `PFR`) are left out with their importers and listed in `skipped-<name>.txt`. `--resume` continues a killed run, or one stopped on a module now left out, after checking the Lean tree, the order prefix and the oleans. The last log line is exactly `# modules=N failed=0` |
| `declfreeze.py <base.lean> <head.lean> [authorized,…]` | compare declarations: publics added or removed, statement changes, body changes (authorized or not), private changes |
| `privstmt.py`, `stmtcheck.py`, `census.py`, `codeonly.py`, `imports.py`, `axprobe.py` | declaration statements, counts, comment-stripped code, imports, axiom-print probes |
| `pairdiff.py <head screen> <earlier screen>…` | new and removed pairs between copy-text screens (`scripts/copy-text-screen-v3.py`) |
| `mkdownmulti.py <repo> <graph dir> <out> <module>…` | the union of modules' downstream closures in topological order, without the root `TCSlib`; needs `graph.py` (its graph dir is this folder) |
| `fillinputs.py <repo> <rev> <module path> <outdir>` | a fill's build inputs at a revision, read with `git show`: the order list (the upstream closure of the owned module and of every module downstream of it, without the root `TCSlib`, in topological order), its Mathlib roots, and the base sorried declarations per module (with a `TOTAL` line) |
| `staticsorry.py <worktree> <replay log>` | compare a replay log's sorry counts with a static count |
| `mkreplay.py …` | write a chained replay script: prechecks (the pushed head, a clean tree, pinned blobs, the previous replay's pass, the list count, no root, a fresh snapshot), then `lean_check_tree.sh` per module |
| `mkbundle-mixed.py <root> <lean-rev> <other-rev> <out> <order> [--verify]` | build an audit bundle: `TCSlib/` files from one revision, the records from another |
| `verifybundle.py <export root> <bundle> <order>` | check a bundle against a `git archive` export |
| `stage.sh <folder> <bundle> <lean-rev> <records-rev> <list> <readme intro> <findings name>` | build, verify and stage a gate folder in `exchange/outbox/gates/` |
| `mdreflow.py <file> <line>…` | reflow the Markdown list items or paragraphs containing the given lines to 100 columns, keeping backtick spans whole |
| `manifest.py <records worktree> <gate dispatches> <out>` | the 2026-10-18 restructure's dry-run manifest (kept as the record of how paths were mapped) |
| `issue2.py plan \| apply <base> \| dispatch <ancestor>` | wave 1's brief issuer, kept for reference (its draft paths are wave 1's) |
| `lean/` | the seed-inclusive definition inventory (`DefInventorySeeds.lean.part.txt`) |
