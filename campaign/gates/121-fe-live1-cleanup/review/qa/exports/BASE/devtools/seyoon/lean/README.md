# Maintainer tools (copies, 2026-10-17)

Copies of the maintainer's scratch tools. The session scratchpad lives under `/private/tmp`, and
a nightly cleaner deleted the originals of several on 2026-10-17; `privstmt.py` was rewritten on
`declfreeze.py`'s parser and reproduces its recorded output. They run on the repository's text
only (`python3 -I`), except `leanelab.sh` (the throttled single-file elaboration against an olean
snapshot).

| Tool | Use |
|---|---|
| `declfreeze.py <before> <after> [allowed]` | public declarations added, removed, restated or body-changed; privates added, removed, changed |
| `privstmt.py <before> <after>` | for every declaration present in both, statement changes and body/docstring-only changes |
| `pairdiff.py <head screen> <base screen>` | the copy-text screen's new and gone pairs by name |
| `axprobe.py` | axiom-print probes |
| `leanelab.sh <worktree> <oleans> <file>` | elaborate one file (at most two at a time, `-j4`, niced) |
| `mkbundle-mixed.py`, `verifybundle.py` | gate bundles: Lean from one commit, records from another; verification against an export |
| `graph.py`, `graph2.py` | replay lists: a landed set's downstream closure, root excluded |
| `staticsorry.py`, `sorryset.py` | the static sorry count against a replay log; a brief's base sorry set |
| `mkorder-gen.py`, `mkimportoverlay.py` | a brief's order list; an import overlay |
| `DefInventoryEach.lean.part.txt`, `DefInventorySeeds.lean.part.txt`, `EnumLemmas.lean.txt` | the pre-ship inventory elaborators (the seed-inclusive one from #118's gate) |
