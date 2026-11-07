# Current 25-file draft screen method

This review compares the same complete 25-source population on both sides:
API prerequisite commit `1160c18f03fd318f0dec25738790935fa61379d4` and an
uncommitted current landing capture taken before comment cleanup. It is not
an issued packet or a final gate snapshot. `capture.py` verifies the full
commit and all 25 full Git blob objects before writing the baseline inputs,
and verifies that the actual current sources stayed stable during capture.
All 50 input files are retained inert as `.lean.txt` copies, with hashes in
`capture.json`. No Git write or source edit is performed.

`run_screens.py` makes the two executable input trees in a fresh directory
under `/private/tmp`. It runs the repository's unmodified
`scripts/copy-text-screen-v3.py`, baseline then head, with Python isolated
mode and niceness 10. Each screen holds the shared scratch `locks/screen`
directory with its live PID. Lock acquisition/release and any stale-lock
reclamation are recorded in `lock-events.jsonl`; a live holder is waited
for. The original script bytes and hash are retained. Raw stdout/stderr is
written without truncation. After both screens, the unmodified
`devtools/seyoon/pairdiff.py` compares the full outputs.

The tool reports **directed textual candidates**: declarations whose
normalized body has at least 60 characters, like proof/term kinds only,
greedy common tiles of at least 25 characters, and at least 60 reproduced
characters covering half of the source body. Both within-file and
cross-file comparisons are included. Proof and term are syntactic classes:
a `def` with an `inj'` proof field is still a term to this tool. Directed
pair counts and reproduced-character totals are not counts of independent
semantic copies, unique duplicated text, lines, or ledger percentages.
The body delimiter is also a text/depth heuristic: a depth-zero `let ... :=`
in a theorem's type can start the extracted region before the actual proof.
Matches in approved let-view private headers therefore require source
classification as statement/transport text rather than automatic proof-copy
classification. The screen is run unchanged; it is not a replacement for
the separate Lean-aware header freeze.

`index_candidates.py` does not repeat matching. It uses only the reviewed
v3 parser helpers to recover candidate labels, declaration kinds and source
spans, then indexes every raw candidate and the complete label-pair delta.
Its stripping routine additionally records raw offsets without changing
the stripped text. It checks that its declaration and pair counts agree
with the raw screen summaries, and retains all new/gone lists without a
cap. Grouped semantic review distinguishes moved source, executable data,
proof copies, shared proof helpers and short glue. It is a bounded review
of every new cross-file family and meaningful new in-file edges, not an
exhaustive semantic-duplication theorem.

`reconcile_assignments.py` separately checks the named T1/T2/T2b/T3/T5/T6
families against the captured sources. This prevents an unchanged
first-entry twin or a frozen data table from disappearing into a
new-pairs-only summary. Its source checks are not elaborations or approvals.

After both tiling runs, `verify_comment_linkage.py` independently captures
the final actual 25 sources and compares the trusted parser's complete
extracted declaration names, namespaces, kinds, flags and normalized
bodies, and the screened labels/kinds/bodies. Offsets and line numbers are
ignored. The resulting separate equivalence receipt links the raw
pre-comment screen to current proof content without changing its original
inputs or claiming another tiling run.

The foreign-field/resource and public-home holds remain separate from
duplication review. No new debt acknowledgment, API approval, source fix,
Lean check, cache change, replay or gate closure is inferred from this
screen.
