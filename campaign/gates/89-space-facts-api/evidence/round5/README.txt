Gate 89 round 5's evidence (maintainer, 2026-11-04). PR #181 on lean/logspace-move, head
98912ab293dc329b3f7274ee27977fa19789ce78. Round 5's Lean commits (patches/): d789d6db (the BL-1
re-points, the move of two_pow_bits_le to Machines/Bin, wP_eq, the removal of TQBFHard.wP_le) and
98912ab2 (one docstring). The merges b0f95123 and 98912ab2's parent bring in campaign records and change
no Lean.

elab/        elab_chain.sh: the round-5 files and the moved lemma's unchanged users, in dependency order,
             compiled with -o into a copy-on-write clone of oleans-lsm4 (tools/leanelab-o.sh); PrimeFind and
             BPLInP re-run after their last edits. Empty outputs except RecordTable's four sorry warnings,
             which the base has too.
freeze/      declfreeze.py, each round-5 file at 227d92ee (round 4's head) against the head, with each file's
             authorized body changes; moved-lemma.txt: two_pow_bits_le byte-identical.
api-search/  every origin ref, for two_pow_bits_le, wP_eq and TQBFHard.wP_le.
ls1-search/  ls1search.py (the logSpace candidates), bitsweep.sh (portable; bitsweep-round4head.tsv
             reproduces the auditor's 191 rows at round 4's head), bitcontext.py, bitclasses.py and
             bitsweep-classes.md (every group of the sweep at the head), classification.md.
screen/      copy-text-screen-v3.py over 33 files at a git-archive export of 711f5444 and at b0f95123
             (the head but for one docstring, which the screen strips); under the screen lock.
lint/        lint.sh: campaign_style_lint over five directories and style_lint over the round-5 files,
             at the export and the head.
merged-tree/ replay-lsm5.sh (fills/replay/mk-next.sh), its 209-module closure, the precheck's result.
