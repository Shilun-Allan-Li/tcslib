Gate 89 round 4's evidence (maintainer, 2026-11-04). PR #181 on lean/logspace-move, head
227d92ee4a91fa86860d1d1ddf3a98130fa674b9. Round 4's Lean commits (patches/): a7c2a655 (ARMProof),
fe4bdb67 (the move of logSpace_le_size_succ to Basic; BPLInP, SpaceAmplifyPoly), 252bbcb8 (ExpBFS/Run),
227d92ee (ISCountGenCorrect). The merges 248e3796 and 3c091078 bring in campaign records commits and
change no Lean.

elab/        ARMProof against oleans-lsm3 (round 3's fresh snapshot). The rest in a copy-on-write clone of
             oleans-lsm3 (cp -cR): Basic and ISCountMath compiled with -o into the clone
             (tools/leanelab-o.sh), then ISCountGenCorrect, BPLInP, SpaceAmplifyPoly and ExpBFS/Run
             against it (tools/leanelab.sh). Every output is empty: 0 diagnostics. A pre-replay check;
             replay-lsm4 is the merge evidence.
freeze/      declfreeze.py, each round-4 file at b8add1ac (round 3's head) against 227d92ee. moved-lemma.txt:
             logSpace_le_size_succ's statement and proof, ISCountMath at b8add1ac against Basic at the
             head, byte-identical.
ls1-search/  ls1search.py (the logSpace candidates; context.txt) and bitsweep.sh (the binary-length
             sweep; bitsweep-context.txt by bitcontext.py) at the head; classification.md classifies both.
api-search/  every origin ref, for declarations and uses of logSpace_le_size_succ.
screen/      copy-text-screen-v3.py over the 24-file population, at a git-archive export of 711f5444
             and at the head, under the screen lock.
lint/        campaign_style_lint over SpaceComplexity and Randomized at the export and at the head;
             style_lint over the seven round-4 files at the head.
merged-tree/ replay-lsm4.sh (fills/replay/mk-next.sh), its closure and the precheck's result.
