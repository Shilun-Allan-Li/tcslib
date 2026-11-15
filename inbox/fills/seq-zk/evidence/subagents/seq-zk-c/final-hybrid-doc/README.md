# Final HybridRecursion proof-stage comments

At the lead's request following a's final documentation audit, added exactly three internal
comments: averaging the continuation potential over real-prefix coin tables; snoc reindexing
and conditional-gap averaging; and the published telescope bounding all adjacent gaps.
No public statement, tactic, definition, imported module, or mathematical premise changed.

Old source SHA5277132bb0013c9e290f17272947624e6fd33f17fb9029608d9821affe1e92da.
Final source SHA631056b5eaf933c2e920671fa9308e97eff5849bf1f465528296e16c0c5bb001,
93lines/max94columns. Before/after whole-source snapshots and the exact stage-comments.patch
are preserved. roundtrip.json records successful git apply --check/apply in both directions
and byte-for-byte verification: deleting those comments or reversing the patch restores
the exact old source; applying the patch restores the exact final source.

The requested ONE native own-tree check passed0errors/0warnings,2.50s actual runtime,
maximum resident set size2,116,354,048bytes. Full raw output, structured result, source hash,
and shared-slot acquire/release evidence are retained. It used LEAN_SLOT_TAG=seq-zk-c,
TCSLIB_OLEANS=the own seq-zk-c tree, shared lean-slot.sh, /usr/bin/time -l, and
scripts/lean_check_tree.sh for HybridRecursion alone. No Lake, timeout, interruption,
additional dependency sweep, frozen-reader edit, new Mathlib root, or other math work.

All171 current withV-fix receipt files remain unchanged; the already-recovered historical
CP3 audit archives also remain untouched. This NEW final-hybrid-doc directory contains all
new evidence. Source and closed evidence are ready for exact final copying.
