# #252 merged and snapshot adopted

Seyoon reported #252 merged and gate 131 dispatched. The campaign source merge is
`6e43b7a237481d0d03ff3ef47116918e1e835559`. Gate 130 had closed and its complete 335-module replay passed at
`04b0b07d4ea836f52cb645f480b67cdc9e99ea59`. The actual merged tree has all 1,003 Lean blobs
byte-identical to that checked head; all 895 physical object hashes match its
whole output. Adopt `oleans-nspace5` in place; no snapshot is composed.

The existing #253 / gate 131 replay remains valid under START-HERE §4: its three
edited modules have no import path to any of the three newly merged providers,
and the exact prospective tree merges cleanly. The dispatched bundle and
source pins are unchanged. Gate 131 remains open.

#243–#247 and #249 retain their gate closures. Their edited owners have import
paths to the changed providers, so they need refreshed replay evidence before
renewed clearance. See the exact import paths and clean prospective trees in
post-merge-pr-validity.json. #254 is a separate tooling-only PR, with no Lean diff.

The original gate 129 and 130 bundles were archived after their findings were
recorded. Their original hashes and the archive commit are recorded here.
