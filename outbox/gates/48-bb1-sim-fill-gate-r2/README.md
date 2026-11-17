# Gate 48 round 2 · the bb1-sim gate (#357) · G48-01 fixed by LE-g48

Read `pack-r2.md` first. This folder's earlier content (exchange `5976f1a0`) was a round-2 pack for a debt ruling that
was superseded before dispatch; this commit replaces it.

Files:
- `pack-r2.md`: the round-2 pack (questions, pins, evidence summary, what carries over).
- `findings-r1.md`: round 1's findings, filed verbatim.
- `resolutions-r1.md`: the maintainer's resolution of G48-01 (landing edit LE-g48).
- `le-g48.md`, `le-g48.diff.txt`, `le-g48-evidence.zip`: the edit and its Lean evidence (the zip carries its own
  `SHA256SUMS` and `omitted-SHA256SUMS`).
- `records-r1-r2.diff.txt`: `git diff e6cdf4d4 3bc01cd7` over the ledger, `cleanup-stages.md`, the fill review and
  the plan's decision log.
- `pr357-description-r3.md`: PR #357's description as sent after LE-g48.
- `SHA256SUMS`: covers every other file here.

PR #357's head is `dfdc56f21898abe2d9d6cef83b0cfe57da87d28d`. The round-1 pack is
`outbox/gates/48-bb1-sim-fill-gate/` at exchange `827065642ff5965c6f7c51c592f18b9f32dc2811`.
