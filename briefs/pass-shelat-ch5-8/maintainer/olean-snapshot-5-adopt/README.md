# Olean snapshot #5: adoption at the #340 + #346 merges (2026-11-17)

- **New T:** `3f540c22360c869069a0fba684e23ce6f3cb20db` (merge of #346, after #340's merge `7152e62f`).
- **Source:** Gate 44 round 2's replay `olean-replay-g44b` of T44′ `bee027f0` (tip × #340 × #346 with LE-g44), audited CLEAR in Gate 44 round 2.
- **Step-3 diff** of the merge against `bee027f0`: empty (`step3-diff.txt`; T44′ recomputed locally).
- **Snapshot #4 at retirement:** 0/0/0 against `6607620d…` (`v4-final/`).
- **Adoption:** `Mathlib/` overlay removed; map `olean-snapshot.map-3f540c22.tsv`, SHA-256 `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9` (= the audited g44b map), 1458 entries (TCSlib 1425, audits 2, PFR 31); files manifest SHA-256 `12457f3240b07e4bb3121b5c9bcc8864a5d24c7d01c2f6967b8224f1ccbac650`.
- **basecheck:** init at `3f540c22` (1427 modules) against g44b's checked state: RESULT OK.
- **Swap:** #4's oleans deleted; g44b moved to `$SP/olean-snapshot`; rehash 0/0/0 (`v5/`). `olean-replay-346c` deleted (superseded).
- Not adoptable any more: the GSW 6a replays `olean-replay-6a-o1`/`-stmt` (built on #4; the root overlaps) — they re-replay on #5.
