# Olean snapshot #3: adoption at the #351 merge (2026-11-17)

- **New T:** `cf7d28f7159b46033e8b8ae170954f9575e5d145` (merge of #351, bb1-sim Games statements).
- **Source:** the phase-2 replay R1 of `land/bb1-sim-games` `dfacac35` (`briefs/pairings/fills/bb1-sim/statements-final-r1/phase2.md`): a `cp -al` of snapshot #2 with 181 modules rebuilt (rc 0, 0 errors), state 1422/1422 OK.
- **Step-3 diff** (`git diff --name-only <merge> <head> -- '*.lean' lean-toolchain lake-manifest.json`): empty (`step3-diff.txt`).
- **Snapshot #2 at retirement:** rehash 0/0/0 against map `95493449…` (`v2-final/`).
- **Adoption:** `Mathlib/` overlay removed; `snapmap.py make` → map `olean-snapshot.map-cf7d28f7.tsv`, SHA-256 `e9dfbfddfd6ca253f9fd5ee6c3efe868f8614083794312c89d32032564fea53d`, 1453 entries (TCSlib 1420, audits 2, PFR 31); `snapshot.py` → files manifest `olean-snapshot.files-cf7d28f7.txt`, SHA-256 `1e9a3ba7c0dd8b18c2d38d498fff30b5ee88a48f8c560673484fb1049cb85733`.
- **basecheck:** `stateplan.py init` at `cf7d28f7` (1422 modules) against R1's checked state over its full order: 0 key/olean disagreements, RESULT OK (`basecheck.out`, `state-init-cf7d28f7.json.gz`).
- **Swap:** #2's oleans deleted, R1 moved to `$SP/olean-snapshot`; rehash 0/0/0 against the new map (`v3/`).
- **Discarded:** R2 (`land/bb1-sim-group` replay), no longer adoptable after #351 (shared `BonehBoyen*` downstream); its evidence is in the phase-2 zip. #352 and #346 re-replay on #3.
- Tools: `olean-rebase-dl-oleans-2/olean-rebase-evidence.zip`, `olean-advance-a6d01b1b/tools-used/`.
