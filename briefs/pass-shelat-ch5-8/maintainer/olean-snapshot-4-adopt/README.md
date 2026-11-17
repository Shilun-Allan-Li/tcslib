# Olean snapshot #4: adoption at the #352 merge (2026-11-17)

- **New T:** `463f224414ab7615e54104be353bfcda9dfceda7` (merge of #352, bb1-sim group helpers).
- **Source:** the re-replay of #352 on snapshot #3 (`$SP/olean-replay-352`; `briefs/pairings/fills/bb1-sim/statements-final-r1/phase2b-352.md`): merge tree `3029d8c3`, 12 modules rebuilt (rc 0, 0 errors), state 1422/1422 OK.
- **Step-3 diff** against `3029d8c3`: empty (`step3-diff.txt`).
- **Snapshot #3 at retirement:** rehash 0/0/0 against map `e9dfbfdd…` (`v3-final/`).
- **Adoption:** `Mathlib/` overlay removed; map `olean-snapshot.map-463f2244.tsv`, SHA-256 `6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7`, 1453 entries (TCSlib 1420, audits 2, PFR 31); files manifest `olean-snapshot.files-463f2244.txt`, SHA-256 `4364054c7f864102947e807f4da9606a0630479044849b8cdb962c98a3fbccc0`.
- **basecheck:** init at `463f2244` (1422 modules) against the replay's checked state: 0 disagreements, RESULT OK (build revs: `cf7d28f7` 1410, `3029d8c3` 12).
- **Swap:** #3's oleans deleted, the replay moved to `$SP/olean-snapshot`; rehash 0/0/0 (`v4/`).
- #346's replay on #3 (`olean-replay-346b`) is no longer adoptable (shared `BonehBoyen*` downstream); #346 re-replays on #4.
