# Olean snapshot #6: adoption at the #357 merge (2026-11-17)

- **New T:** `8060f6b767da9e43d1c1f6d32c55b97758b80bd8` (merge of #357 into `cryptography/pass-shelat-ch2-4`).
- **Source:** LE-g48's replay `olean-replay-bb1sim-g48` of #357's head `dfdc56f21898abe2d9d6cef83b0cfe57da87d28d`, audited CLEAR in Gate 48 round 2.
  - Before adoption it rehashed against its recorded map (`mapnoml.py`, `0858dccb…`): 1463 files, 0 extra / 0 changed / 0 missing, 3346 `Mathlib/` symlinks, NthRootLemmas `c0a9cff0…` (`replay-verify.out`).
  - Its checked state (LE-g48 `state.json`, SHA-256 `78f0d483…`) at `dfdc56f2` over the 1432-module order: RESULT OK (`replay-statecheck.out`).
- **Step-3 diff** of the merge against `dfdc56f2` (`*.lean`, `lean-toolchain`, `lake-manifest.json`; `lakefile.lean` included): empty (`step3-diff.txt`).
- **Snapshot #5 at retirement:** 0/0/0 against `fca1b6a3…` (`v5-final/`).
- **Adoption:** `Mathlib/` overlay removed (3346 symlinks + the overlay NthRootLemmas olean, as at #5); map `olean-snapshot.map-8060f6b7.tsv`, SHA-256 `0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf` (= the audited g48 map, byte-equal), 1463 entries (TCSlib 1430, audits 2, PFR 31); files manifest SHA-256 `1ae04ef5f80e99b331d5062546831c9a180354a88181d4233d5eacf57433c86e`, 1463 files.
- **basecheck:** init at `8060f6b7` (1432 modules; `state-init-8060f6b7.json.gz`) against g48's checked state: RESULT OK (`basecheck.out`).
- **Swap:** #5's directory deleted (no Lean process running; other replay trees keep their hard links); g48 moved to `$SP/olean-snapshot`; rehash 0/0/0 (`v6/`). `olean-replay-bb1sim` (#357's pre-LE-g48 replay) deleted (superseded). #5's map and files manifest are kept in `$SP`.
- Not adoptable any more (built on #5 without #357): `olean-replay-cs1` (TS1), `olean-replay-6a-o1`, `-6a-stmt`, `-6a-stmt-g45`, `-6a-readers`, `-6a-fill12`, `-6a-fill86` — each re-replays on #6 before merge-time adoption.
