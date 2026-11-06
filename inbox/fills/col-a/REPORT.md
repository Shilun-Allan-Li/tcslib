# Fill col-a: REPORT (checkpoint 1, interim)

- **Unit:** col-a (`ThreeColoring/Protocol.lean`; helpers `ThreeColoring/ColRep*.lean`).
- **Base:** `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (head of PR #210, branch
  `cryptography/pass-shelat-ch2-4-eqlemmas`); local branch `fill/col-a`, never pushed, never rebased.
- **Exchange start commit:** `3f4e04cff265acc6681a2dc4694bebabe5448d95`.

## Status at this checkpoint

| Target | Status |
|---|---|
| `R3COL_witnessRelation`, `decidable` clause | **filled** (`exact ColRep.R3COL_decidable`; helper `ThreeColoring/ColRepWitness.lean`) |
| `colRep_efficientProverProof` | in progress |

`Protocol.lean` and `ColRepWitness.lean` check with zero errors; `Protocol.lean`'s only `sorry`
warning is `colRep_efficientProverProof`.

## Environment (addendum items 1–3)

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 memory limit 14,337,302,528 B,
  in use (usage − total_cache + total_shmem) 27,406,336 B, **headroom 13.33 GiB**; clone on ext4
  `/dev/vda`, **29.44 GiB free**. Pass.
- Toolchain `leanprover/lean4:v4.25.0` installed by elan after the preflight (disk re-checked
  before the cache: 29.0 GiB free).
- Cache store (`evidence/logs/cache-store.log`): absent before the first fetch (0 files).
- Narrowed fetch: 66 roots (identical to `inputs/col-a/roots.txt`), "Attempting to download 2107
  file(s)", "Decompressing 2107", "Completed successfully", exit 0.
- Packages (`evidence/logs/packages-check.log`): last line "RESULT: all present packages match the
  manifest"; ABSENT: doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean. Zero-size oleans: 0.
- Cache probe (`evidence/logs/cache-probe.log`): `import Mathlib.Algebra.BigOperators.Field`, exit 0.
- Bootstrap (`evidence/logs/bootstrap.log`): order-list modules 1–122 (through
  `ThreeColoring/ProtocolProofs`), all exit 0. `/usr/bin/time` is not installed; start/end times and
  peak child RSS are logged by a `getrusage` wrapper.

(The final report replaces this file.)
