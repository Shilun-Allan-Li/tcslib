# Megafill D's drafting environment (addendum v2.5, Part 1), 2026-10-25

The drafting agent's single clone at the drafting base `fe666d60f21e51438374e7c3f3a966eaa93862c0`,
set up once for the union of the two nearest candidates' Mathlib roots (`spaceConstructible_poly`'s
and E-Q's order lists), and used for every probe of the triage. Every log was written to its final
path from the start. Lean started normally (Part 2 was not needed).

| Step | Result | Log |
|---|---|---|
| Preflight | 4 CPUs; cgroup v1 limit 14,341,881,856 B, memory in use (`usage − total_cache + total_shmem`) 40,030,208 B, so the headroom is 13.32 GiB (floor 4); the clone's filesystem ext4 (not memory-backed), 26,444,976,128 B = 24.63 GiB free (floor 12) | `logs/preflight.log` |
| Toolchain | elan, then `leanprover/lean4:v4.25.0` (archives extracted with `TAR_OPTIONS=--no-same-owner`); `lean --version` and `lake --version` in the log | `logs/toolchain.log` |
| Re-check | 22.11 GiB free after the toolchain (floor 8) | `logs/recheck.log` |
| Cache store | `/root/.cache/mathlib` absent before the fetch: 0 archives | `logs/cache-store.log` |
| Roots | 57: the union of `Savitch`'s order list (182 modules) and E-Q's overlay order list (80 modules at the first overlay; the final overlay's 81 add no root beyond `Mathlib.Data.Nat.Log`, which is in the union) | `logs/mathlib-roots.txt` |
| Narrowed fetch | `TAR_OPTIONS=--no-same-owner lake exe cache get <57 roots>`: exit 0; attempted and downloaded 1,029, decompressed 1,029, no failure; 93 s | `logs/cache-get.log`, `logs/cache-get.time` |
| Manifest | 11 packages present, each matching the manifest's URL and revision; 4 absent (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`), imported by no module of the lists: PASS | `logs/manifest-check.log` |
| Cache check | no empty olean among 1,038; a probe importing the first root elaborated (exit 0) | `logs/cache-check.log` |
| Bootstrap | the 213-module union in topological order: 213/213 exit 0, 0 errors, 33 sorry warnings (agreeing module by module with the union of the two base sorry sets); 1,873 s of Lean time; peak 2,970,904 KiB (`Build/CfgRecord`); per-module time and memory logged | `logs/bootstrap.log`, `logs/bootstrap-order.txt` |
| Bootstrap addendum | `ClassNP/Transducer`, the one module the `Savitch` overlay adds: exit 0 | `logs/bootstrap-addendum.log` |

The host has no `/usr/bin/time`; per-module memory is the children's peak resident set from
`getrusage` (the `MEM` lines). Tools: `tools/runmem.py` (the memory wrapper) and
`tools/subst_hashes.py` (the hash inserter and checker), both megafill C's, copied unchanged;
`tools/run_probe.sh` (new): copies a probe record to the clone's ignored `.lake/probes/`, checks it
with `scripts/lean_check_tree.sh` under `runmem.py`, and writes its output with the record's SHA-256
and the exit status.
