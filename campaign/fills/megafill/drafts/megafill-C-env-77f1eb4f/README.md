# Megafill C's drafting environment (addendum v2.5, Part 1), 2026-10-24

The drafting agent's single clone at the drafting base `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532`,
set up once for the union of the three new briefs' Mathlib roots, and used for every pre-ship
check. Every log was written to its final path from the start.

| Log | What it records |
|---|---|
| `logs/preflight.log` | `nproc`, the cgroup (v1, no effective limit) and its counters, `/proc/meminfo`, `df -B1` and `df -T`, and the computation: headroom `MemAvailable` 15.24 GiB (floor 4), 29.49 GiB free (floor 12) |
| `logs/toolchain.log` | elan and `leanprover/lean4:v4.25.0` (archives extracted with `TAR_OPTIONS=--no-same-owner`); `lean --version`, `lake --version` |
| `logs/recheck.log` | the re-check after the toolchain: 27.08 GiB free (floor 8) |
| `logs/cache-store.log` | the cache tool's archive store before the first fetch: absent, 0 archives |
| `logs/mathlib-roots.txt` | the 41 roots: the Mathlib modules the union of the order lists imports directly |
| `logs/cache-get.log`, `logs/cache-get.time` | the narrowed `lake exe cache get`: 1,023 attempted, 1,023 downloaded and decompressed, no failure, exit 0, 70 s |
| `logs/manifest-check.log` | each package present in `.lake/packages` against `lake-manifest.json`: 11 match, 4 absent |
| `logs/cache-check.log` | no empty olean; a probe importing the first root elaborates |
| `logs/bootstrap-order.txt`, `logs/bootstrap.log` | the 119-module bootstrap, module by module, each with its start, end, seconds, exit status and peak memory (`MEM` lines: the children's maximum resident set from `getrusage`, since the host has no `/usr/bin/time`) |

`tools/runmem.py` is the memory wrapper behind the `MEM` lines (every probe's `.out` ends with one);
`tools/subst_hashes.py` resolved every hash in the drafts from `git rev-parse` and checked each
with `git cat-file -t`.
