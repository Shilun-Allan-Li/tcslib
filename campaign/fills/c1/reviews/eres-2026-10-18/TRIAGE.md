# E-RES triage — C1-R cont1 and C1-WC cont1 (2026-10-18)

Two fills dispatched on 2026-10-18 under addendum v2 stopped with E-RES: R cont1
(`fill-c1-core-cont1.zip`, SHA-256 `27ce25af…`; report `../../reports/core-2-REPORT.md`) and WC cont1
(`fill-c1-window-cont1.zip`, `e5e18dd0…`; report `../../reports/window-2-REPORT.md`). Neither has a
proof contribution; neither lands. Key logs are copied under `core-2/` and `window-2/`.

**Verdict: both stops are false alarms of the headroom measurement.** The thresholds (12 GiB free
disk, 4 GiB memory headroom) are not the cause.

| | R cont1 | WC cont1 |
|---|---|---|
| Host | 9 CPUs, cgroup v2, `memory.max` 8 GiB, overlay disk 33.8 GB | the same |
| Initial preflight | 29.2 GiB free; headroom 7.23 GiB: **PASS** | 29.1 GiB free; headroom 7.09 GiB: **PASS** |
| What happened next | the cache's own `leantar` archive failed to install: `tar: leantar: Cannot change ownership to uid 1001, gid 1001: Invalid argument`; the cleaned retry's preflight then ran | the worker re-read the counters while Lake was cloning the packages, and interrupted the cache (exit 130) |
| Disk at the stop | 20.9 GiB free | 20.9 GiB free |
| `memory.current` at the stop | 7,150,563,328 | 8,493,359,104 |
| v2 headroom (`limit − current`) | 1.34 GiB → E-RES | 0.09 GiB → E-RES |
| `memory.stat` (R: just after the stop) | `anon` 84 MB, `kernel` 366 MB, `file` 6.69 GB (`inactive_file` 3.33 GB) | `anon` 199 MB, `kernel` 421 MB, `file` 7.87 GB (`inactive_file` 5.13 GB) |
| `memory.events` | `max` 31,090, `oom` 0, `oom_kill` 0 | `max` 16,852, `oom` 0, `oom_kill` 0 |
| v2.1 headroom (`limit − (anon + kernel + shmem)`) | 7.58 GiB: pass | 7.42 GiB: pass |

**Cause.** `memory.current` includes the kernel's page cache. Downloading and unpacking the
dependency cache (about 5.5 GiB) and cloning the packages fill an 8 GiB cgroup's cache to its
limit; the kernel reclaims it on demand (`memory.events`' `max` counter counts that reclaim). No
OOM event occurred on either host. A working-set measure (`memory.current − inactive_file`) is
not robust either: R's would give 4.45 GiB, since recently read files count as `active_file`,
and Lean's mapped oleans grow that during a bootstrap.

**A second, independent defect (R):** the pinned cache tool extracts its `leantar` helper with
plain `tar -xf`, which fails where `chown` is forbidden. Earlier workers set
`TAR_OPTIONS=--no-same-owner` themselves; v2 did not say so.

**Ruling (user, 2026-10-18): addendum v2.1** (`campaign/standards/fill-environment-addendum.md`,
SHA-256 `2563c8d2…`): the same thresholds; the headroom is the limit minus `anon + kernel +
shmem` (cgroup v1: `usage − total_cache + total_shmem`; `MemAvailable` without a cgroup limit);
page cache and the `max`/`high` counters are not shortages; a shortage is an OOM event, a Lean
exit 137, or headroom below 4 GiB so computed; the cache runs with `TAR_OPTIONS=--no-same-owner`.
v2 is kept as `exchange/archive/fills/fill-environment-addendum-v2.md`.

**Re-dispatch:** both briefs unchanged (ancestor `96d60278`; R `5fefa735…`, WC `980f5b5d…`), with
v2.1 attached. For comparison, E cont1's host of the same day (cgroup v1, 14.3 GB limit, 27.6 GB
free) passed v2 and completed its fill.

## Later the same day: G4 cont2 and MIG-12 cont1 (under v2.1)

Both stopped with E-RES on **disk**, at a 12 GiB re-check made after the initial preflight
(reports `campaign/fills/s13d/reports/g4-cont2-eres-REPORT.md`,
`campaign/fills/mig12/reports/cont1-eres-REPORT.md`; logs under `g4-cont2/` and `mig12-cont1/`).
v2.1's memory rule worked on both: headroom 6.4 GiB, with `memory.current` at the limit.

| UTC | Fill | Overlay `/` (33,770,192,896 bytes) used |
|---|---|---|
| 15:36:22 | G4 initial preflight (15.44 GiB free: pass) | 15,452,688,384 |
| 15:36:46 | MIG-12 initial preflight (15.42 GiB free: pass) | 15,477,137,408 |
| 15:40:18 | G4 re-check after the toolchain (11.21 GiB free: E-RES) | 19,997,040,640 |
| 15:41:09 | MIG-12 re-check during the toolchain download (10.48 GiB: E-RES) | 20,780,457,984 |

**The two fills shared one disk**, one timeline on the same overlay, and the 15.45 GB in use when
they started is consistent with R cont1 and WC cont1, re-dispatched on the same host shortly
before. A fill needs about 11 GiB from scratch (the toolchain 4.2 GiB with its archive, the
packages about 6 GiB, the cache archives about 1 GiB, the oleans and the clone), so this host
holds about two fills at once. On the stop itself, a 12 GiB re-check after the toolchain
double-counts the toolchain: a lone fill at 11.2 GiB would have finished.

**Rulings (user, 2026-10-18):** addendum **v2.2** (SHA-256 `45405074…`): the 12 GiB floor at the
initial preflight; a re-check before the cache, once the toolchain is installed, needs 8 GiB;
after the cache step only ENOSPC (item 4). And **at most two fills at once**: G4 cont2 and MIG-12
cont1 re-dispatch, with their briefs unchanged, when R cont1 or WC cont1 delivers.
