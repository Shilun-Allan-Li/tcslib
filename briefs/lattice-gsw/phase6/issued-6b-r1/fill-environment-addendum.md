# Fill-agent environment addendum (Pass–shelat ch. 5–8 campaign, v1): resources, the dependency cache, starting Lean

**Version 1 (2026-11-06).** Attached to every fill brief of this campaign (branch
`cryptography/pass-shelat-ch2-4` and its descendants). Part 1 is the Arora–Barak campaign's
addendum v2.6, Part 1, unchanged: it is generic to TCSlib at this Lean pin (4.25.0). That
addendum's Part 2 (a `readlink` shim) and Part 3 (megafills) are **not** authorized here:
- if Lean fails to start with `error: failed to locate application`, stop with escalation E-RES
  and report the error; do not work around it;
- one session works on one brief.

Fills of this campaign may run in parallel on separate hosts (user, 2026-11-06). On one host,
**one Lean process at a time** (a module check, a probe, a bootstrap or sweep step, each through
`scripts/lean_check_tree.sh`, or one `lake exe cache get`); the cache tool's own internal jobs are
not counted. Everything in your brief stays binding.

## Adaptation for the GSW 6b statement job (`gsw-6b-statements`, issued-6b-r1)

This job writes the statement phase of 6b (and the proved owner PR O2), not proofs; Part 1 applies to it, read as
follows. Where this section and Part 1 differ, this section wins.
- **"Fill" means this job**, and "your owned files" are the files the brief's *Scope* lets you create or change.
- **One base, one Lean tree.** Every build and check runs at the **base** `3e51b5f28900db6190f1eb2e6d207d27ee15d541`
  (tree `b69a66a385ca3439d56af1d6b9791b5847984fde`), a deterministic unsigned two-step local merge: #360's head
  `cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25` into #359's head `d154c8830fc8ffc52671b41992e7dbef61e30959`, then that
  into the records tip `036d823933c8248bd8894c7963e15dd0f1837075` (Lean = snapshot #6). `tools/mkbase.sh` creates it.
  `lean-toolchain` (`v4.25.0`), `lake-manifest.json` (Mathlib `029db123ddaa`) and the lakefile are identical at the
  base, the three heads and the records tip, so one `.lake/packages` serves the job. Never build oleans from #359,
  #360 or the records tip alone.
- **The order lists.** `order.txt` has the **1,443** modules reachable from `TCSlib.lean` at the base, in import
  order (a depth-first post-order, imports in file order), with the root `TCSlib` last; it is the root build.
  `prefix.txt` (**288**) is its subsequence that the job needs first: the upstream closure of the 18 `DOWN` modules of
  `closures.txt` and of the 22 `IMPORTS` modules (the existing modules the r3 sketches cite). Item 5's "build first
  only what your owned files import" means `prefix.txt`.
- **Roots.** `prefix-roots.txt` lists the **105** Mathlib modules that `prefix.txt` imports directly, and `roots.txt`
  the **385** that `order.txt` imports. Fetch `prefix-roots.txt` first (item 2's command with that list) and the rest
  of `roots.txt` before the root build; record both fetches. A new `import Mathlib…` line in a new or owned file adds
  roots: fetch for them the same way, record them, and disclose the import.
- **New modules** (the 9 files of the brief's *Scope*) are inserted into your working copy of the order right after
  the last module they import, facades after their children, and recorded in `evidence/build/order-final.txt`.
- **The root build** (the brief's check 2) is long (1,443 modules plus the 9 new ones). Run it last, from the
  committed final head. If it cannot finish on this host, deliver the final with the root step marked incomplete,
  its log tail and the last module checked (item 8: no checks against missing prerequisites); this is not a failed
  job.
- **Lean parallelism: a memory-sized pool, not one process.** This replaces the "one Lean process at a time" sentence
  above, under the user's ruling of 2026-11-17 (`workflow.md` §4.1, *Lean parallelism*), which lets **cloud workers**
  run several Lean processes:
  - size the pool from the machine: at most `nproc` processes, and few enough that at least about 2 GB (or 15%) of
    memory stays available; start from `min(nproc, MemAvailable / 4 GB)`, back off under memory pressure, and give a
    heavy module (for example `Complexity/ClassP/BinaryArith/DetMod` in the root build) room of its own; record
    `nproc`, the memory figures, the pool size and every change to it in `evidence/logs/pool.log`;
  - build in dependency order: start a module only when every module it imports has its olean, and never let two
    processes compile the same module or write the same file (one olean tree per agent makes the second automatic);
  - seals, controls, axiom probes and statement probes may run in parallel across owners, each in its own probe
    file and output directory;
  - all agents share **one pool** (a counting semaphore, for example a directory of `flock` slot files), not a single
    host lock; each agent records the pool size and its peak memory in its evidence;
  - a "shortage" is still as item 1 defines it, and the headroom is computed as item 1 says; under a shortage shrink
    the pool before anything else.

  Everything else is unchanged: never `lake build` the library, never run an unfiltered `lake exe cache get`, only
  the lead fetches the cache, and each module is still compiled through `scripts/lean_check_tree.sh` (one call per
  module, with `TCSLIB_OLEANS` set to the agent's own tree).
- **The cache tool runs alone.** While `lake exe cache get` runs, no Lean process of the pool runs (item 2).
- **One TCSlib olean tree per agent.** A sub-agent's tree may be seeded by copying the lead's **TCSlib** oleans only
  for modules whose source and every upstream source are byte-identical between the two trees (record the list and
  the check); never copy package trees.
- **Before each sweep and the root build,** rebuild every module whose source differs from the source its olean was
  built from, then everything downstream of it, and bind every checked source to `git show HEAD`.
- **Sub-agents** (up to 3): only the lead runs `lake` or fetches the cache; each sub-agent has its own worktree and its
  own TCSlib olean tree, with `.lake/packages` linked to the lead's.

## Part 1: resources and the dependency cache

**Why.** Four fill workers of 2026-10-17 stopped before any proof check, all for host reasons. The
dependency cache filled the disk (`No space left on device`, `leantar` exit 101). One worker staged
files on `/dev/shm`, which counts against the memory limit, and others copied dependency trees
between directories. Empty or truncated oleans, a stale compiled Lake configuration and a Lake
re-clone of Mathlib (package URLs differing from the manifest) followed. Lean then crashed
(SIGBUS 135, SIGSEGV 139) or stalled at a full memory limit. The rules below stop that early and
cleanly.

1. **Preflight, before any cache or Lean work.** Record in `evidence/logs/preflight.log`, and quote
   in `REPORT.md`:
   - `nproc`;
   - the memory limit and use: the cgroup's `memory.max`, `memory.current`, `memory.events` and
     `memory.stat` (cgroup v1: `memory.limit_in_bytes`, `memory.usage_in_bytes`, `memory.stat`),
     or `/proc/meminfo` where there is no cgroup limit;
   - `df -B1` and the filesystem type (`df -T`) of the clone's directory and of every scratch
     directory you use.

   **Stop with escalation E-RES**, quoting the numbers, if the clone's filesystem has less than
   **12 GiB free**, or the memory headroom is below **4 GiB**. Do not try to make room by copying,
   moving or deduplicating dependency trees.
   - **When the disk floor applies.** The 12 GiB floor applies at this initial preflight, which
     covers everything after it, the toolchain included. If you install the toolchain after it,
     you may re-check before `lake exe cache get`; that re-check's floor is **8 GiB** (the
     packages about 6 GiB, the cache archives about 1 GiB, the bootstrap's oleans and the clone).
     After the cache step, disk is not re-checked: an ENOSPC is handled by item 4.
   - **The memory headroom is the limit minus the memory in use**, where the memory in use is
     `anon + kernel + shmem` from `memory.stat` (cgroup v1: `memory.usage_in_bytes − total_cache +
     total_shmem`). Where `memory.max` is `max` (no cgroup limit), the headroom is `MemAvailable`
     from `/proc/meminfo`. Log the fields and the computation.
   - **Not shortages:** page cache (`file`, `active_file`, `inactive_file`, `file_mapped` in
     `memory.stat`; `memory.current` includes it), and `memory.events`' `max` and `high` counters,
     which count reclaim at the limit. The kernel reclaims the cache as Lean needs memory.
   - **A shortage** is an `oom` or `oom_kill` event, a Lean exit 137, or a headroom below 4 GiB
     as computed here.
   - **Measured needs at this pin:** the Mathlib cache is about 5.2 GiB unpacked (all packages, with
     their git checkouts, about 6 GiB), plus about 1 GiB of archives kept by the cache tool; the
     toolchain about 4.2 GiB with its archive. The TCSlib bootstrap writes about 0.2–0.3 GB of
     oleans. Lean's peak memory is about 2.8 GiB (`Build/Catalog`, at `-j4`; 2,796 MiB measured on a
     fill host); most modules need under 1.6 GB.
2. **One checkout, one cache.** Do everything in a single clone.
   - **Fetch the cache for your brief's Mathlib roots only**, into that clone's own
     `.lake/packages`, with `TAR_OPTIONS=--no-same-owner` in its environment (extract the
     toolchain archive the same way if it fails on ownership). The roots are the Mathlib modules
     that the modules of your brief's order list import directly; from the clone's root, after
     your brief's first edit (its imports or overlay, if any):

     ```sh
     ORDER=<your brief's order list>
     sed 's|$|.lean|' "$ORDER" | xargs grep -h '^import Mathlib' | awk '{print $2}' | sort -u \
       > evidence/logs/mathlib-roots.txt
     TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt) \
       2>&1 | tee evidence/logs/cache-get.log
     ```

     The tool fetches those modules and everything they import. **Never run the unfiltered
     `lake exe cache get`.** Record the roots' count and the number of files fetched. If you add
     an import later (only where your brief authorizes one), fetch for the new roots the same way.
     Alternatively, symlink `.lake/packages` to a populated tree at exactly the same pins,
     recorded in `REPORT.md`.
   - **Log the cache tool's archive store first** (v2.5). Before the first `lake exe cache get`,
     record in `evidence/logs/cache-store.log` whether the store exists
     (`${XDG_CACHE_HOME:-$HOME/.cache}/mathlib` by default), how many files it holds and their
     total size (`find … -type f | wc -l`, `du -sb …`). The fetch log's "Attempting to download N"
     and "Decompressing M" then show that `M − N` archives were already in the store. Archives
     already there are the cache tool's own, named by hash and checked by it: using them is
     allowed, and the store is not "another session's object store" (below). In `REPORT.md`, give
     their number and, if you know it, their origin (an earlier session on this host, the host
     image); do not describe them as downloaded by this session.
   - Never copy, move, merge or deduplicate dependency trees between directories.
   - Never reuse another session's scratch tree, package builds, toolchain or object store, and
     never join `LEAN_PATH`s across trees.
   - Never put the clone, `.lake`, the cache, an olean tree (`TCSLIB_OLEANS`) or `TMPDIR` on a
     memory-backed filesystem (`/dev/shm`, any tmpfs).
   - **The cache tool's own work is outside the one-Lean rule.** `lake exe cache get` may first
     compile the cache executable (on a fresh clone, about 20 Lake jobs, among them a few
     Batteries modules) and runs `lake build --no-build proofwidgets:release`. Lake schedules
     these jobs itself, and at this pin it has no option to serialize them. They are expected and
     allowed. They are not a `lake build` of the project, and they are not "a Lean process" in the
     sense of Part 3, item 5. Run the command alone: start no check of your own until it has
     exited. Do not reconstruct, measure or certify Lake's internal scheduling, and do not report
     it as a deviation.
   - **Packages match the manifest** (v2.5: the packages present). A fresh clone's first
     `lake exe cache get …` fetches the packages that `lake-manifest.json` names, except those the
     narrowed fetch does not need. Afterwards, and before every later Lake command, check each
     package **present in** `.lake/packages`: `git -C .lake/packages/<name> remote get-url origin`
     and `rev-parse HEAD` must equal the manifest's URL and revision. If one differs, stop with
     E-RES. List the manifest's packages that were not cloned as **ABSENT**, not as a mismatch (at
     this pin `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`, the documentation
     toolchain). The check passes when every present package matches and no module of your order
     list imports an absent package; quote its last line in `REPORT.md`. Never let Lake re-clone
     or update a package that is already present.
3. **Check the cache before the bootstrap.**
   - The narrowed `lake exe cache get` exited 0, with no failed download.
   - `find .lake/packages -name '*.olean' -size 0` prints nothing.
   - A probe that imports one of your roots elaborates through `scripts/lean_check_tree.sh`, e.g.
     a file containing only the first line of `mathlib-roots.txt` as an `import`. A probe that
     imports no Mathlib does not test the cache, and a module outside your roots' closure is not
     in your cache.
   - **Failed downloads** (a network error such as a proxy `403`, or `N download(s) failed`):
     re-run the same narrowed command up to twice; it fetches only what is missing. If files
     still fail, that is a failed check of this item (item 4).
4. **One cleaned retry, then stop.** Clean and retry once on any of these:
   - ENOSPC (`No space left on device`, `os error 28`);
   - `leantar` exit 101;
   - Lean exit 135 (SIGBUS), 137 (killed) or 139 (SIGSEGV);
   - `compiled configuration is invalid`;
   - a failed check of item 3.

   To clean, delete the clone's `.lake/packages` and its compiled configurations
   (`.lake/lakefile.olean*`), re-run the preflight (a re-check: item 1's floor before the cache),
   and run the narrowed `lake exe cache get` once more. If anything fails again, stop with E-RES
   and report, naming the files that failed to download and the roots you fetched. **Never**
   unpack or restore individual archives or oleans by hand (`leantar`, the cache tool's `lookup`,
   copies from elsewhere).
5. **Bootstrap order.** Your brief's order list is the bootstrap. You may build, first, only the
   modules of the list that your owned file imports (directly or not), in the list's order, and
   check your owned file against them. Build the list's remaining modules before the final
   sweep. Record which you did.
6. **No self-imposed timeouts.** Do not wrap module checks in short timeouts.
   - Log each module's start and end time, and its maximum memory (`/usr/bin/time -v` where
     available).
   - A module that stalls far beyond the measured figures is a resource symptom: re-read the
     memory counters, and compute the headroom as in item 1 (the memory in use, not
     `memory.current`). Stop with E-RES only on a shortage as item 1 defines it.
7. **Logs in place.** Write every log to its final path under `evidence/logs/` from the start
   (`2>&1 | tee …`). Never move a log that a running process is writing.
8. **No checks against missing prerequisites.** If the bootstrap stops, record its tail and skip
   the checks that need its products. Do not report their failures as findings.

E-RES is an environment report, not a failed fill. A continuation goes to a host that passes the
preflight.
