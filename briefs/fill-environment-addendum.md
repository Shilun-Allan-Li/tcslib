# Fill-agent environment addendum (v2): resources, the dependency cache, and starting Lean

**Version 2 (2026-10-17).** Part 1, the resource and cache rules, is new and applies on **every**
host (the user's authorization of 2026-10-17). Part 2, the shim for an unreadable
`/proc/<pid>/exe`, is version 1's text, unchanged (authorized 2026-10-14). Everything else in your
brief stays binding.

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
   - the memory limit and use: the cgroup's `memory.max`, `memory.current` and `memory.events`
     (or `free -b` where there is no cgroup);
   - `df -B1` and the filesystem type (`df -T`) of the clone's directory and of every scratch
     directory you use.

   **Stop with escalation E-RES**, quoting the numbers, if the clone's filesystem has less than
   **12 GiB free**, or the memory headroom (limit minus current use) is below **4 GiB**. Do not
   try to make room by copying, moving or deduplicating dependency trees.
   - **Measured needs at this pin:** the Mathlib cache is about 5.2 GiB unpacked (all packages
     about 5.5 GiB), plus the archives while unpacking. The TCSlib bootstrap writes about
     0.2–0.3 GB of oleans. Lean's peak memory is about 2.4 GB (`Build/Catalog`, at `-j4`); most
     modules need under 1.6 GB.
2. **One checkout, one cache.** Do everything in a single clone.
   - Run `lake exe cache get` once, into that clone's own `.lake/packages`. Alternatively,
     symlink `.lake/packages` to a populated tree at exactly the same pins, recorded in
     `REPORT.md`.
   - Never copy, move, merge or deduplicate dependency trees between directories.
   - Never reuse another session's scratch tree, package builds, toolchain or object store, and
     never join `LEAN_PATH`s across trees.
   - Never put the clone, `.lake`, the cache, an olean tree (`TCSLIB_OLEANS`) or `TMPDIR` on a
     memory-backed filesystem (`/dev/shm`, any tmpfs).
   - The cache tool's own internal validation (`lake build --no-build proofwidgets:release`) is
     expected and allowed; it is not a `lake build` under your brief's ban.
   - **Packages match the manifest.** A fresh clone's first `lake exe cache get` fetches the
     packages that `lake-manifest.json` names. Afterwards, and before every later Lake command,
     check each one: `git -C .lake/packages/<name> remote get-url origin` and `rev-parse HEAD`
     must equal the manifest's URL and revision. If one differs, stop with E-RES. Never let Lake
     re-clone or update a package that is already present.
3. **Check the cache before the bootstrap.**
   - `lake exe cache get` exited 0.
   - `find .lake/packages -name '*.olean' -size 0` prints nothing.
   - A probe that imports Mathlib elaborates through `scripts/lean_check_tree.sh`, e.g. a file
     containing only `import Mathlib.Algebra.BigOperators.Group.Finset.Basic`. A probe that
     imports no Mathlib does not test the cache.
4. **One cleaned retry, then stop.** Clean and retry once on any of these:
   - ENOSPC (`No space left on device`, `os error 28`);
   - `leantar` exit 101;
   - Lean exit 135 (SIGBUS), 137 (killed) or 139 (SIGSEGV);
   - `compiled configuration is invalid`;
   - a failed check of item 3.

   To clean, delete the clone's `.lake/packages` and its compiled configurations
   (`.lake/lakefile.olean*`), re-run the preflight, and run `lake exe cache get` once more. If
   anything fails again, stop with E-RES and report. **Never** unpack or restore individual
   archives or oleans by hand (`leantar`, the cache tool's `lookup`, copies from elsewhere).
5. **Bootstrap order.** Your brief's order list is the bootstrap. You may build, first, only the
   modules of the list that your owned file imports (directly or not), in the list's order, and
   check your owned file against them. Build the list's remaining modules before the final
   sweep. Record which you did.
6. **No self-imposed timeouts.** Do not wrap module checks in short timeouts.
   - Log each module's start and end time, and its maximum memory (`/usr/bin/time -v` where
     available).
   - A module that stalls far beyond the measured figures is a resource symptom: re-read the
     memory counters. If the headroom is gone, stop with E-RES.
7. **Logs in place.** Write every log to its final path under `evidence/logs/` from the start
   (`2>&1 | tee …`). Never move a log that a running process is writing.
8. **No checks against missing prerequisites.** If the bootstrap stops, record its tail and skip
   the checks that need its products. Do not report their failures as findings.

E-RES is an environment report, not a failed fill. A continuation goes to a host that passes the
preflight.

## Part 2: starting Lean when `/proc/<pid>/exe` is unreadable (v1, unchanged)

**Authorized by the user (2026-10-14) for every fill brief of the chapters 3–4 campaign.** It
applies only under the condition below.

### The condition

Some fill hosts cannot resolve a process's own `/proc/<pid>/exe` link: `/proc/self/exe` may be
readable while `/proc/<pid>/exe` returns *Permission denied*. Lean 4.25.0 locates its own
installation through that link (`IO.appDir`, used by `Lean.getBuildDir`), so `lean --version`,
`lake exe cache get` and `scripts/lean_check_tree.sh` fail with

```text
error: failed to locate application
```

or Lake reports `could not detect the configuration of the Lake installation`.

### The authorized fallback

**Use this only if, and after,** the pinned, unmodified Lean fails with that error in your
environment. Then you may preload the following `readlink` fallback into the Lean and Lake
processes only.

- **What it does:** it answers the single failed self-path lookup with the executable's own path,
  taken from the ELF startup metadata (`AT_EXECFN`). Every other call is passed through
  unchanged.
- **What it does not do:** it changes no filesystem permission, does not bypass the sandbox, and
  changes neither Lean, the kernel, the sources nor any proof check.
- **Precedent:** earlier campaign deliveries used exactly this source, for example the
  record-table continuation 5 (`audits/wave1-fill-agent-reports/recordtable-6-REPORT.md`).

`executable-path.c` (SHA-256 `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`):

```c
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>
/* Supply the executable's actual path from ELF startup metadata when procfs
   cannot resolve it. No filesystem, network, or proof-checking rules change. */
ssize_t readlink(const char *path, char *buf, size_t cap) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  ssize_t n = real_readlink(path, buf, cap);
  char own[64];
  snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
  if (n >= 0 || (strcmp(path, "/proc/self/exe") && strcmp(path, own))) return n;
  const char *exe = (const char *)getauxval(AT_EXECFN);
  char absolute[PATH_MAX];
  if (!exe || !realpath(exe, absolute)) return n;
  size_t len = strlen(absolute);
  if (len > cap) len = cap;
  memcpy(buf, absolute, len);
  return (ssize_t)len;
}
```

Compile and use it in your scratch directory:

```bash
cc -shared -fPIC -O2 executable-path.c -ldl -o executable-path.so
export LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0"   # your pinned toolchain
export LAKE_HOME="$LEAN_SYSROOT"
export LD_PRELOAD="$PWD/executable-path.so"
lean --version   # must now print the pinned version
```

### Rules

1. **Use exactly this source.** Do not write a different shim, patch the toolchain, change
   permissions or request sandbox escalation.
2. **Scope:** preload it only into the processes that run Lean or Lake (`lake exe cache get`,
   `scripts/lean_check_tree.sh`, your probes). Nothing else.
3. **Record it in `REPORT.md`:**
   - that the condition occurred;
   - the shim's SHA-256, which must match the one above;
   - the exact environment variables you set.

   Include the source under `evidence/runtime/`. **Do not ship the compiled `.so`** or any
   build products.
4. **If Lean still cannot start** with the shim, stop and report. Do not try anything further.
5. A standard host, where Lean starts normally, needs none of this. Do not preload the shim
   there.
