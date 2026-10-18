# C1-E continuation 1 — environment report

**Disposition: E-RES. Environment-blocked before repository setup (phase 0).**
The target was not proved and no source was edited. The mandatory preflight stop
prevents this delivery from containing a source change, patch series or git bundle.
This is an environment report, not a failed fill or a verified source partial.

## Resource preflight

Measured at **2026-10-17 22:18:02 UTC**. The log was written directly to
`evidence/logs/preflight.log` from the start.

| Measurement | Observed | Required |
|---|---:|---:|
| `nproc` | 9 | Not specified |
| Clone-parent filesystem free bytes | 822,689,792 (about 0.77 GiB) | 12,884,901,888 (12 GiB) |
| Cgroup `memory.max` | 8,589,934,592 (8 GiB) | Headroom test below |
| Cgroup `memory.current`, first read | 8,589,729,792 | — |
| Cgroup `memory.current`, decision read | 8,589,844,480 | — |
| Headroom at decision | 90,112 bytes (88 KiB) | 4,294,967,296 (4 GiB) |

Headroom was calculated as `8,589,934,592 - 8,589,844,480 = 90,112` bytes.
Both stop conditions were met. The two memory reads are separate samples; neither
is a peak-memory measurement for this task.

The prospective clone parent and all report/helper/output paths are under
`/workspace/scratch/61fb2f885d99`, on `overlay`. `/tmp` was also measured and is
on the same `overlay`; no task artifact was staged there. No memory-backed
filesystem was used. The clone directory was never created.

Raw preflight output:

```text
2026-10-17T22:18:02+00:00
9
0::/
/sys/fs/cgroup/memory.max
8589934592
/sys/fs/cgroup/memory.current
8589729792
/sys/fs/cgroup/memory.events
low 0
high 0
max 140852972
oom 1
oom_kill 1
oom_group_kill 0
Filesystem       1B-blocks        Used Available Use% Mounted on
overlay        33770192896 31212740608 822689792  98% /
overlay        33770192896 31212740608 822689792  98% /
Filesystem     Type    1K-blocks     Used Available Use% Mounted on
overlay        overlay  32978704 30481192    803408  98% /
overlay        overlay  32978704 30481192    803408  98% /
disk_free_bytes=822689792; minimum=12884901888
memory_limit_bytes=8589934592; memory_current_bytes=8589844480; memory_headroom_bytes=90112; minimum=4294967296
E-RES
```

The cgroup event counters were already present at preflight. They are not evidence
that a process from this task was killed.

## Attachment integrity

After the resource stop, the attachments were hashed and the brief was read only
to prepare this report. Both hashes match the user's expected values:

| Attachment | Verified SHA-256 |
|---|---|
| `c1-fill-exhaustive-cont1.md` | `a00bdc6f9458c7ff69362475cc45b7250f0173d0a6ce7d3851bf3183ae847b6f` |
| `fill-environment-addendum(20261017-221742).md` | `2a80b0ef8da202cc5faf4c1513b2f34ed7437c5aef2cb3ed815355934b54ad2b` |

## Repository and environment status

- Intended repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required campaign branch: `complexity/arora-barak-ch3-4`.
- Required inputs/base commit: `9e77d2b26a62c3ee0c418a1e0a031c867c0ac80a`.
  This is the brief's prescribed base, not a verified checkout HEAD.
- Clone, repository-brief comparison, ancestor check and creation of
  `fill/c1-exhaustive-cont1`: **SKIPPED — E-RES**.
- No repository edit was made, including the three authorized imports.
- No rebase, merge, cherry-pick, push or PR was performed.
- No Lean or Lake process was started. No `lake build` was run.
- No cache download, package inspection, Mathlib probe or bootstrap was attempted.
- No dependency tree was copied, moved, deduplicated, reused or deleted.
- The cleaned-retry rule was not triggered: no cache or Lean failure occurred.
  The initial preflight instead requires an immediate stop.
- Addendum Part 2 was not triggered. No shim was created or preloaded; no
  `LEAN_SYSROOT`, `LAKE_HOME`, `LD_PRELOAD`, `LEAN_PATH`, `TCSLIB_OLEANS` or
  `TMPDIR` override was set by this task.

## Open work and proof sketch

Phase reached: **preflight only; phases 1–4 not started**.

Open declaration: `Turing.FinNDTM.exists_exhaustiveDecider` in
`TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean`, as identified by the brief.
No other declaration was opened or modified.

**Proof sketch** (the brief's prescribed route; not implemented or verified):
construct the private bounded-window clearing row, then compose the existing
replay machine, silent embedding and step clock. Restore the clock counter,
rewind the choice head, test and clear the captured output, and restore each work
tape between replays. Enumerate all choice words at each depth using the existing
counter infrastructure and phase host. Deepen until the first all-halting depth,
prove that acceptance there agrees with acceptance at the hypothesized bound,
and sum the replay costs to obtain the stated exponential ledger.

No constant `C`, ledger proof, leaf construction, private lemma or appendix was
added. The proposed window-clearing row remains future work, not a completed
promotion candidate. No external declarations were cited in new Lean code.

**Target axiom walk: NOT RUN.** The brief describes the target as sorried and its
consumer `Turing.ndAcceptsWithin_decider_of_universal` as proved modulo that
target. No `#print axioms` result was obtained for either, and no assertion of
kernel verification or absence of `sorryAx` is made.

## Verification and delivery accounting

All dependent checks were skipped, as required by addendum Part 1, item 8.
The files below record skipped operations; they are explicitly not fabricated
Lean output or screen output:

- `evidence/logs/bootstrap.log`: zero modules attempted.
- `evidence/logs/final-sweep.log`: sweep and import probe not run.
- `evidence/logs/axioms.log`: target and consumer prints not run.
- `evidence/logs/screen-before.txt`: v3 screen not run.
- `evidence/logs/screen-after.txt`: v3 screen not run.

Both screen status texts are: `SKIPPED — E-RES. Repository not cloned; no screen
command executed. No screen measurements are available.`

**new copies: none** — no source edits exist. This is not a screen pass.
No new in-file or cross-file pairs were introduced by this task.
Lint, diff grep, declaration counts and final source line count were not measured.
The brief's base line count of 110 is unverified on this host. There is no final
Lean sweep tail; the status log records that the sweep was not started.
The base sorry list was not read, so no sorry-set comparison is claimed.

The ZIP contains this report, the raw preflight log, the five skipped-operation
records above and `SHA256SUMS`. Each payload file other than `SHA256SUMS` is
covered by that manifest. Source, `git format-patch` series and git bundle are
absent because the mandatory stop occurred before a clone, base verification or
edit. No placeholder source, patch or invalid bundle is supplied.

## REPORT.md checklist

Checked entries mean the reporting requirement was addressed, not that a skipped
verification passed.

- [x] Target/phase and prescribed base reported; ancestor check explicitly skipped.
- [x] Preflight numbers, filesystem types and raw log reported.
- [x] First-edit status reported: no source edit; imports not added due E-RES.
- [x] New declarations: none. Window clear and appendix: not started.
- [x] Constant `C` and ledger: not constructed; open route described above.
- [x] Promotion candidates: none completed. Escalation: E-RES.
- [x] Rule 10: no code citations; probe skipped. Rule 11: no diff; grep skipped.
- [x] Duplication: both screen status records supplied; new copies: none, no screen pass.
- [x] File-size/declaration counts, sweep, axioms and lint: explicitly not measured/run.

## Escalation

**E-RES:** free disk was 822,689,792 bytes, below 12,884,901,888; memory
headroom was 90,112 bytes, below 4,294,967,296. Continue on a host that passes
both resource thresholds, starting with the mandatory preflight and then the
original pinned-base procedure. No ground rule was relaxed.
