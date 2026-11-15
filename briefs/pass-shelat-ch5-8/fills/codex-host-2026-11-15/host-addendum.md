# Host addendum: Codex workers on Seyoon's Mac (2026-11-15)

This addendum applies to the fills `sc-garble`, `derand` (issued-r2) and `seq-zk`. Seyoon is running them on
**Codex**, on his Mac, from his local checkout of the exchange branch. Each brief still names "Claude" as the
worker, but for these three runs the worker is Codex (Seyoon, 2026-11-15). The brief, its fill-environment
addendum and any ruling in the package stay binding. This addendum overrides them only where it says so.

## 1. Host-wide Lean cap: at most 3 Lean processes at once
This replaces the fill-environment addendum's "one Lean process at a time on one host".
- The cap is shared by every job on the Mac: these three fills and Seyoon's other jobs.
- **Run every Lean-running command through `lean-slot.sh`**, which is next to this file. Copy it once to a
  stable place outside the exchange checkout, for example `~/bin/lean-slot.sh`, and run `chmod +x` on it.
  - Each `scripts/lean_check_tree.sh` call:
    `lean-slot.sh bash scripts/lean_check_tree.sh <Module/Path>`
  - Each probe or other direct `lean` run, the same way.
  - Each `lake exe cache get …`, with **three** slots, because its Lake jobs can start several Lean processes:
    `lean-slot.sh -k 3 env TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt)`
- All jobs use the default slot directory `~/.lean-slots`. Do not set `LEAN_SLOT_DIR` or `LEAN_SLOTS`. Set
  `LEAN_SLOT_TAG` to your unit name (`sc-garble`, `derand`, `seq-zk`; for a sub-agent, `seq-zk-a` and so on).
- Never start `lean` or `lake` outside the wrapper, and never in the background outside it. Do not kill another
  job's processes. Do not edit or remove another job's slot directories; the wrapper reaps dead ones itself.
- A sweep is a loop of single-slot calls, one module per call. Do not hold a slot across modules.
- Waiting for a slot is normal. Log it, but it is not a stall and not an E-RES.
- **Evidence.** Copy the lines of `~/.lean-slots/slots.log` that carry your tag into `evidence/logs/slots.log`,
  and quote the cap in `REPORT.md`.

## 2. Preflight on macOS
This replaces the cgroup and `/proc` steps of Part 1, item 1. Record the output in `evidence/logs/preflight.log`:
- `sysctl -n hw.ncpu hw.memsize`
- `vm_stat`
- `memory_pressure -Q`, where it exists
- `df -k` and `mount` for the clone's filesystem and every scratch directory

**Memory headroom** = (free + inactive + speculative + purgeable pages) × the page size from `vm_stat`'s first
line. Log the computation. The floor stays at **4 GiB**.
- If you are below it while other jobs run, wait and re-measure up to 3 times, 10 minutes apart.
- After that, stop with E-RES.
- A shortage is a Lean exit 137 or 139, a jetsam kill, or a headroom under 4 GiB.

The disk floor stays at **12 GiB free** for your own clone. All three fills together need about 40 GiB.

**Time and memory.** Where the addendum says `/usr/bin/time -v`, use `/usr/bin/time -l`; it reports "maximum
resident set size" in bytes. For hashes, use `shasum -a 256` (it reads and writes the same format as
`sha256sum`).

## 3. Checkouts
- **The Lean work goes in its own git worktree**, never in Seyoon's exchange checkout:
  `git -C <exchange checkout> fetch origin <branch>`, then
  `git -C <exchange checkout> worktree add ../tcslib-<unit> <issue base>`. Then make the brief's local branch there.
  Worktrees share the repository's object store, and that is allowed.
- Each job has **its own `.lake/packages`** and its own narrowed cache fetch, as the addendum says.
- The toolchain under `~/.elan` and the cache tool's archive store under `~/.cache/mathlib` are the host's, and
  may be shared. Log them as the addendum says.
- Put no checkout, `.lake`, olean tree or `TMPDIR` on a RAM disk.

## 4. seq-zk: up to 3 sub-agents
- **The lead owns the job.** It owns the brief, the branch `fill/seq-zk`, the delivery and `REPORT.md`.
  Sub-agents return their work to the lead, and only the lead commits on `fill/seq-zk` and pushes.
- **Each sub-agent has its own worktree and its own olean tree.**
  - The worktree is a git worktree of the lead's clone, on a sub-branch from the lead's current commit.
  - The olean tree is set with `TCSLIB_OLEANS`. Never let two Lean processes write one olean tree.
  - A sub-agent's `.lake/packages` is a symlink to the lead's: read-only Mathlib, the same pins. Only the lead
    runs `lake`.
  - The lead may seed a sub-agent's olean tree by copying its own **bootstrapped TCSlib olean tree** (`cp -cR`,
    an APFS clone). Copying Mathlib or other package trees stays forbidden.
- **Sub-agents count against the host cap**, through the same wrapper and the same slots. There is no
  per-job allocation, so three sub-agents may wait for one another and for other jobs.
- **Ownership.** Split by helper module, so that no two sub-agents edit the same file. The owned file
  `SequentialZK.lean` is edited only by the lead.
- **The record.** `REPORT.md` records who proved what, and the final sweep and every check are run by the lead
  on the merged branch. The evidence-completeness rule covers sub-agent logs too: put them under
  `evidence/subagents/<name>/`.

## 5. Delivery from the local exchange checkout
- **Use your own delivery worktree** of the exchange branch, so that the three jobs never share an index:
  `git -C <exchange checkout> worktree add ../exchange-<unit> origin/exchange/pass-shelat-ch5-8`.
- **Commit only under `inbox/fills/<unit>/`.** Before each push, run
  `git pull --rebase origin exchange/pass-shelat-ch5-8`. Then push to `exchange/pass-shelat-ch5-8`. Never
  force-push.
- **Identity.** Commit with the checkout's configured identity, with `commit.gpgsign=false`. Record the author
  and committer, and the signing, in `patches/COMMITS.tsv` as the brief requires.
- **If a push is refused,** keep the commit and say so in the chat. Seyoon pushes it.
- **Fallback.** At the end, also return the final payload in the chat as a ZIP, with `<unit>/` at its root.
- Do not touch Seyoon's own exchange checkout's working tree or branch.
