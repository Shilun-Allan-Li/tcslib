# Internal fill worker: environment (replaces the environment addendum's Part 1)

You are a fill worker running on the maintainer's machine, not on a fresh host. The brief is
binding; this note replaces only the addendum's host set-up (Part 1: preflight floors, cache
fetch, bootstrap), because the environment is already built for you:
- **Your clone:** worktree `$WT` (given in your prompt) on local branch `fill/<unit>`, at the issue
  commit `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1`, with `.lake/packages` linked to a populated
  Mathlib tree at the pinned revisions. Do not fetch the cache, do not touch `.lake/packages`.
- **Your olean tree:** `$OL` (given in your prompt): a full, current build of the issue commit. Check
  modules with `cd $WT && PATH="$HOME/.elan/bin:$PATH" TCSLIB_OLEANS=$OL bash scripts/lean_check_tree.sh <module path without .lean>`.
  After editing your owned file, re-check it, and before delivery re-check everything downstream of
  it in the order list's order (your brief's `inputs/<unit>/order.txt`).
- **Never `lake build`; never `lake exe cache get`.** One Lean process of yours at a time. Other
  workers run on the same machine with their own trees: never touch anything outside `$WT`, `$OL`,
  `$EX` and your own scratch directory `$SP/fillwork-<unit>/`.
- Python as `python3 -I`. Commit hashes from `git rev-parse`.
- **Delivery** (the brief's exchange protocol): `$EX` is a detached checkout of
  `exchange/pass-shelat-ch5-8`. For each checkpoint and the final delivery: `cd $EX && git fetch -q
  origin exchange/pass-shelat-ch5-8 && git checkout -q --detach origin/exchange/pass-shelat-ch5-8`,
  write `inbox/fills/<unit>/` (REPORT.md, `patches/` from `git -C $WT format-patch
  16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1..fill/<unit>`, `src/<repo path of each owned file>`,
  `evidence/`), `git add inbox/fills/<unit> && git commit -m "fill <unit>: checkpoint <n>"` (or
  `final`), then `git push origin HEAD:exchange/pass-shelat-ch5-8`; if rejected, fetch, rebase
  (`git rebase origin/exchange/pass-shelat-ch5-8`), and push again. Never force-push. Change nothing
  else on that branch. Do not push your `fill/<unit>` branch anywhere.
- Record in `REPORT.md` that you ran as an internal worker under this note (no preflight or cache
  step), the machine's `nproc` and free memory at start, and each module check's time.
