# Native Mac setup and snapshot receipt

Codex took over on 2026-11-06 PST / 2026-11-07 UTC. `setup-initial.json` is the immutable initial setup observation, before the bootstrap or E-PAD receipt; its not-started fields are historical, not current status. HANDOFF §0 tracks the current work.

- Campaign checkout: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-arora-barak-ch3-4`.
- Exchange subtree: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/arora-barak-ch3-4`.
- Scratch: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch`; source `env.sh` at the start of every command.
- Managed worktrees are linked under scratch as `wt-hk` (records), `wt-camp`, `wt-sg1`, `wt-natbits` and `wt-epad`; `wt-xch` points to the shared exchange checkout. They share Git objects with the campaign checkout rather than re-cloning. Every Lean worktree's `.lake/packages` is linked to the original checkout.
- Native pinned Lean 4.25.0 and its matching Lake. Initial machine check: 12 CPUs, 18 GiB RAM, about 464 GiB free. No `lake build` was used.
- All present dependency revisions match the manifest (`manifest.log`). The absent documentation-only packages were not needed for proof elaboration. All 431 checked Mathlib roots had usable cached products; the narrowed import probe exited zero. The already cached PFR products let the native bootstrap include the full closure, with zero skips.

## Complete campaign snapshot

`oleans-mac0` is the native compiled tree at `680760723d72826469d0fc294e4d7ee2ecac3e6c`. This commit and the prior merge of #221 have identical Lean. The actual bootstrap ran through `slotrun.sh` and the prescribed `bootstrap-snapshot.sh`; `bootstrap/bootstrap.log` ends **# modules=894 failed=0**. Its complete order and empty skip list are retained. No compiled snapshot was assumed from the previous VM.

The bootstrap and initial checks used two Lean slots. When two jobs from the other campaign were found outside these locks, our two replays were suspended, preserving their state. The user then raised the machine-wide cap to **five**. The current local budget is **three**, set by `TCSLIB_LEAN_SLOTS=3` in scratch `env.sh`, leaving two for the other chat. The wrappers accept budgets 1–5; leanelab owns its slot, while a replay holds one through slotrun. See `resource-pause.json` and `resource-cap-five.json` for the actual pause/resume. Copy-text screens separately take `locks/screen`, one process at a time. All Python invocations use `python3 -I`. Preflights/seals run read-only against an already completed import closure; they are distinct from the full merged-tree replays.

## Reproduction tools and attribution

The eight scratch API files were copied from `devtools/seyoon/scratch-api/`; the replay helper directory was copied from `devtools/seyoon/`. Its `mk-next.sh` hard-coded Claude attribution, so the scratch copy was patched to Codex author, committer and co-author trailer before any merge. The exact patched script is retained here as `mk-next-codex.sh` (SHA-256 `307e4589665c967bd4cfde8d72645096cfdc7bf4e2e9a4e03ea123ee59b81f4e`). To reproduce it, copy the full helper directory before replacing that one file; its sibling tools are required. No shared Git identity configuration was changed.

`run-replays.py` waits for the complete bootstrap and checks three-dot changed-file counts before generating each prescribed replay; Git mutations and prechecks are sequential. Its independent snapshots all start from `oleans-mac0`, never from a composition of PR snapshots. `source-checks.py`, `search-sources.py`, `run-screens.py`, `prepare-probes.py`, `prepare-epad-probes.py` and `run-probes.py` preserve the source exports, candidate searches and exact executed probe inputs/results.

The records-only direct-push exception was explicitly reconfirmed by the user. Lean changes remain isolated in PRs #215, #222 and #228. The shared exchange checkout may contain another chat's work: preserve it, use only the campaign subtree and pull with rebase before each push.
