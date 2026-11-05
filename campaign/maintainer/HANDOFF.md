# Handoff: the ch. 3–4 maintainer session moves to a cloud VM

Ruled by the user on 2026-11-04: the campaign moves to a cloud machine like the Pass–Shelat line,
with the exchange in the `arora-barak-ch3-4/` folder of the orphan branch
`exchange/pass-shelat-ch5-8`. The handoff point is **quiescent**: the heavy local replays finish
on the Mac first. Read `WORKFLOW.md` (beside this file) first; it holds the standing rules. The
long-form state is in `campaign/backlog.md`, and the duplication debt in
`campaign/duplication-ledger.md`.

## 1. Starting a session on a new machine

1. **Environment.**
   - Network access to Mathlib's cache hosts (`lakecache.blob.core.windows.net`,
     `mathlib4.lean-cache.cloud`), the same custom environment as the Pass–Shelat line.
   - `TCSLIB_SCRATCH` set to a scratch directory with about 15 GB free, and `TCSLIB_REPO` to the
     clone. The exchange worktree's path, `$TCSLIB_SCRATCH/wt-xch/arora-barak-ch3-4`, goes in
     `TCSLIB_EXCHANGE` for `stage.sh`.
2. **Checkouts.**
   - Clone `https://github.com/Shilun-Allan-Li/tcslib` and fetch with
     `+refs/pull/*/head:refs/remotes/origin/pr/*`, so that the name searches see every PR head.
   - **The records worktree:** `git worktree add --detach $TCSLIB_SCRATCH/wt-hk
     origin/complexity/arora-barak-ch3-4`. The tools assume `wt-hk` under the scratch dir. Push
     records with `git push origin HEAD:complexity/arora-barak-ch3-4`, after
     `git fetch && git rebase origin/complexity/arora-barak-ch3-4`.
   - **The exchange worktree:** `git worktree add --detach $TCSLIB_SCRATCH/wt-xch
     origin/exchange/pass-shelat-ch5-8`. Touch only `arora-barak-ch3-4/`, and pull with rebase
     before every push.
   - **Every worktree** needs `mkdir -p <wt>/.lake && ln -s <clone>/.lake/packages
     <wt>/.lake/packages`.
3. **Mathlib.** In the clone, run `lake exe cache get`, never `lake build`. Then check that
   `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib` exists. The fill-environment addendum
   (`campaign/standards/fill-environment-addendum.md`) records the cloud recipe the fill workers
   use: a narrowed fetch, the manifest check, and the Lean start-up fallback.
4. **The first snapshot.** `bash wt-hk/devtools/seyoon/bootstrap-snapshot.sh wt-hk
   oleans-cloud0` compiles the root's import closure, 886 modules, one at a time. The local
   Mac's 313-module replay took 16 minutes, and the VM is two to three times slower. The log's
   first line names the commit. Later replays chain from this snapshot with
   `devtools/seyoon/mk-next.sh`, so give it as `<snapshot-tree commit>`.
5. **Copy-text screens:** `scripts/copy-text-screen-v3.py`, one at a time under
   `$TCSLIB_SCRATCH/locks/screen`.

The local Mac's snapshots (`oleans-*`) and review folders are not carried over. Every record the
gates cite is in the repository: packs, evidence, reviews, reports and deliveries' evidence.

## 2. State (updated 2026-11-05, about 10:05 PST)

**Merged on 2026-11-04/05:** #181 (space facts), #182 (ARM embedding), #184 (the codec's edge mode),
#189 (G5's statements; gate 92), #188 (E-D's landing, `exists_diagonalizer`; gate 93), #190 (the
configuration facts; gate 94, `replay-lcf3`).

| PR | What | Replay | Gate | Next |
|---|---|---|---|---|
| #191 | NF's landing: `exists_codeNDTM_accepts_linear` proved | `replay-lnf` **passed** (4 modules from `oleans-lcf3`, at `e8994dc1`; 0 `sorry`) | 95 **dispatched** 2026-11-05 (`outbox/gates/95-nf-landing-fill-gate/`, 415 sections) | merge when gate 95 closes |
| #196 | the deepening's API: `SavitchARM/Window` (window exactness, termination) and eleven facts in eight files (design §9–§10; decisions 4 and 5) | `replay-ldwa` **passed** (73 modules from `oleans-lcf3`, at `89f4ebbc`; the existing 30 `sorry`s) | 96 **staged** (`outbox/gates/96-deepen-api-gate/`, 209 sections) | dispatch gate 96; merge when it closes; then issue the deepening fill (Claude) |
| #197 | G5's consumer API (decision G5-F1, API first): `Build/ZoneStep` (`exists_zoneTrackStepTM`, the amortization), `Contract.zero`, `ZoneRebalance`'s equations | `replay-lzsa` **ready to run** (111 modules from `oleans-lcf3`, at `0a1b64d5`) | 97 drafted (`campaign/gates/97-zone-step-api/`) | replay; stage gate 97; then G5's fill brief |

On #191's merged tree the nondeterministic time hierarchy is admission-free:
`ntime_hierarchy`, `ntime_hierarchy_of_pos` and `NTIME_linear_ssubset_square` rest on the
standard axioms (gate 95's `evidence/axioms/NTHAx.out`). With #191 merged, the headline count is
expected to reach **21 of 26**; the status record is `campaign/status/2026-11-05-headlines/`.

**Merging several of these:** each replay above chained from `oleans-lcf3` with only its own
PR. Once two or more have merged, the merged campaign's first snapshot (§1, item 4) is the replay
of record for the combination.

**Mac-only branches with commits not in the campaign** (checked 2026-11-05; none has an upstream
that contains them). Most are superseded deliveries or landings:
- `deliver/fill-eq-query-in`, `deliver/fill-s13d-g4-cont4-in`, `deliver/fill-u2s-universal-in`;
- `lean/g4-cont1-partial`, `lean/ntime-diag-bf`, `lean/seam-layout`;
- `local/eq-cp1-landing`, `local/eq-cp1-landing-v2`;
- `dedup/ch34-d4`, which has no Lean.

Two October re-points may still be 12.2c material:
- `local/canon-mapcomp-repoint`: `CodeSimulator`'s grammar-stage relabeling as
  `Cfg.mapState_mapState`;
- `local/r-leaf-repoint`: `NDCodeSimulator`'s input rewinds as `Build/InputRewind`'s.

`maint/12.2c-t2a` (2026-10-12) is the T2a facade wiring.

## 3. Queue after the PRs

1. **The general `savitch`'s deepening fill** (agent: Claude, the user's 2026-11-05 choice). The
   brief `campaign/fills/ch34/briefs/ch34-fill-deepen-DRAFT.md` issues after #196 merges, with
   its pre-ship re-run on the merged tree and its `@TBD@` items measured. The design is
   `campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md` §8–§10.
2. **G5's fill brief**, after #197 merges: Hennie–Stearns over the zone layer, citing
   `Build/ZoneStep`. The fill writes the controller, its invariant and the count bound; `k = 0`
   is handled separately (plan §2). Codex first, by the soft rule.
3. **H's brief:** re-take its pre-ship after NF and E-D land. Its screen population includes both
   files, and NF-X1's `un_setup` pair.
4. **The dedup window (12.2c):** the ledger's acknowledged families, among them LS-1, LS-3, BL-1
   (scoped by kind), CL-1, AS-1, RC-1–3, QF-1 and NF-X1.
5. **The deferred cleanup of public-facing docstrings** (WORKFLOW §2): about 280 campaign labels in
   existing Lean text, and E-D's frozen proof sketch (F9).
