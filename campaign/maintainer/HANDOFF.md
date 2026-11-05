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

6. **Cloud specifics, learned 2026-11-05** (the first cloud session):
   - **Profile edits are refused**, so the variables live in `$TCSLIB_SCRATCH/env.sh` (with elan's
     `bin` on `PATH`); source it at the start of every command. elan is installed with
     `--no-modify-path` and no default toolchain; the pin comes from `lean-toolchain`.
   - **The cache:** narrowed to the Mathlib roots of the bootstrap set plus the open PR heads
     (355 roots, 3,605 files, from the Azure host `lakecache.blob.core.windows.net`, 0 failures).
     `mathlib4.lean-cache.cloud` is refused by the proxy, but this Mathlib uses it only under
     `USE_FRO_CACHE=1`. A new Mathlib import needs a narrowed fetch for its root.
   - **A worker restart ends every process**, detached ones included, and restarts came while the
     session waited on the user. Long jobs must be resumable: `bootstrap-snapshot.sh <wt> <name>
     --resume` continues a killed bootstrap after its checks. After a restart, check
     `$TCSLIB_SCRATCH/fills/replay/*.log` and resume.
   - **`lean_check_tree.sh` takes no lock slot**, so a running bootstrap or replay holds slot 2 by
     hand: `mkdir $TCSLIB_SCRATCH/locks/lean-slot-2 && echo <its bash pid> > …/pid` (freed by the
     stale check when it dies).
   - **ext4 has no copy-on-write:** `cp -R` copies a snapshot in full (about 1 GB). Prune.
   - `mkreplay.py` calls `$TCSLIB_SCRATCH/api/staticsorry.py`: a copy of
     `devtools/seyoon/staticsorry.py`. `$TCSLIB_SCRATCH/api/chain.py` lists a change's pre-replay
     compile chain.
   - **Sub-agents:** at most five at once, for independent tasks (WORKFLOW §5).
   - **PFR is left out** (ruled by the user, 2026-11-05: option B). The Mathlib cache does not
     provide the `PFR` package's oleans, so the twenty `CommunicationComplexity/NewmanTheorem`
     modules that import it (directly or not) are left out of cloud snapshots
     (`bootstrap_order.py`; `skipped-<name>.txt`). They are outside WORKFLOW §2's snapshot areas,
     and no open PR's replay reached them. Building them would need a direct `lean` run over 31
     PFR modules, which the rules do not cover: ask the user first.

The local Mac's snapshots (`oleans-*`) and review folders are not carried over. Every record the
gates cite is in the repository: packs, evidence, reviews, reports and deliveries' evidence.

## 2. State (updated 2026-11-05, about 10:40 PST): quiescent, no replay owed

**Merged on 2026-11-04/05:** #181 (space facts), #182 (ARM embedding), #184 (the codec's edge mode),
#189 (G5's statements; gate 92), #188 (E-D's landing, `exists_diagonalizer`; gate 93), #190 (the
configuration facts; gate 94, `replay-lcf3`).

| PR | What | Replay | Gate | Next |
|---|---|---|---|---|
| #191 | NF's landing: `exists_codeNDTM_accepts_linear` proved | `replay-lnf` **passed** (4 modules from `oleans-lcf3`, at `e8994dc1`; 0 `sorry`) | 95 **dispatched** 2026-11-05 (`outbox/gates/95-nf-landing-fill-gate/`, 415 sections) | merge when gate 95 closes |
| #196 | the deepening's API: `SavitchARM/Window` (window exactness, termination) and eleven facts in eight files (design §9–§10; decisions 4 and 5) | `replay-ldwa` **passed** (73 modules from `oleans-lcf3`, at `89f4ebbc`; the existing 30 `sorry`s) | 96 **dispatched** 2026-11-05 (`outbox/gates/96-deepen-api-gate/`, 209 sections) | merge when gate 96 closes; then issue the deepening fill (Claude) |
| #197 | G5's consumer API (decision G5-F1, API first): `Build/ZoneStep` (`exists_zoneTrackStepTM`, the amortization), `Contract.zero`, `ZoneRebalance`'s equations | `replay-lzsa` **passed** (111 modules from `oleans-lcf3`, at `0a1b64d5`; the existing 45 `sorry`s) | 97 **staged** (`outbox/gates/97-zone-step-api-gate/`, 91 sections) | dispatch gate 97; merge when it closes; then G5's fill brief |

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

Two October re-points may still be 12.2c material. The user had them pushed as archive branches
(2026-11-05):
- `archive/mac/canon-mapcomp-repoint` (`e4c5d015`): `CodeSimulator`'s grammar-stage relabeling as
  `Cfg.mapState_mapState`;
- `archive/mac/r-leaf-repoint` (`89bf6acb`): `NDCodeSimulator`'s input rewinds as
  `Build/InputRewind`'s.

The rest stay on the Mac.

`maint/12.2c-t2a` (2026-10-12) is the T2a facade wiring.

**Update (2026-11-05, cloud session, about 14:30 PST).** The first cloud snapshot is
**`oleans-cloud0`**: 869 modules (the root's import closure less the 20 PFR modules), at
`dfed8b1f`'s Lean tree, `$TCSLIB_SCRATCH/fills/replay/bootstrap-oleans-cloud0.log`. Each PR's
replay below chained from it with only its own PR.

| PR | Head | Replay | Gate | Next |
|---|---|---|---|---|
| #191 | `ac934f99` (the repair `10c01517` + a records-only merge) | `replay-lnf2` **passed** (4 modules, 0 `sorry`) | 95 round 1 does not close (0/1/4); **round 2 staged** (`outbox/gates/95-nf-landing-fill-r2-gate/`, 84 sections) | dispatch round 2; merge when it closes |
| #196 | `ce9d63f4` (the repair `b1b5199b` + a records-only merge) | `replay-ldwa2` **passed** (73 modules, the existing 30 `sorry`s) | 96 round 1 does not close (0/2/4); **round 2 staged** (`outbox/gates/96-deepen-api-r2-gate/`, 149 sections) | dispatch round 2; merge when it closes; then the deepening fill (Claude) |
| #197 | `fde50a5a` (the closing commit `20e7fc75` + a records-only merge) | `replay-lzsa2` **passed** (111 modules, the existing 45 `sorry`s) | 97 **closed** (PASS 0/0/6, the minors swept) | **clear to merge**; then G5's fill brief |

**Merging several of these:** each replay chained from `oleans-cloud0` with only its own PR. Once a
second one merges, replay the downstream closure of every `.lean` file changed since `dfed8b1f`'s
tree, on the merged tree, chained from `oleans-cloud0` (WORKFLOW §2).

**The user's rulings (2026-11-05):** gate 95 F1 repair; gate 96 F2 harvest; WS-1 acknowledged by
kind and widened; QL-X1 an idiom and CQ-1 opened; gate 97 F5 publish; CE-1 acknowledged; PFR left
out of cloud snapshots. All are in `duplication-ledger.md` and the gates' `resolutions.md`.

**Duplication rulings of 2026-11-05 (the user)**, recorded in `duplication-ledger.md`:
- **WS-1**, acknowledged by kind and then **widened**: every proof that one step keeps a
  configuration within a window of any shape, and window monotonicity; canonical
  `Cfg.InWindow.apply_iff`, `Cfg.InWindow.mono`, and the tape half (to be published in 12.2c;
  `Oracle`'s private `apply_workTapes_eq_of_ne` is its source).
- **CE-1**, acknowledged for 12.2c: `coreSum_eq_of_code_eq`, public in both `ExpBFS/Radius` and
  `Randomized/BPLInPCount`.
- **QL-X1**: the `NoEdge`/`Rel` pair is an idiom; **CQ-1** opened (codec-level query predicates).
- **ZP-1**: `zoneRowPre_congr` and `zoneRowPre_mapState_iff` published; `ZoneRebalance`'s twelve
  inline sites re-pointed in 12.2c.
- Maintainer records with them: RN-1 accounting (`nf_pack`), RC-4 (F8's row candidates), WL-1,
  WC-1 (optional), RP-1 (definitional reads #196's equations can replace).

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
   (scoped by kind), CL-1, AS-1, RC-1–3, QF-1 and NF-X1; since 2026-11-05 also WS-1 (scoped by
   kind and widened; publish the tape half first), RC-4, CE-1, ZP-1, CQ-1, WL-1, RP-1 and WC-1
   (optional), with QL-X1 an idiom exclusion.
5. **The deferred cleanup of public-facing docstrings** (WORKFLOW §2): about 280 campaign labels in
   existing Lean text, and E-D's frozen proof sketch (F9).
