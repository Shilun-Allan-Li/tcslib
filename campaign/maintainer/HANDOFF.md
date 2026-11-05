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

## 2. State (updated 2026-11-04, about 22:40 PST)

| PR | What | Replay | Gate | Next |
|---|---|---|---|---|
| #188 | E-D's landing: `exists_diagonalizer` proved | `replay-led2` **passed** (3/3, at `02030b70`) | 93, round 2 **dispatched** | merge on a PASS |
| #189 | G5's statements: `two_work_tapes_run` (`sorry`), `alphabet_reduction_run`, `exists_code2TM`, the `Encoding` renaming lemma, `universal_TlogT` | `replay-lg5` **running** (325 modules from `oleans-ledge`) | 92 **dispatched** | merge on a pass and a PASS; then G5's fill brief |
| #190 | the configuration facts (`CfgFacts`, five lemmas; private copies re-pointed) | `replay-lcf2` passed at `95d54ce2`; the certifying replay is the merged-tree one after #189 | 94 to stage | merge after #189 |
| #191 | NF's landing: `exists_codeNDTM_accepts_linear` proved | after #190 merges | a light fill gate (95) to stage | retarget from `lean/cfg-facts` to the campaign once #190 merges; merge the campaign; replay |

With #188 and #191 merged, `NTimeHierarchy`'s three theorems should be free of `sorryAx`.
Confirm this with `#print axioms` at that tree.

## 3. Queue after the PRs

1. **G5's fill brief:** Hennie–Stearns over G2–G4's zone contracts. The two carried minors of
   gate 22 are pinned (plan §2), and `k = 0` is handled separately. Codex first.
2. **The general `savitch`'s deepening fill:** its brief is due now that #182 and #184 have
   merged. The route is pinned in
   `campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md` §8, and the route probe is
   `probes/DeepenRoute.lean.txt`.
3. **H's brief:** re-take its pre-ship after NF and E-D land. Its screen population includes both
   files, and NF-X1's `un_setup` pair.
4. **The dedup window (12.2c):** the ledger's acknowledged families, among them LS-1, LS-3, BL-1
   (scoped by kind), CL-1, AS-1, RC-1–3, QF-1 and NF-X1.
5. **The deferred cleanup of public-facing docstrings** (WORKFLOW §2): about 280 campaign labels in
   existing Lean text, and E-D's frozen proof sketch (F9).
