# EF-R2/R3 `ef-r23-regev` · final r1 · landing

**Landing branch pushed: `land/ef-r23-regev` at `fc0957421cb538ca3e316186c8c167d7e647dd12`.** It is based on
`iO/phase-a-base` (`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`) and holds the three worker commits plus one
maintainer commit, LE-coins. The rulings are EF-R23-R1 (A), R2 (A) (ledger DL-63, done), W1 (A) and W2 (A),
in the decision-log rows of 2026-11-18. **No PR is open yet**: Seyoon opens it as a draft. The body below is
ready to use.

Run on 2026-11-19, 00:14–00:25 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`, and the work is in
`$SP/land-efr23/`.

## Inputs

- **Delivery.** `inbox/fills/ef-r23-regev/` at exchange commit `226ae633d73694b559fc18eb52b0f996968c918a`.
  - Its tree there is `84bde7a3…`. That is the same tree as at the reviewed delivery commit `4b6d3db5` and at
    the exchange tip `87039c4d` when the job ran, and no commit touches the path between them.
  - The patches and `src/` verify against the delivered `SHA256SUMS`.
- **Evidence zip** `ef-r23-final-r1-evidence.zip`: its SHA-256 `a9aee685…` matches `evidence-SHA256SUMS`.
  `phase2/le-coins.patch` is the demonstrated LE-coins diff.

## Commits

| # | Landing commit | Worker commit | Author (kept) | Subject |
|---|---|---|---|---|
| 1 | `56c14c0693b37cde51ee9beeca1fc17b51826727` | `c7b23617` | Claude, 2026-11-18T10:10:03Z | Encoding: general-modulus arithmetic toolkit (EF-R2/R3 series 1) |
| 2 | `5125c540458e1b2003f5a04dad0cf93b0be65a18` | `daaf5e65` | Claude, 2026-11-18T10:10:03Z | Regev symmetric: shift reduction NUPPT and single-message security (EF-R3) |
| 3 | `3398032adecd484f692a9b7e5c27c8a9bbaf9d41` | `324c5de2` | Claude, 2026-11-18T10:36:08Z | Regev PKE: encryption reduction NUPPT and single-bit security (EF-R2) |
| 4 | `fc0957421cb538ca3e316186c8c167d7e647dd12` | (maintainer) | Claude | Regev PKE: reuse EnsembleLemmas.coinsEquiv in exists_reductionMachine (LE-coins) |

- **Commits 1–3** come from `git am -3 -S` of the three delivered patches.
  - Author name, email, date and message are byte-identical to the worker's commits, so the worker's own
    `Claude-Session` trailer is kept (I6).
  - Each commit's tree equals its worker commit's tree. The tree after commit 3 is
    `4f05a1af55ed8677da65a9e679e3138cc9726f65`, which is `324c5de2`'s tree.
  - The six files are byte-identical to the delivered `src/` (`6c691b8e…`, `b8245050…`, `ce8c8141…`,
    `f0f062cd…`, `4eb20648…`, `553343e4…`).
- **Commit 4** is staged by explicit path. Its message ends with the required two trailer lines.
- **All four commits are SSH-signed** (one `gpgsig` each). The branch has 6 files, +1,473/−0 against the base.

## LE-coins (EFR23-F01, ruling EF-R23-R1 (A))

This is a proof-only change in `exists_reductionMachine`, +6/−5 with maximum width 100. It changes no
statement. The resulting blob is `829d7e37…`, the same blob as phase 2's demonstration commit `90123822`, so
this is the demonstrated diff exactly.

```diff
@@ -290,7 +290,7 @@ its advice holds `n`, `m`, `q`, the width and the codepoint of `μ`.
-3. Coins: the relabelling `((t, v), u) ↦ t ++ u ++ v` (`Fin.appendEquiv`, `finCongr`) of
+3. Coins: the relabelling `((t, v), u) ↦ t ++ u ++ v` (`EnsembleLemmas.coinsEquiv`) of
@@ -335,12 +335,13 @@ theorem exists_reductionMachine (F : LWE.Family) (μ : Bool) (D : NUPPT) :
-      ((Fin.appendEquiv _ _).prodCongr (Equiv.refl (D.Coins κ)))).trans
-      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)))
+      ((EnsembleLemmas.coinsEquiv rfl).prodCongr (Equiv.refl (D.Coins κ)))).trans
+      (EnsembleLemmas.coinsEquiv hlen.symm)
   have hφ (t : T) (v : D.Coins κ) (u : U) :
       List.ofFn (φ ((t, v), u)) = List.ofFn t ++ List.ofFn u ++ List.ofFn v := by
-    change List.ofFn (fun i => Fin.append (Fin.append t u) v (Fin.cast hlen.symm i)) = _
-    rw [← List.ofFn_congr hlen, List.ofFn_fin_append, List.ofFn_fin_append]
+    change List.ofFn (EnsembleLemmas.coinsEquiv hlen.symm
+      (EnsembleLemmas.coinsEquiv rfl (t, u), v)) = _
+    rw [EnsembleLemmas.ofFn_coinsEquiv, EnsembleLemmas.ofFn_coinsEquiv]
```

The full diff is `$SP/land-efr23/le-coins.diff` (`git show fc095742`).

## Re-check on the landing head

The re-check used phase 2's recipe: `snapshots.md` job recipe and the tools in
`olean-advance-a6d01b1b/tools-used/`. Every tool ran with `python3 -I`. There was no `lake build` and no cache
get.

- **Scratch check head** (never pushed).
  - I made a sparse detached worktree at phase 2's scratch merge `45769ce2` (`iO/phase-a-base` merged with
    `bff0567b`, tree `1a55e8aa…`) and added unsigned cherry-picks of the four landing commits.
  - The result is `d898a09f8b758c74874350d79939c2a2204ad972`, tree `740e0153fd7041bb54b82e6b7d0b8d32208643aa`,
    which equals `git merge-tree --write-tree fc095742 bff0567b`.
  - After the third cherry-pick the tree is `013ee3de…`, phase 2's check head.
  - Against phase 2's check head `15e18eb8` the only change is the PKE owner (+6/−5).
- **Olean tree.**
  - I state-checked `$SP/olean-replay-efr23` first: `stateplan check` at `15e18eb8` over phase 2's
    `full-order.txt` and `state.json` gave 1470/1470 RESULT OK. No file there is newer than phase 2's end.
  - I copied it with `cp -al` to `$SP/land-efr23/replay`: 1503 files, all hard links, plus 3346 Mathlib
    symlinks.
  - Snapshot #11 `snapmap verify` gave 0/0/0, RESULT OK, before the run, after the build and at the end.
- **Plan.** `fullorder` at `d898a09f` gives 1470 modules, identical to phase 2's. `stateplan plan` gives
  **5 to build and 1465 reused**:
  - the PKE owner `Encryption/PublicKey/Regev/Asymptotic`;
  - `Encryption/PublicKey/Regev`, `Encryption/PublicKey` and `Encryption`;
  - root `TCSlib`.
  - Neither `audits/*/Checks` is in the PKE owner's downstream.
- **Build** (`runner.py`, one Lean process at a time).
  - **5/5 rc 0.** `error:` 0, `error(` 0, substring "error" 0, `sorry` 0, warnings 0. `permod.py` found no
    log/record mismatch.
  - The PKE owner took 2.96 s and root `TCSlib` 3.75 s (maxrss 4.56 GB).
  - `stateplan update` took 5 modules. `check` at `d898a09f` gave **1470/1470, RESULT OK**.
  - The 5 rebuilt oleans have link count 1.
  - `$SP/olean-replay-efr23` still checks RESULT OK at `15e18eb8` after the run, so nothing was written
    through.
- **Admissions.** The six files contain 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque`.
  `style_lint.py` on the edited owner reports 0 findings.
- **Axioms** (`runner_full.py`, no `-o`). The probe is phase 2's `AxiomsHead` with four `#print axioms` added,
  and it ran with rc 0, 0 errors.
  - **80 stored constants** (65 declarations, 15 auxiliary): 29 use `[Classical.choice, Quot.sound, propext]`,
    46 use `[Quot.sound, propext]` and 5 use `[propext]`. None is non-standard.
  - Constant set and axiom sets are identical to phase 2's.
  - `exists_shiftMachine`, `singleMessageSecure_of_dlweAssumption`, `exists_reductionMachine` and
    `singleBitSecure_of_dlweAssumption` each give `[propext, Classical.choice, Quot.sound]`.
  - The `sorry` control reports `[sorryAx]`, and its warning is the only one.
- **Canonical coe-A seal of the changed owner.**
  - I regenerated the collector from the recipe template with the three owners. It is byte-identical to
    phase 2's `CollectHead.lean`, and it ran with rc 0 and 0 errors on the landing tree.
  - `mkseals_coe.py` (A variant, unmodified, `SEAL_CHUNK=1000`) generated the seal for
    `TCSlib.Cryptography.Encryption.PublicKey.Regev.Asymptotic`: **1,147 requests**, 44 terms, 14 excluded
    terms, 18 stored constants.
  - The seal ran with **rc 0 and 0 errors**, and 0 `sorry`. Both parts have `G06-SEAL-END` with
    `requested = verified` (1000 + 147). `sealsum` gives 1 probe, 1 pass.
  - Phase 2's demonstration had 43 terms. The one extra term is `EnsembleLemmas.coinsEquiv`, now read from the
    landing source's collector. The seal still passes with it sealed.
- **decls2** (pinned `decls2.py`, `fa81981a`) of the landing head against `iO/phase-a-base` gives **62 ADDED,
  0 CHANGED, 0 REMOVED**.
  - Compared with the review's `decls2-mine.txt` and the delivered `statements/decls2.txt`, the rows are the
    same except for row order and one line number: `singleBitSecure_of_dlweAssumption` moves from `:397` to
    `:398`, because LE-coins adds one line.
  - decls2 of the LE-coins commit alone (against `3398032a`) is empty. **LE-coins adds or changes nothing.**
- **Lean slots.** Three runs: the build, the probes and the seal. Before each start `pgrep -x lean` showed
  0 processes on the host, and none was killed.

## State after the job

- **Kept for the Codex gate** (about 40 MB of unique data; the replay is 0.8 MB beyond its hard links):
  - `$SP/land-efr23/replay` is the olean tree accepted at check head `d898a09f`, matching the landing head.
    State: `$SP/land-efr23/check/state.json`.
  - `$SP/land-efr23/tree` is the export of `d898a09f`.
  - `$SP/land-efr23/mergewt` is the scratch worktree at `d898a09f`, with probes under `EFR23Land/`.
  - `$SP/land-efr23/wt` is the landing worktree on `land/ef-r23-regev`.
  - Delete all four after the gate.
- **Phase 2's `$SP/olean-replay-efr23` is now superseded** for the gate, because it holds the pre-LE-coins
  check head. Its owner may delete it. This job did not touch it.
- **Logs and records** are in `$SP/land-efr23/check/`: `build/`, `probe-runs/`, `seal-runs/`, `seal/A/`,
  `permod.log`, `stateplan-*.log`, `linkcount.log`, `snap-verify-*.log`, `slot.log`, `decls2-landing.txt`.

## Draft PR body

Use base `iO/phase-a-base` and head `land/ef-r23-regev`, and open it as a **draft**.

Title: `EF-R2/R3: Regev symmetric and PKE reductions as proved NUPPT machines`

```markdown
Efficiency wave 1, job EF-R2/R3 (`ef-r23-regev`). It replaces the Regev symmetric and public-key security
reductions with **proved `NUPPT` machines**, so both security theorems rest on `DLWEAssumption` alone (the PKE
one also needs the existing width condition) and have no efficiency hypothesis. Audit rows R43/R44 become
class M.

**Stacked PR.** The base is `iO/phase-a-base` (`5ed465f6`), which merges #374, #378, #384 and #380, all still
open. Like #387, this PR lands after those four. Its own diff is 4 commits and 6 files, +1,473/−0.

## Contents
- `Encoding/ModularArithmetic.lean` (new, series 1) is a uniform general-modulus toolkit on the fixed-width
  `encodeVector` layout: `addMod`, `vecAddModWords`, `subsetSumModWords`, `modContext`, their correctness
  readers and their `PolyTimeComputable` theorems. It is built only on registered hosts. **This delivery
  supplies EF-R1's toolkit**: the GSW reductions will build on it.
- `Encryption/Symmetric/Regev/Asymptotic.lean` (new) proves `exists_shiftMachine` (an equality) and
  `singleMessageSecure_of_dlweAssumption`.
- `Encryption/PublicKey/Regev/Asymptotic.lean` (new) proves `encodeView` with its readers,
  `exists_reductionMachine` (an equality) and `singleBitSecure_of_dlweAssumption`.
- The three facades each gain one import and one Contents bullet. `TCSlib.lean` is unchanged.

The reductions come from `NUPPT.exists_realizesOn_of_preTarget_id`; the PKE reduction also uses
`NUPPT.exists_split`. The parameters and messages are advice only. The four targets are stated exactly as in
the brief.

## Commits
1. `56c14c06` Encoding: general-modulus arithmetic toolkit (EF-R2/R3 series 1) (worker)
2. `5125c540` Regev symmetric: shift reduction NUPPT and single-message security (EF-R3) (worker)
3. `3398032a` Regev PKE: encryption reduction NUPPT and single-bit security (EF-R2) (worker)
4. `fc095742` LE-coins, a maintainer landing edit (EFR23-F01, ruling EF-R23-R1 (A)). It is a proof-only change
   that reuses `EnsembleLemmas.coinsEquiv`/`ofFn_coinsEquiv` in `exists_reductionMachine` and changes no
   statement.

Commits 1–3 are the worker's commits applied with `git am`: authorship and messages are kept and the trees
are identical. All four commits are signed.

## Checks
- **Maintainer review:** ACCEPT WITH LANDING EDITS (`briefs/efficiency-gaps/wave1/EF-R2-R3/final-r1/`), and
  the one landing edit is applied. Rulings: EF-R23-R1 (A), R2 (A) (ledger DL-63), W1 (A), W2 (A).
- **Merged-tree replay on olean snapshot #11** (`bff0567b`). Phase 2 rebuilt 26 modules with rc 0, including
  root `TCSlib` and both `audits/*/Checks`. On the landing head, the PKE owner and its downstream (5 modules,
  root included) were rebuilt with rc 0, 0 errors and 0 `sorry`. The state check over the full order gave
  1470/1470 OK.
- **Axioms:** all 80 stored constants of the three new modules are standard. The four targets use
  `[propext, Classical.choice, Quot.sound]`.
- **Canonical coe-A seals:** 0 errors for the three owners in phase 2, and 0 errors for the edited PKE owner
  on the landing head (1,147 requests). The paired controls are ALL_OK.
- **decls2** against the base: 62 added, 0 changed, 0 removed.
- **Admissions and lint:** 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque`, and the lint has no new
  finding.

## Still to do
- **A Codex gate is to be staged** for this PR.
- Merge after #374, #378, #384 and #380.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
```
