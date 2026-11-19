# GSW 6b U15+U17 `gsw-6b-u15-u17` · final r1 · phase 2: replay on olean snapshot #11

**Verdict: PASS, with no new finding.** The delivered head `619d2029` was replayed on its own copy of snapshot #11 (B6 +
the unit), then **stacked on the records tip** (which already carries U12/U13, #392) on a second copy. Both build with
the root `TCSlib`; `Circular.olean` and `LeveledSecurity.olean` are byte-identical in the two trees. As an extra, the
full 6b stack (records tip + U14+U16 + U15+U17 + U18+U19) was replayed once for both units of this review.

- **Build.**
  - **B6 + U15+U17:** 7/7 modules rc 0, including the root `TCSlib`; 0 `error:`/`error(`, the substring "error" 0
    times. The only warnings are the 2 `sorry` warnings of `Asymptotic` (U18-U19's A1, A3).
  - **Stacked on the records tip:** 12/12 rc 0, 0 errors; the 12 `sorry` warnings are other units' targets (Bootstrap
    5, Leveled 2, PolyRatio 3, Asymptotic 2).
  - **Checks.** No `audits/*/Checks` imports a changed module; both are in the full order, reused, and pass the state
    check.
- **Admissions:** **39 in 14** on B6 (`base-sorries.txt` minus G15, L4, L5: the brief's C2 count); 30 in 12 stacked.
- **Axioms.** All 67 stored constants of the two modules are standard, 0 `sorryAx`, in both trees, with the same names
  and sets as the worker's census. G15, L4, L5: `[propext, Classical.choice, Quot.sound]`.
- **Seals.** Canonical coe-A and seal B: rc 0, 0 errors; Circular 464 and LeveledSecurity 1,561 (A) / 1,562 (B)
  requested and verified.
- **Controls.** 2 liveness pairs per owner, ALL_OK. **Unfold scan:** 0 foreign definitions.
- **Duplication probes.** No lemma for D1, D2, D4; K2 finds the lemma used; K1, D3, D5 inconclusive (timeouts).
- **Lint.** Unchanged. **Snapshot #11:** 0/0/0 before, mid-run and at the end.

Run on 2026-11-19 from 01:36 to 02:21 UTC (this unit 01:36–02:01, then U18+U19, then the full stack). `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`; the work directory is
`$SP/g6b-u1517-1819/`.

- **Lean processes.** One at a time: 77 starts plus 2 `mathlibextra`, for both units together.
  - Each start went through `runq.sh`, which checks before the start that at most 2 other Lean processes are running
    (`pgrep -fc "bin/lean "`, so the machine stays at ≤ 3) and that at least 2,000 MB is free, polling every 60 s while
    full. Every start is in `logs/slot.log`.
  - Never more than 2 other Lean processes were running at a start, and no start waited. The lowest free disk at a
    start was **6,315 MB**.
- **Not done.** No `lake build`, no cache get, no commit on any ref, no branch, no push, no PR.
- **Not touched.** The snapshot was read and hard-linked only. No other job's tree, worktree or process was touched
  (`$SP/g6b-u1416/` was read only, for its tool forms).
- **Deleted at the end:** both replay trees of this unit, each after its end-of-run state check.

## P2-0 Inputs

| Input | Result |
|---|---|
| **Records tip** | `c87eb40365e8ccd44f02ca54f6e5e4f0e50de633` when read, later `a25338e0` (records-only commits). Both have `TCSlib` tree `745bf4b4` = B6 + U12/U13: `git diff --name-only bff0567b <tip>` over `TCSlib`, `TCSlib.lean`, `audits`, the lake files and `lean-toolchain` is `Branching.lean`, `DecryptFormula.lean`. |
| **Delivery** | Exchange `4da71016…` (origin tip), final `f501b6694`; extracted with `git archive`; both manifests pass (472 and 464 rows). |
| **Snapshot #11** | Map `e7bb03b4…867d0` and files manifest `463c8869…0b13`, re-hashed. `snapmap.py verify` before the copy: **0/0/0** over 1,487 files, RESULT OK. |
| **Recipe tools** | `olean-advance-a6d01b1b/tools-used/`, unmodified, byte-identical to the g6b-u1213 copy (64 files; `logs/recipe-tools-SHA256SUMS`). |

## P2-1 Heads (scratch only)

- **Worktree.** A detached sparse worktree `$SP/g6b-u1517-1819/wt` (`TCSlib/`, `TCSlib.lean`, `audits/`, `scripts/`, the
  lake files, `lean-toolchain`), `.lake/packages` symlinked to the repository's.
- **Reproduction.** The 3 patches on B6 give `f4219a24…`, `56fe8e9a…`, `619d2029…`, as delivered
  (`logs/repro-u1517.log`).
- **Stacked head.** `git merge-tree --write-tree 619d2029 c87eb403` is clean, tree `6d402542…`, `TCSlib` tree
  **`611a86b4cbcef82ed2e2fa04b9d7ba9b4f487542`** (the same against `a25338e0`). Committed with `commit-tree` (parents
  the tip and the head; on no ref) as **`67a69bae2b352fcc584c9cad1f34b3d51fde9d21`** (`logs/stack-head-u1517.txt`). Its
  diff against B6 is the two owned files plus U12/U13's two.

## P2-2 B6 + U15+U17 (the `snapshots.md` job recipe)

- **Copy and overlay.** `cp -al $SP/olean-snapshot`: 1,487 files, all hard links. `mloverlay.sh`: 3,346 Mathlib
  symlinks. `mathlibextra.sh` built `NthRootLemmas` with rc 0; its olean is **`c0a9cff0…`**, as required.
- **Plan.** `downorder.py` at `619d2029` against B6: **changed 2, down 7** (the two owned files, `Asymptotic`, the
  facades `GSW`, `Homomorphic`, `AdvancedEncryption`, and the root). `fullorder.py`: 1,456 modules, roots `TCSlib` and
  both Checks. `stateplan`: **7 to build, 1,449 to reuse**.
- **Build** 01:36:39–01:37:00. **7/7 rc 0**; 2.1–4.6 s per module; peak maxrss 4.57 GB (the root). The 2 `sorry`
  warnings are `Asymptotic`'s A1 and A3; `Circular` and `LeveledSecurity` have empty logs.
- **Accept.** `permod.py`: 7 modules, 0 bad, no log/record mismatch. `stateplan update`: 7 taken, none refused (binding
  every record's source SHA-256 to `git show 619d2029:<path>`). `check`: **1,456/1,456, RESULT OK**, again at the end.
  Link count 1: exactly the 7 rebuilt oleans plus `NthRootLemmas`, unchanged at the end.
- **Admissions** (`run/u1517-b6/admissions.txt`): **39 in 14**; removed exactly G15, L4, L5; none added.

## P2-3 Stacked on the records tip

- A fresh `cp -al` copy with the same overlay (`NthRootLemmas` hard-linked from P2-2's tree).
- **Plan** at `67a69bae`: changed 4, down 12; **12 to build, 1,444 to reuse**.
- **Build** 02:00:08–02:00:38: **12/12 rc 0**, 0 errors. The 12 `sorry` warnings: Bootstrap 5, Leveled 2, PolyRatio 3,
  Asymptotic 2 (U14+U16's and U18+U19's targets).
- **Accept.** `stateplan update` 12, `check` **1,456 RESULT OK** (and at the end), link count 1 for the 12.
- **Admissions:** **30 in 12** = base minus U12/U13's nine and this unit's three.
- **Cross-tree:** `Circular.olean` `7b69da6b…` and `LeveledSecurity.olean` `101d8764…` are byte-identical to P2-2's
  (`logs/olean-cross-u1517.txt`).

## P2-4 Axioms

`G6bProbe/u1517/Axioms` (the g6b-u1213/u1416 census form over `Circular` and `LeveledSecurity`, with a `sorryAx`
dependency trace, the three targets by name and a `sorry` control): rc 0, 15 s.

- **67 stored constants** (Circular 12, LeveledSecurity 55): 44 `[Classical.choice, Quot.sound, propext]`, 5
  `[Quot.sound, propext]`, 18 `[propext]`. **0 non-standard, 0 `sorryAx`, empty trace.**
- `logs/axcmp-u1517.txt`: the worker's `AxiomProbe-final.log` has the same 67 names (private prefixes normalized) with
  the same sets: RESULT SAME.
- **Targets** (census and `#print axioms`): G15, L4, L5 each `[propext, Classical.choice, Quot.sound]`.
- **Control:** `g6bSorryControl` `[sorryAx]`, the probe's only warning.
- **Stacked tree:** the same probe gives the identical census (`runs/u1517-stack-axioms`).

## P2-5 Rule 10

- **Collector.** `mkcollect.py` with the two owners: rc 0, 2,193 CAT rows; `Circular: stored 12`, `LeveledSecurity:
  stored 55`.
- **Canonical coe-A** (`mkseals_coe.py`, A variant, unmodified):
  - Circular: **464 requests** (22 term names, 11 excluded abbreviations), LeveledSecurity: **1,561 requests** (30 term
    names, 13 excluded abbreviations: `Ciphertext`, `Coins`, `KeySeed`, `LevelCoins`, `Parameters.columns`,
    `Parameters.lwe`, `PublicKey`, `Secret`, `LWE.Noise.Coins`, `LWE.Noise.fintype`, `LWE.Parameters.dimension`,
    `modulus`, `samples`).
  - **rc 0, 0 errors** for both: `G06-SEAL … requested=464 active=446 already_irreducible=18 verified=464` and
    `requested=1561 active=1542 already_irreducible=19 verified=1561`, each with its `G06-SEAL-END`.
- **Seal B** (`SEAL_EVAL=1`): 464 and **1,562** requests (`PolyExpr.eval` is in LeveledSecurity's closure, not
  Circular's); **rc 0, 0 errors**, verified = requested.
- **The worker's counts agree:** coe-A 464 / 1,561 and coe-B 464 / 1,562.
- **Liveness pairs** (`mkctl2.py`; appended to the canonical sealed copy and to the head source). NEG reads the body
  (`by intros; first | exact rfl | exact Iff.rfl`), POS uses the reader.

  | Owner | Pair | Sealed | Open |
  |---|---|---|---|
  | Circular | `GSW.realView` / `realView_eq` (phase 5) | NEG line 345: 1 error (Type mismatch); POS 346 passes | 0 errors |
  | Circular | `distAdv` / `distAdv_def` (Foundations) | NEG 349: 1 error; POS 350 passes | 0 errors |
  | LeveledSecurity | `hybridPlant` / `hybridPlant_eq` (EnsembleSecurity) | NEG 865: 1 error; POS 866 passes | 0 errors |
  | LeveledSecurity | `GSW.reduction` / `reduction_eq` (phase 5) | NEG 869: 1 error; POS 870 passes | 0 errors |

  Sealed: exactly one error at each NEG line, so **ALL_OK** (`logs/controls-check-u1517.txt`). All four definitions are
  among the requests. These differ from the worker's pairs (`realView`, `levelKey`).
- **Explicit-unfold scan** (`unfoldscan.py` against the CAT rows): 155 identifiers; 3 resolve to a TCSlib definition,
  all `levelPosHybrid`, the file's own private `def` (own definitions may be read, COMMON §5.1). **0 foreign.** The
  `let`-bound bijections `Ψ`, `Φ` and the map `F` passed to `simp only` are local.

## P2-6 Duplication probes

`G6bProbe/u1517/DupProbe` (`exact?`, 400k heartbeats; each probe has the use's hypotheses and instance arguments,
G53-01) and `DupProbeLong` (the three timeouts again at 3.2M, 635 s):

- **K2** (control, the averaging step): `exact abs_uexp_sub_le hc h`, the lemma used.
- **D1** `0 ≤ Regev.extractionError P` (`P : LWE.Parameters`): `exact?` fails. No lemma (U1517-F03).
- **D2** `leveledView P χ L μ = levelHybrid P χ L μ L`: fails. No lemma.
- **D4** the uniform-key helper's statement: fails. No lemma.
- **K1** (control, `acceptProb_fst`'s shape), **D3** (two bits, one uniform-key test, `≤ 2·(N·ε)`) and **D5** (the
  `H_0`/`realView` identity): timeouts in `isDefEq`/`whnf` at both limits (K1 also a universe constraint), so
  inconclusive; the worker's P1/P3/P5 behaved the same. The searches in `logs/searches-u1517.txt` decide them (review
  §Duplication).
- rc 1 by design (6 and 4 errors).

## P2-7 Full 6b stack (extra; shared with U18+U19)

- **Head.** `c87eb403` + U14+U16's reviewed head `9852429e` (its `Bootstrap`/`Leveled` blobs equal its delivered
  `src/`; that step gives `TCSlib` `8dc09446`, the U14+U16 review's prospective tree) + `619d2029` + `4672ed30`, each by
  a clean `merge-tree`, committed on no ref: **`6e363a298ff6fe59e861f968d4c54262d96e9f74`**, `TCSlib` tree
  `37ae0f3223db419f636bb2d39484191f698de994` (`logs/stack-head-full.txt`).
- **Build** 02:19:21–02:20:03: **12/12 rc 0, 0 `sorry` warnings**; `check` 1,456 OK; admissions **18 in 8**, the README's "the
  base order's count falls from 42 to 18".
- **Axioms** (`runs/full-axioms`, the four owners of both units): 103 constants, **0 `sorryAx`**; G15, L4, L5 and all
  of U18+U19's targets `[propext, Classical.choice, Quot.sound]`, the helper `[propext, Quot.sound]`. (The 104 of the
  two unit censuses less `levelTerm.congr_simp`, a generated congruence lemma realized on demand.)
- A first attempt at this tree stopped before any Lean start (`replay.sh`'s slot gate aborted under `set -e` when
  `pgrep` found 0 processes); the partial copy was deleted and the gate fixed (`|| true`), then the replay ran
  (`logs/trees.log`).

## P2-8 Lint

`campaign_style_lint.py TCSlib/Cryptography --check8b`: **92 FAIL / 103 WARN over 540 files** at B6, at `619d2029` and
at `67a69bae`; identical FAIL/WARN line sets. The changed INFO lines are the size lines and `LeveledSecurity.lean 681
lines > target 600` (U1517-F05). `style_lint.py` on the owned files: **0 findings** at B6 and at the head.

## P2-9 State after the run

- **Deleted:** `$SP/g6b-u1517-1819/olean-replay-u1517-b6` and `-u1517-stack` (02:04Z), after `check-end` (1,456 OK each)
  and a re-hash of the rebuilt oleans (unchanged).
- **Snapshot #11:** `snapmap.py verify` **0/0/0** mid-run (02:02Z) and at the end (02:21Z).
- **Scratch commits** (on no ref, never pushed): `f4219a24`, `56fe8e9a`, `619d2029` (reproduction), `67a69bae`, the
  full-stack chain ending `6e363a29`.
- **Evidence:** `gsw-6b-u15-u17-u18-u19-final-r1-evidence.zip`, with the raw seal logs and sealed copies.

## What this changes in `review.md`

| Item | Phase 1 | After phase 2 |
|---|---|---|
| C1/C2 build and admissions | worker's sweep (6 modules, root not built) | **reproduced**, with the root, on B6 and stacked; 39 in 14 |
| C5 axioms | worker's census | **reproduced**: 67/67, same sets, 0 `sorryAx` |
| C6 Rule 10 | worker's whole-file seals | **canonical coe-A and B** pass (464; 1,561/1,562); 4 liveness pairs; unfold scan 0 foreign |
| Duplication | static | D1, D2, D4 no lemma; K1/D3/D5 inconclusive, decided by search |
| New findings | U1517-F01–F05 | none |
