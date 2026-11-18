# EF-R2/R3 `ef-r23-regev` · final r1 · phase 2: merged-tree replay on olean snapshot #11

**Verdict: PASS.** The replay ran on the merge of `iO/phase-a-base` with the records tip, which is Lean-equal
to `bff0567b`.
- **Build.** 26/26 modules rc 0, 0 `error:`/`error(`, 0 `sorry`, 0 warnings, including root `TCSlib` and both
  `audits/*/Checks` (closes EFR23-F04 and answers EF-R23-W1).
- **Axioms.** All 80 stored constants of the three new owners are within `propext`, `Classical.choice`,
  `Quot.sound`; the four headline theorems use exactly those three. A `sorry` control is flagged.
- **Seals.** Canonical coe-A seal of the three owners: 0 errors. The delivered coe-A paired controls, re-run:
  ALL_OK.
- **Probes.** The maintainer's own R-P1/R-P2 (the delivered ones are missing, F02): 0 mismatches.
- **LE-coins (F01's fix)** demonstrated on a scratch commit: compiles, axioms standard, coe-A seal 0 errors.
- **Lint** unchanged. **Snapshot #11** rehashes 0/0/0 before, after the build and at the end.

**No landing branch and no PR**: F01 is a major (see `review.md`, *Landing (held)*).

Run on 2026-11-18, 11:17–11:40 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `ef-r23-final-r1-evidence.zip`, beside this file, with `PROVENANCE.txt` and an inner
  `SHA256SUMS` that does not list itself. The zip's SHA-256 is in `evidence-SHA256SUMS`.
- **Lean processes.** One at a time (the recipe's `runner.py`/`runner_full.py` are sequential). S2-A batch D2
  and the EF-H11 review shared the host; the slot count at the start of each phase is in `logs/slot.log`
  (one other `lean` at every phase start; every sample taken during the run showed at most 2 on the host,
  this job's included, within the limit of 3). Only this job's own runs were waited on;
  nothing was killed.
- **Not touched:** snapshot #11 (read and hard-linked only), `$SP/olean-replay-efd1` and its worktrees, other
  agents' replay directories. No `lake build`, no cache get.

## P2-0 Inputs

- **Records tip** at the run: `d1826ce0` (moved from `b7bc1011` during the review by another session).
  `git diff --name-only bff0567b d1826ce0` over `TCSlib`, `TCSlib.lean`, `audits`, the lake files and
  `lean-toolchain` is empty: Lean-equal to snapshot #11's T.
- **Snapshot #11** `$SP/olean-snapshot`: map `olean-snapshot.map-bff0567b.tsv` = `e7bb03b4…867d0` (the
  register's), files manifest `olean-snapshot.files-bff0567b.txt` = `463c8869…`.
- **Recipe tools** `olean-advance-a6d01b1b/tools-used/` as extracted for the EF-D1 review, unmodified:
  `runner.py`, `runner_full.py`, `stateplan.py`, `downorder.py`, `fullorder.py`, `permod.py`, `snapmap.py`,
  `mloverlay.sh`, `mathlibextra.sh`, `seal/review/{mkcollect,mkseals_coe,sealsum}.py`, the archived gate-10
  builders and `NmCollect.template.lean`.
- **New tools** (in the zip's `tools/`): `repro.sh` (phase-1 `git am`), `recount_r10.py` (phase-1 seal and
  control log recount), `recount_ctl.py` (this run's controls), `rule10.sh` (this driver).

## P2-1 Scratch merge and check head (scratch only, never pushed)

- **Merge** in a sparse detached worktree at `5ed465f6`:
  `git -c commit.gpgsign=false merge --no-ff bff0567b`, fixed date `11:00Z`. Clean.
  `45769ce2fe6ad657e9eb31b02044ebb35424e3f8`, **tree `1a55e8aac645cab79de85749a17299e077c8cd62`**, the same
  tree as EF-D1's scratch merge; against `bff0567b` it changes exactly the iO base's 15 Lean paths.
- **Check head:** unsigned cherry-picks of the 3 worker commits:
  `15e18eb89a401de141b36de782ae94dd3cf676aa`, **tree `013ee3de6092eb676f590a6a854861d76ee46fe9`** =
  `git merge-tree --write-tree 324c5de2 bff0567b`. Against the merge: the 6 delivery files, +1472.
- I did not reuse `$SP/olean-replay-efd1`: its root, `SIS.olean` and the two EF-D1 owners belong to EF-D1's
  check head, and a fresh copy of snapshot #11 costs minutes.

## P2-2 Replay (snapshots.md job recipe)

- **Copy and overlay.** `cp -al $SP/olean-snapshot $SP/olean-replay-efr23` (1487 files, all hard links);
  `mloverlay.sh`: 3346 Mathlib symlinks; `mathlibextra.sh`:
  - `NthRootLemmas` rc 0, olean **`c0a9cff0…`** (the recipe's value);
  - `Mathlib/Data/Fin/Tuple/Take` rc 0, olean `d5a54963…` (absent from the shared package build; the PKE
    file imports it, as the worker disclosed; its one import is present). Only in the replay tree.
- **Tree.** `git archive` of the check head (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, lake files,
  `lean-toolchain`; 1622 files), `.lake/packages` symlinked. The 6 delivery sources equal the delivered
  `src/` (`b8245050…`, `6c691b8e…`, `553343e4…`, `4eb20648…`, `f0f062cd…`, `ce8c8141…`).
- **Plan.** `stateplan init` at `bff0567b`: 1456 modules. `downorder.py`: changed 21, down 26. `fullorder.py`:
  1470 (roots `TCSlib` and both `Checks`). `stateplan plan`: **26 to build, 1444 reused**: the 15 iO paths,
  the 6 delivery modules, `Encryption/{Symmetric,PublicKey}`, `Encryption`, root `TCSlib` and the two
  `Checks`. The exact importers of the three changed facades are `Encryption/Symmetric.lean`,
  `Encryption/PublicKey.lean` and `TCSlib.lean`, all in the plan.
- **Build** 11:21–11:25. **26/26 rc 0**; `error:` 0, `error(` 0, the substring "error" 0, `sorry` 0, warnings
  0; `permod.py`: no log/record mismatch. Peak maxrss 4.58 GB (root). The three owners: 3.7 s, 2.3 s, 2.1 s.

## P2-3 Accept (recipe step 5)

- `stateplan update`: 26 modules, none left out. `check` over the full order: **1470/1470, RESULT OK**.
- **Link count 1** for all 26 rebuilt oleans; every other snapshot file is a hard link.
- **Snapshot #11** `snapmap.py verify`: **0/0/0**, 1487 files, no symlinks, before the copy, after the build
  and at the end.

## P2-4 Axioms and probes

All through `runner_full.py`: `lean -DmaxErrors=0`, no `-o`.

- **`AxiomsHead`** (the recipe's axiom probe with the three owners, plus a `sorry` control): rc 0.
  **80 stored constants** (65 declarations, 15 auxiliary):

  | Axiom set | Constants |
  |---|---|
  | `[Classical.choice, Quot.sound, propext]` | 29 |
  | `[Quot.sound, propext]` | 46 |
  | `[propext]` | 5 |

  0 non-standard. `exists_shiftMachine`, `singleMessageSecure_of_dlweAssumption`, `exists_reductionMachine`,
  `singleBitSecure_of_dlweAssumption`: `[Classical.choice, Quot.sound, propext]` (R-P3). The control reports
  `[sorryAx]`, and its warning is the only one. The worker's 62 public constants are a subset.
- **`CollectHead`** (`mkcollect.py` from the recipe template, the three owners): rc 0, 0 errors, 1579 CAT rows;
  stored 48 / 14 / 18.
- **`ToolkitProbe`** (written by the maintainer; `#eval` evidence, not proofs). A first run failed to elaborate
  (a missing `open Turing` in the probe; rc 1, nothing evaluated); the fixed run is rc 0:
  - **R-P1**, canonical context `modContext w q` at the least `w` with `q ≤ 2^w` (`q = 2^w` at `q = 2, 8`),
    `q ∈ {2, 3, 5, 7, 8, 12}`: `addMod` on every residue pair (295 cases), `vecAddModWords` at lengths 0–3
    (all pairs, or 20 × 20 spread samples; 4,062 cases) against `u + v`, `subsetSumModWords` for `m × n`,
    `m ≤ 3`, `n ≤ 2`, up to 12 matrices, every bit vector, two unread extra bits, against `Aᵀ *ᵥ r`, and the
    one-column form against `∑ b i r i` (3,696 cases). **0 mismatches.** Malformed inputs evaluate (total).
  - **R-P2**, toy `n = 1`, `m = 2`, `q = 5`, width 3: `shiftPre ⟨shiftAdvice μ, enc x⟩ = enc (shift μ x)` over
    all 625 challenges × 4 messages (2,500), `encryptPre ⟨encryptAdvice μ, ⟨enc pk, r ++ [1,1,0]⟩⟩ =
    encodeView (view μ pk r)` over 625 keys × 2 bits × 4 subsets (5,000). **0 mismatches.** Control: the
    advice of the wrong bit gives a different string (`equal=false`). The machines themselves are not
    evaluated (they come from an existential; the Lean theorem is the evidence).

## P2-5 Rule 10

- **Canonical coe-A seal** (`mkseals_coe.py`, A variant, unmodified; `SEAL_CHUNK=1000`), on the collector log:

  | Owner | Requests | Terms | Excluded terms | Stored | Result |
  |---|---|---|---|---|---|
  | `Encoding.ModularArithmetic` | 1,011 | 16 | 1 | 48 | rc 0, 0 errors; parts 1000 + 11 verified |
  | `Encryption.Symmetric.Regev.Asymptotic` | 1,133 | 38 | 13 | 14 | rc 0, 0 errors; 1000 + 133 verified |
  | `Encryption.PublicKey.Regev.Asymptotic` | 1,147 | 43 | 14 | 18 | rc 0, 0 errors; 1000 + 147 verified |

  Every part has its install and `G06-SEAL-END` records with `requested = verified`. The worker's coe-A
  counts for the same owners are 1011 / 1131 / 1145: equal for the toolkit, and 2 fewer for each scheme
  owner (a slightly different enumeration of the same closure; this seal is the stricter one).
- **Paired controls.** The delivered coe-A control files (S sealed, U unsealed; 3 hosts) re-run on this tree,
  recounted per `theorem ctl…` span (`recount_ctl.py`): sealed hosts NEG/POS 6/6, 9/9, 10/10 with exactly one
  error per NEG and none per POS; unsealed 0 errors; 0 stray. **ALL_OK.** All 13 new definitions are covered.
- **Explicit-unfold scan**: not re-run; the delivered scan (363 items, 0 foreign) is over the same bytes.

## P2-6 LE-coins demonstration (EFR23-F01's fix)

- A second sparse worktree at the check head; scratch commit `9012382292416e82ff40267f96523e4e67296230`
  (unsigned, never pushed), proof-only, `+6/−5` in `PublicKey/Regev/Asymptotic.lean` (max width 100):

  ```diff
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
  plus the proof sketch's step 3 now names `EnsembleLemmas.coinsEquiv`. Full patch: `le-coins.patch`.
- **Compile** of the edited owner (no `-o`): rc 0, 0 errors. **Axioms** (`PKEFixedAx`, the edited file plus
  two `#print axioms`): both PKE theorems `[propext, Classical.choice, Quot.sound]`.
- **Its own coe-A seal** (1,147 requests, with `EnsembleLemmas.coinsEquiv` itself among the sealed names):
  rc 0, 0 errors, `requested = verified` in both parts. So the edit needs no unfolding of the helper.

## P2-7 Lint

- `campaign_style_lint.py TCSlib/Cryptography --check8b` on exports of the scratch merge and the check head:
  **92 FAIL / 103 WARN over 551 files** and **92 / 103 over 554**. The line sets are identical: no new FAIL or
  WARN, none removed.
- `style_lint.py` on the six files: rc 0, **0 findings**.

## P2-8 State after the run

- **Kept** for the landing re-run and the gate: `$SP/olean-replay-efr23` (1487 + 26 rebuilt oleans, two
  Mathlib extras, 3346 symlinks); worktrees `$SP/efr23/p1/amwt` (`324c5de2`, the reproduced worker head),
  `$SP/efr23/p2/mergewt` (scratch `45769ce2`, `15e18eb8`) and `$SP/efr23/p2/demowt` (scratch `90123822`). None
  is pushed.
- **Raw seal sources are not in the zip** (regenerable by `mkseals_coe.py` from the collector log, which is in
  the zip); their SHA-256 are in `rule10/omitted-SHA256SUMS`. The raw seal and control logs are included.
