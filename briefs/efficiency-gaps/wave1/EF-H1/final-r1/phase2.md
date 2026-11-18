# EF-H1 `ef-h1-arith` · final r1 · phase 2: merged-tree replay on olean snapshot #11

**Verdict: PASS, for both runs.** Each run replayed on a copy of snapshot #11 over a scratch stack on
`bff0567b`, which is Lean-equal to the records tip.

- **Run A, the series alone** (5 commits; the head's tree equals phase 1's `merge-tree` prediction).
  - **Build.** 6/6 modules rc 0, with 0 `error:`/`error(` and 0 `sorry`. These include the root `TCSlib`
    and `audits/pass-shelat/Checks`, which closes EFH1-I6 (W2).
  - **Axioms.** All 62 stored constants of the three new owners are within `propext`,
    `Classical.choice` and `Quot.sound`.
  - **Seals.** Canonical coe-A seal: 0 errors on all three owners. The delivered paired controls give
    exactly NEG1–NEG4.
  - **Probes.** H1-P1's output is byte-identical to the delivery's. The smoke test fails only on the
    overlay's names, which confirms the series alone does not discharge `ArithmeticFP`.
- **Run B, series plus overlay** (7 commits; the tree again equals the prediction).
  - **Build.** All **76** modules downstream of the 7 changed files, including the root and both
    `audits/*/Checks`: rc 0, with 0 errors. The only `sorry` and warnings are pre-existing ones in
    untouched files. **This closes EFH1-F01 and EFH1-F02.**
  - **Axioms.** All 75 constants, plus the 9 owner-file readers, are standard.
  - **Smoke test (H1-P2).** It passes, with output identical to the delivered log.
  - **Seals and controls.** Canonical coe-A seal: 0 errors. The new controls show `mulStr_eq`,
    `mem_PRIMESBin` and `mem_PRIMES` passing sealed, while the body reads fail.
- **I2 closed.** `extEuclidCalls` and `extEuclid` are `irreducible`.
- **Lint.** Unchanged in both runs: 92 FAIL / 103 WARN, identical line sets.
- **Snapshot #11** rehashes 0/0/0 at every check.

Nothing was committed, pushed or landed. Landing and the overlay wait on EF-W1-R.

Run on 2026-11-18, 11:42–12:17 UTC, as the review's *Phase 2 plan* describes and the coordinator
dispatched. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

- **Evidence:** `ef-h1-final-r1-evidence.zip`, beside this file. It holds `PROVENANCE.txt` and an inner
  `SHA256SUMS` that does not list itself. The zip's own SHA-256 is in `evidence-SHA256SUMS`.
- **Lean processes.** This job ran **one Lean process at a time**. Its driver `runq.sh` (in the zip)
  runs each module through the recipe's `runner.py`/`runner_full.py`, and before **each** Lean start
  it checks `pgrep -fc "bin/lean "` ≤ 2 and at least 2 GB free disk. Every start, with the slot count
  and free disk, is in `slot.log`.
  - The host never had more than 2 Lean processes at once: this job's and S2-A D2's seal runs.
  - The slot check never had to wait.
- **No `lake build`, no cache get, no branch, no PR, no push.** Nothing was committed.
- **Not touched:** the snapshot (read and hard-linked only), `$SP/olean-snapshot-10`, and the other
  `olean-replay-*` directories. Only this job's own PIDs were waited on, and none was killed.
- **Disk.** 3.6 GB was free at the start; the lowest reading was 3,430 MB at a Lean start. As instructed, run A's
  olean tree and export were deleted once their results were recorded, before run B started.

## P2-0 Inputs

- **Records tip.** `origin/cryptography/pass-shelat-ch2-4` = `2b42bf53b724899e6c856ac5cc9edec9e09e4d65`.
  `git diff --name-only bff0567b 2b42bf53` over `TCSlib`, `TCSlib.lean`, `audits`, the lake files and
  `lean-toolchain` is empty, so the tip is Lean-equal to snapshot #11's T.
- **Snapshot #11** is `$SP/olean-snapshot`.
  - Map `olean-snapshot.map-bff0567b.tsv` = `e7bb03b4…867d0`, the register's value.
  - Files manifest `olean-snapshot.files-bff0567b.txt` = `463c8869…`.
  - `snapmap.py verify` before the copy: **0/0/0**, 1487 files, RESULT OK.
- **Recipe tools.** `olean-advance-a6d01b1b/tools-used/` was extracted fresh from
  `olean-rebase-evidence.zip` (`b662b7da…`). It is byte-identical to the copy EF-D1 used (`diff -rq`
  empty). The tools were used unmodified: `runner.py`, `runner_full.py`, `stateplan.py`, `downorder.py`,
  `fullorder.py`, `permod.py`, `snapmap.py`, `mloverlay.sh`, `mathlibextra.sh`, `seal/review/{mkcollect,
  mkseals_coe,sealsum}.py` and the archived gate-10 builders.
- **New tools** (in the zip's `tools/`):
  - `runq.sh`, the per-module slot and disk check around the recipe runners;
  - `rule10.sh`, the probe and seal driver.

## P2-1 Scratch stacks (scratch only, never pushed)

A sparse detached worktree `$SP/efh1/p2/stackwt` at `bff0567b`. REC `cf6a2266` is an ancestor of
`bff0567b`, so the stacks are plain cherry-picks, unsigned, with a fixed committer date of `12:00Z`.

| Head | Commit | Tree | Expected (phase 1 `merge-tree`) |
|---|---|---|---|
| **A** (series, 5 commits) | `7c2400d6722f7954bbe65b965cb69b3e5efbbb06` | `16371c0ea7693881d33d20b15996cf66214aa717` | `16371c0e…` **equal** |
| **B** (A + the 2 overlay commits) | `a3d61cadd3e0e40436b387452e477420f319b7da` | `050a20b11c84c9380ff1650aeb80f51ea02debb6` | `050a20b1…` **equal** |

- Against `bff0567b`, A changes exactly the 4 delivery files (+840).
- B also changes `Candidates/Arithmetic.lean` and `Complexity/Randomized/Primality{,Math}.lean`: 7 paths
  in all.
- So both results apply to the delivery's merge with the records tip.

## P2-2 Run A: the series alone

- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-efh1`: 1487 files, all hard links.
  - `mloverlay.sh` made 3346 Mathlib symlinks.
  - `mathlibextra.sh` built `NthRootLemmas` with rc 0; its olean is **`c0a9cff0…`**.
- **Tree.** `git archive` of head A (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake files,
  `lean-toolchain`), with `.lake/packages` symlinked.
- **Plan.**
  - `stateplan init` at `bff0567b`: 1456 modules.
  - `downorder.py`: changed 4, down 6.
  - `fullorder.py`: 1459, with roots `TCSlib` and both `Checks`.
  - `stateplan plan`: **6 to build, 1453 reused**, exactly the review's static prediction. The 6 are
    `ArithmeticDischarge`, `ExtendedEuclidMachine`, `PrimesInP`, the facade `Candidates`, the root
    `TCSlib` and `audits/pass-shelat/Checks`.
- **Build.** 11:44:21–11:46:51.
  - **6/6 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, `sorry` 0, warnings 0 (`permod.py`;
    no log/record mismatch).
  - **Sources bound.** Every record's source SHA-256 equals `git show 7c2400d6:<path>`. The four delivery
    files equal the worker's `build/summary.txt` hashes (`9283869d…`, `8c3e0ff1…`, `51c49532…`,
    `1b38a302…`).
  - Times: the three new modules took 1.9–2.3 s each, the root 3.3 s, and `audits/pass-shelat/Checks`
    118 s. Peak maxrss was 4.54 GB (root).
- **This closes EFH1-I6 (W2).** The root `TCSlib` elaborates with the series, on snapshot #11's PFR
  oleans.
- **Accept.**
  - `stateplan update`: 6 modules, none left out.
  - `check` over the full order: **1459/1459, RESULT OK**.
  - **Link count 1** for all 6 rebuilt oleans. Exactly 6 non-Mathlib oleans in the tree have link
    count 1; their hashes are in `runA/rebuilt-oleans.sha256`.
  - `snapmap.py verify`: **0/0/0**.
- **Probes** (through `runner_full.py`: `lean -DmaxErrors=0`, no `-o`):

  | Probe | Result |
  |---|---|
  | **`Axioms`** (`AxiomProbe.r2` form; the 3 new owners; `sorry` control) | rc 0. **62 stored constants:** the worker's 50 named declarations (all present), 10 `_proof_N` auxiliaries, and the generated `xgcdInvWord.eq_1`, `xgcdLoopMeasure.eq_1`. Axiom sets: `[Classical.choice, Quot.sound, propext]` 33; `[Quot.sound, propext]` 27; `[]` 2. **0 non-standard.** The control reports `[sorryAx]`, and its warning is the only one. |
  | **`Smoke`** (the delivered `H1P2.lean`, unchanged) | rc 1, **19 errors, every one an unknown constant of an overlay-only name**: `ArithmeticFP.ofPrimesInP` (8), `arithmeticFP_iff_primesInP` (2), the seven `polyTimeComputable_{mul,add,sub,divMod,modExp,le,xgcd}Str`, `polyTimeComputable_primeStr_of_primesInP`, `primesInP_of_polyTimeComputable_primeStr` and `primesInP_iff_polyTimeComputable_primeBit`. `#print axioms polyTimeComputable_sizeStr` succeeds. **This shows the series alone does not discharge `ArithmeticFP`**, as the review states. |
  | **`H1P1`** (the delivered probe, unchanged) | rc 0, 0 errors. **Its output is byte-identical to the delivered `probes/H1P1.log`.** This includes the 144-row `xgcd` table and the two kernel `decide` checks. |
  | **`Ctl_sealed` / `Ctl_unsealed`** (the delivered control files, unchanged) | Sealed: exactly 4 errors, at lines 8, 15, 20 and 24, which are NEG1–NEG4. POS1–POS4 (lines 11, 18, 21, 26) pass. Unsealed: 0 errors. **ALL_OK.** |
  | **`I2_sealed` / `I2_unsealed`** (new, EFH1-I2) | With `xgcdLoopStep` and `xgcdInvWord` locally irreducible: exactly 2 errors, at line 14 (NEG5, the `rfl` read of `xgcdLoopStep`) and line 28 (NEG6, the `rfl` read of `xgcdInvWord`). POS5 (`xgcdLoopStep_eq`) and POS6 (`xgcdInvWord_spec`) pass. Unsealed: 0 errors. |
  | **`I2_reducibility`** (new, EFH1-I2) | `extEuclidCalls` and `extEuclid` are **`Lean.ReducibilityStatus.irreducible`**. `example : extEuclidCalls 3 2 = 1 := rfl` fails, its only error (line 12). So the canonical seal list rightly omits them: nothing can read their bodies definitionally. **This closes I2.** |

- **Canonical coe-A seal** (`mkcollect.py`, then `mkseals_coe.py` A variant with `SEAL_CHUNK=1000` as in
  the EF-D1 precedent, then `sealsum.py`). The `Collect` probe: rc 0, 0 errors.

  | Owner | Requests | Terms | Excluded terms | Stored | Parts | Result |
  |---|---|---|---|---|---|---|
  | `ArithmeticDischarge` | 1,021 | 24 | 1 | 17 | 1000 + 21 | **rc 0, 0 errors** (122 s) |
  | `ExtendedEuclidMachine` | 1,028 | 17 | 0 | 41 | 1000 + 28 | **rc 0, 0 errors** (106 s) |
  | `PrimesInP` | 2,912 | 11 | 1 | 4 | 1000 + 1000 + 912 | **rc 0, 0 errors** (290 s) |

  - Every part has install and end records, and every end record gives `verified = requested`.
  - The EOF verification probes: 3/3 pass.
  - The request counts are higher than the worker's (443, 444, 1,111). As in EF-D1, the recipe
    collector requests every ordinary TCSlib definition of the owner's transitive closure, matchers
    included, so this seal is the stricter of the two.
- **Lint** (static; `campaign_style_lint.py TCSlib/Cryptography --check8b` on exports):
  - `bff0567b`: **92 FAIL / 103 WARN over 540 files**;
  - head A: **92 / 103 over 543**;
  - the FAIL/WARN line sets are identical (diff empty);
  - `style_lint.py` on the 4 files: **0 findings**.
- **Cleanup.** After the results were staged in the evidence (`runA/`), `$SP/olean-replay-efh1` and the
  export were deleted. `snapmap.py verify` after the deletion: **0/0/0**.

## P2-3 Run B: series plus overlay

- **Copy and overlay.**
  - A fresh `cp -al $SP/olean-snapshot $SP/olean-replay-efh1`: 1487 files, all hard links.
  - `mloverlay.sh`: 3346 links.
  - `NthRootLemmas` rebuilt with rc 0: **`c0a9cff0…`**.
- **Tree.** `git archive` of head B, as for A.
- **Plan.**
  - `stateplan init` at `bff0567b`: 1456 modules.
  - `downorder.py`: changed 7, down 76.
  - `fullorder.py`: 1459.
  - `stateplan plan`: **76 to build, 1383 reused**, exactly the review's static count. The queue equals
    `down.txt`, and includes the root `TCSlib`, `audits/garg-ch1-3/Checks` and
    `audits/pass-shelat/Checks`.
- **Build.** 11:59:24–12:06:03.
  - **76/76 rc 0.** `error:` 0, `error(` 0, the substring "error" 0 (`permod.py`; no log/record
    mismatch).
  - **Sources bound.** Every record's source SHA-256 equals `git show a3d61cad:<path>`. The 7 changed
    modules equal the worker's overlay `build/summary.txt`: `PrimalityMath` `6caa9771…`, `Primality`
    `e5b9b31e…`, `Arithmetic` `499fbb3f…`, `ArithmeticDischarge` `4b353a65…`, `ExtendedEuclidMachine`
    `b6629d3b…`, `PrimesInP` `3fc7f07e…` and the facade `1b38a302…`.
  - **The 13 warnings are all pre-existing**, all in untouched files with byte-equal sources at
    `bff0567b`:
    - `GSW/PolyRatio` (3) and `GSW/Asymptotic` (2): `declaration uses 'sorry'`, the #377 statement
      `sorry`s present at `bff0567b`. So the 5 `sorry` warnings are none of this job's.
    - `Candidates/DDH` (3): unused section variables.
    - `Pseudorandom/Generators/LWE/Flat` (5): definition linter.
  - **Every importer of the three frozen files is covered:** `Factoring`, `RSA`, `Rabin`, `DDH`,
    `Concrete`, `DiscreteLog{,Hardcore}`, `ElGamal`, the DL hash (`Hashing/FromDiscreteLog/*`), the
    BB1 (Boneh–Boyen) IBE modules, `Randomized/{Matching,ZeroP,ZeroPPIT}`, the facades, the root and
    both `Checks`.
  - Total 391 s. The slowest were `audits/pass-shelat/Checks` (114 s) and the BB1 `Handler` (27 s).
    Peak maxrss was 4.58 GB (root).
  - **This closes EFH1-F01** (the overlay's evidence now binds every source) **and EFH1-F02** (the
    full downstream).
- **Accept.**
  - `stateplan update`: 76 modules, none left out.
  - `check`: **1459/1459, RESULT OK**.
  - **Link count 1** for all 76. Exactly 76 non-Mathlib oleans in the tree have link count 1
    (`runB/rebuilt-oleans.sha256`).
  - `snapmap.py verify`: **0/0/0**.
- **Probes.**

  | Probe | Result |
  |---|---|
  | **`Axioms`** (3 new owners + the 9 owner-file readers by name; `sorry` control) | rc 0. **75 stored constants:** run A's 62, plus the overlay's 13 targets. Diffing the named rows against the worker's 50 and the overlay's 13 shows **all 63 present, no extras**. Sets: `[Classical.choice, Quot.sound, propext]` 46; `[Quot.sound, propext]` 27; `[]` 2. **Readers:** the 7 `*Str_eq` and both `mem_PRIMES{,Bin}` are present, with `[propext]` ×7, `[Quot.sound, propext]` (`xgcdStr_eq`) and `[]` (`leStr_eq`). **0 non-standard.** The control reports `[sorryAx]`. |
  | **`Smoke`** (the delivered `H1P2.lean`, unchanged) | **rc 0, 0 errors.** `ofPrimesInP h` is accepted as `H` by `factoringCollection_oneWay`, `rsaCollection_oneWay`, `dlCollection_oneWay` and `polyTimeComputable_expEval`, and `arithmeticFP_iff_primesInP` elaborates. The 13 `#print axioms` lines are all `[propext, Classical.choice, Quot.sound]`. **The output is identical to the delivered `scope-request/H1P2.log`.** |
  | **`H1P1`** | rc 0; output byte-identical to the delivered log. |
  | **`Ctl_sealed` / `Ctl_unsealed`** (the delivered pairs + POS4b + NEG/POS7–8; `PRIMESBin` and `PRIMES` added to the seal) | Sealed: **exactly 6 errors**, at lines 8, 15, 20, 24 (NEG1–NEG4), 32 (NEG7, `Iff.rfl` on `PRIMESBin`) and 35 (NEG8, `Iff.rfl` on `PRIMES`). POS1–POS4, **POS4b (`mulStr_eq z` passes with `mulStr` sealed)**, POS7 (`mem_PRIMESBin`) and POS8 (`mem_PRIMES`) pass. Unsealed: 0 errors. So the overlay's readers are exactly what makes the field theorems and the bridge go through under the seal. |
  | **`I2_sealed` / `I2_unsealed`, `I2_reducibility`** | As in run A: NEG5 and NEG6 only, POS5/POS6 pass; both `irreducible`; the one expected `rfl` failure. |

- **Canonical coe-A seal**, the same recipe as A:

  | Owner | Requests | Terms | Excluded terms | Stored | Parts | Result |
  |---|---|---|---|---|---|---|
  | `ArithmeticDischarge` | 1,021 | 24 | 1 | 23 | 1000 + 21 | **rc 0, 0 errors** (118 s) |
  | `ExtendedEuclidMachine` | 1,028 | 17 | 0 | 42 | 1000 + 28 | **rc 0, 0 errors** (117 s) |
  | `PrimesInP` | 2,912 | 13 | 1 | 10 | 1000 + 1000 + 912 | **rc 0, 0 errors** (287 s) |

  - Every part verifies `verified = requested`, and the 3/3 EOF probes pass.
  - The request sets are the same size as A's, because the overlay adds theorems only and no definition.
  - The stored counts grow by the overlay's 6, 1 and 6 declarations.
- **Lint.** `campaign_style_lint --check8b`: head B gives **92 / 103 over 543 files**, line sets equal
  to `bff0567b`'s. `style_lint.py` on the 7 changed files (including `Arithmetic.lean` and both
  `Primality*`): **0 findings**. The overlay's double blank lines (EFH1-F06) are not flagged.

## P2-4 State after the run

- **Kept:**
  - `$SP/olean-replay-efh1`: **run B's** accepted tree (1487 hard links + 76 rebuilt oleans, about
    41 MB, the `NthRootLemmas` olean and 3346 Mathlib symlinks), for the gate. Under EF-W1-R (A),
    head B, plus landing edits, is the likely landing content. Delete it if the ruling goes otherwise.
  - The stack worktree `$SP/efh1/p2/stackwt`, at head B, with its probe directory.
  - The scratch commits `7c2400d6` and `a3d61cad`, never pushed.
- **Deleted:** run A's olean tree, both exports (`treeA`, `treeB`) and the lint baseline export of `bff0567b`.
- **Lowest free disk** at a Lean start was 3,430 MB.
- **Snapshot #11**: `snapmap.py verify` gives **0/0/0** at the end (12:17Z).

## What this changes in `review.md`

| Item | Phase 1 | After phase 2 |
|---|---|---|
| EFH1-F01 (the overlay's pool log misdescribed) | open | **closed**: every overlay module rebuilt from bound sources, rc 0 |
| EFH1-F02 (the overlay's downstream partial) | open | **closed**: 76/76 downstream modules rc 0 |
| EFH1-I2 (`extEuclidCalls` not sealed; one control per owner) | information | **closed**: both are `irreducible`; NEG/POS5–6 behave |
| EFH1-I6 / W2 (root not elaborated) | information | **closed**: root `TCSlib` rc 0 in both runs |
| EFH1-F03–F06 | minor | **unchanged** (disclosure, wording, form and landing-edit items; no Lean finding) |
| The worker's C1, C5, C6, C8, H1-P1, H1-P2 | recounted statically | **reproduced** by an independent replay |

Run B also settles one point of EF-W1-R mechanically: with the nine one-line readers in their owner
files, the seven field theorems, the `PRIMESBin` bridge, `ofPrimesInP` and the iff all compile, and no
existing module is affected.
