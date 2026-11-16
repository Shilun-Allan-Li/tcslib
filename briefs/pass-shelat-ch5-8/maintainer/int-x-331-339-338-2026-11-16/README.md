# Integration cross-build: records tip × #331 × #339 × #338 (2026-11-16)

**Result: X builds cleanly.** 715/715 rebuilt modules have rc 0 with 0 errors (both `error:` and `error(`), through root
`TCSlib` and both `audits/*/Checks`. The state check and the whole-tree check are OK. The axioms hold as required, the
admissions are 229 → 198 as expected, and #327/#324 touch no Rule 10 owner's closure. This meets the integration condition
of #331, #339 and #338.

Maintainer job. Detailed provenance: `PROVENANCE.txt` inside `int-x-331-339-338-evidence.zip`.

## Inputs

| Item | Commit | Notes |
|---|---|---|
| Records tip T | `76a3fba9c4bfe732d8f91980d856632a118c4561` | Contains #327/#324 (`201bf57a941131d1737295089ffd7477e1d7f7b9`). Its `TCSlib`, `TCSlib.lean`, `audits`, `scripts` and lake files are the same objects as int-x-327-324-333's cross-built tree `199ea4c629e2ddfac4c85991763c096b9b9ff41f`. |
| #331 (pairing statements, Gate 40 CLEAR) | `9e7a96481785d6cac4dea3b2e990c49ac278b060` | Merge base `673a27158338437896c624df32bf5421c6ba45cf`; 13 files. |
| #339 (`gsw-core`, Gate 43 CLEAR) | `839f36cca9b4af0570c014f03f19858d0a03cbfb` | Merge base `347665bd741d367c4d2057f7d61866ff1d91c356`; 5 files. |
| #338 (`gsw-security`, Gate 43 CLEAR) | `d45d3682089cb6fd04f4d075f48a464fefaa143c` | Merge base `15d8f01a42f23aa17d8fd305c7e5edde9b602da4`; 2 files. |

The three heads equal `origin refs/pull/N/head`. During the job the records branch gained 21 records-only commits
(`76a3fba9` → `ca5c1372`); none of them changes code paths.

## Method

The method is int-x-327-324-333's, and its tools are reused unmodified.
- Tools: its `tools-used/` plus int-331-tip's `fullorder.py`.
- New tools: `restore_x3.sh`, which is `restore_x.sh` with only the order path changed; `baseagree.py`; `axsum.py`.

Steps:
1. **Preflight.** The `$SP/dl-oleans` snapshot is 1230 files with SHA-256
   `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, the required value.
2. **Merges.** In a new sparse worktree (`TCSlib/`, `TCSlib.lean`, `audits/`, `scripts/`, lake files), I created the local
   branch `int/x-331-339-338` at T and ran `git merge --no-ff` three times. Each merge was clean. The commits are unsigned,
   dated 2026-11-16T00:00:00Z and never pushed.
3. **Build.** I built incrementally from the snapshot base `eff2dcd0` by import-closure keys (`stateplan.py`).
   - Order: the closure of root `TCSlib`, `audits/garg-ch1-3/Checks` and `audits/pass-shelat/Checks` at X, 1353 modules. As
     a set it equals `downorder.py`'s order against `eff2dcd0`.
   - Plan: 715 modules to build (561 snapshot oleans plus 154 new) and 638 reused. The queue equals the down set.
   - The 561 snapshot oleans were backed up and hash-verified.
   - I added the Mathlib overlay and built NthRootLemmas (`c0a9cff0…`, as before).
   - Modules were built one at a time through `scripts/lean_check_tree.sh` (`runner.py`), followed by the state update and
     check, the whole-tree check, the census, and the reference and log comparisons.
4. **Axioms.** I ran one probe at X with `runner_full.py` (`lean -DmaxErrors=0`, no `-o`). It contains
   int-stmt-331-333's DepTrace `#admitted`, unmodified, applied to 54 names, plus a per-module closure census.
5. **Restore.** I restored the backup, deleted the new oleans and the overlay, and ran `restoreplan --delete`. Then I took a
   fresh snapshot and ran a second, independent check.

## Merges

| | Commit | Tree |
|---|---|---|
| A = T × #331 | `8a65609bc3e16b02350b3bdc87dbc4817ac757fd` | `5e980ff06505b8d97215cde35c81706f6a5a3542` |
| B = A × #339 | `396c90d2aac645da555ee95becc37af8a5345040` | `8a23f17479a0d44697ef93c3e890108c9e7b10d5` |
| X = B × #338 | `7ab4196ceb257cfe7d619f61c6f167b4ea537d2c` | `7d47e675512c478ad840f9bc85ad352800193674` |

The local branch `int/x-331-339-338` is kept at X.

- **Diff check.** `git diff T X -- TCSlib TCSlib.lean audits` has 20 files. It equals exactly the union of the three PRs'
  diffs against their merge bases (13 + 5 + 2 files, pairwise disjoint):
  - paths, statuses, modes and new blobs all match;
  - the old blobs at T equal those at each merge base;
  - every file of X is blob-equal to its PR head.

  Nothing outside `TCSlib/`, `TCSlib.lean` and `audits/` changes.
- **Reverse order.** T × #338 × #339 × #331, done with `git merge-tree` and unreferenced scratch commits, is clean at every
  step and gives tree `7d47e675…`. That is the same tree as X.
- **Name clash.** #331 adds 144 public names; #339 and #338 add none. Every pairwise intersection is empty. The only
  duplicate names are the same 12 pre-existing `GraphTheory/Core` duplicates at T and X.

## Build of X

- **Runner:** rc 0. **715/715 rc 0; `error:` 0; `error(` 0; the substring "error" 0.** Every log hash equals its record.
- **Totals:** 60 sorry warnings and 421 warnings; 6685 s of module time (17:47–19:38 UTC); maximum RSS 4.49 GB.
- **The 20 PR modules:** all rc 0 with 0 errors.
  - #331: `Pairing/Assumptions` 1 sorry (T1), `BonehBoyenSecurity` 2 (T2, T3), `BonehBoyenMachine` 1 (T4). The other 10
    modules, including root `TCSlib` and the facades, have 0 sorry and 0 warnings.
  - #339 and #338: 0 sorry and 0 warnings in all seven files.
- **`audits/*/Checks`:** rc 0, 0 warnings.
- **State check** (`stateplan check` over the 1353-module order): **RESULT OK**.
- **Whole-tree check** (`treecheck_ml`): every module is rc 0 at the X source, every olean equals its record, and there are
  no missing or stray oleans and no empty directories: **RESULT OK**. The tree holds 4731 files, none of them zero bytes.
- **References:**
  - All 715 rebuilt oleans are byte-identical, in source and olean, to a record from an earlier committed build: X1,
    int-331-tip, gate40-seals-merged, gsw-core-r1 or gsw-security-r1. There are 0 same-source, different-olean cases.
  - `logcheck`: 715 OK-REF.

## Axioms at X

The probe ran with rc 0, 0 errors and 0 warnings. `axsum.py` gives **RESULT OK**.
- **GSW.** All 35 targets (29 from #339, 6 from #338) depend on `[propext, Classical.choice, Quot.sound]`, and none has a
  direct `sorryAx` user in its closure. For example, `decrypt_keygen_eval` has closure 7629. #338's six closures, 2444 /
  19103 / 9349 / 19199 / 19214 / 19231, equal the gsw-security review's.
- **Pairing, standard.**
  - `joux_correct`, `jouxKeyIndist_of_dbdhAssumption`, `bb1_correct`, `bb1_encPP_inj`, `bb1_encSK_inj` and `bb1_encCT_inj`
    are standard with 0 `sorryAx` users. Their closures (6837 / 10289 / 8663 / 1530 / 1526 / 1531) equal int-331-tip's.
  - The other 8 theorems in `KeyExchange/Joux` are standard too. `jouxMsg_eq` and `jouxKey_eq_pow` use only
    `[propext, Quot.sound]`.
- **T1–T4.** `bdhAssumption_of_dbdhAssumption`, `bb1_sim_real`, `bb1_sim_random` and `exists_bb1_distinguisher` each depend
  on `[propext, sorryAx, Classical.choice, Quot.sound]`. Each is the **only** direct `sorryAx` user in its own closure.
- **`bb1_sidSecure`.** It depends on `[propext, sorryAx, Classical.choice, Quot.sound]`, and its closure's direct `sorryAx`
  users are **exactly T2, T3 and T4**.
- **Module census.**
  - The 7 GSW owner modules have no `sorryAx` user anywhere in their closures.
  - Among #331's 8 non-facade modules, only `Assumptions` [T1], `BonehBoyenMachine` [T4] and `BonehBoyenSecurity` [T2, T3, T4]
    reach one.

## Admissions (int-x census method, `tipcensus.py`)

- **T `76a3fba9`: 229**, as expected, because T's code equals X1's.
- **X `7ab4196c`: 198 = 229 + 4 − 35**, which is the expected value.
  - #331 adds 4: `Assumptions` 1 (T1), `BonehBoyenSecurity` 2 (T2, T3) and `BonehBoyenMachine` 1 (T4).
  - #339 removes 29: `Gadget` 5, `Noise` 12, `Scheme` 6, `Symmetric` 2 and `Eval` 4.
  - #338 removes 6: `Security` 4 and `Hashing/SIS/Columns` 2.

  No other module changes. No set disagrees. The same 34 modules outside root `TCSlib`'s closure have no record.

## Seal relevance

`git diff d98cc4901 201bf57a9 --name-only` gives 57 `.lean` files: #327's SequentialZK, #324's ComposeSecurity and
`ZeroKnowledge/Defs`.

I computed the import closure at X of each of the 17 owners:
- the 10 Rule 10 owners of #331: `Pairing/{Group,Assumptions,Operations}`, `KeyExchange/Joux`,
  `AdvancedEncryption/IdentityBased/{Defs,BonehBoyen,BonehBoyenMachine,BonehBoyenSecurity}`, and the `IdentityBased` and
  `AdvancedEncryption` facades;
- the 7 GSW owners: `GSW/{Gadget,Noise,Scheme,Symmetric,Eval,Security}` and `Hashing/SIS/Columns`.

**None of them contains any of the 57 modules.** So the earlier seal evidence carries over unchanged with respect to
#327/#324:
- #331: gate40-seals-merged;
- #339: gsw-core-r1;
- #338: gsw-security-r1.

No seals were run.

For information only, since this is not about #327/#324: compared with each PR's own head, the owners' closures at X differ
only because of the sibling PRs in this integration.
- The `AdvancedEncryption` facade gains `Pseudorandom/Indistinguishability` through #338's import (106 → 107 modules). It
  also sees the seven GSW and Columns files at their filled versions.
- The `GSW/Security` owner sees `Gadget`, `Noise` and `Scheme` at #339's versions.

The other 15 owners have the same module sets and the same sources as at their PR heads.

## Restore

`$SP/dl-oleans` is back to snapshot `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`:
- 0 backup hash failures; 561 oleans restored; 154 new oleans and the Mathlib overlay deleted;
- `restoreplan --delete`: extra 0, changed 0, missing 0;
- **SNAPSHOT EQUAL**, with 1230 files and 0 empty directories;
- a fresh recheck snapshot is also equal, and `restoreplan` without `--delete` again gives 0 / 0 / 0.

I then removed the backup, the probe sources and the scratch worktree. The branch is kept.

## Anomalies

1. **First probe attempt stopped.** It used a per-constant `collectAxioms` census and was stopped by its own 25-minute
   timeout, leaving no record.
2. **Second probe attempt had a parse error.** It returned rc 1 from one error in my own probe source: a doc comment placed
   before `open … in run_cmd`. Its result lines are identical to the reported third run. Both attempts are kept in the zip
   with explanations. Neither wrote anything to the olean tree.
3. **NthRootLemmas first call.** The first `mathlibextra.sh` call was given a relative log path and ran nothing.

## Files

- `int-x-331-339-338-evidence.zip`, SHA-256 `e6cd13e88b49649474548454a5de31affbc641dc3889f3617bd2a4587947e11d`. It contains
  932 files plus its own `SHA256SUMS` (SHA-256 `73ae692934520c849097e567982444f87366cf4e45da139483df7b744984d7cd`), under
  `int-x-331-339-338/`:
  - `PROVENANCE.txt`;
  - `landing/` and `checks/`;
  - `order-x/`, `order-tip/`, `state/` and `plan-x/`;
  - `tree/` and `build-mathlib-extra/`;
  - `build-x/`, with every module log;
  - `records/`, `tree-final/` and `refs/`;
  - `admissions/` and `axioms/`;
  - `seal-relevance/` and `restore/`;
  - `tools-used/` and the run scripts.
- `SHA256SUMS` covers the files of this directory.
