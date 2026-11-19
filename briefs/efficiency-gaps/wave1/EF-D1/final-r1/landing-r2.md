# EF-D1 · final r1 · landing r2: promotion into #384's `Contract.lean`, readers on #378, SR1 and re-point on #387

**Status: LANDED (round r2b), pushed 2026-11-19 as fast-forwards with no force:**

| Branch | Old head | New head |
|---|---|---|
| `foundations/coin-sampling` (#378) | `51dc7672` | `3473adda66d9c61c51ba640ed4c701e5cde0b6b1` |
| `foundations/coin-contract` (#384) | `8e01b720` | `40e12f64293833056e311ab7aaf5a62fb3006353` |
| `iO/phase-a-base` | `5ed465f6` | `5382668bc9cc496355c83e7b77909d9647e089b3` |
| `land/ef-d1-lattice-families` (#387) | `bd4c6f2d` | `18dd79c18c6f92e3bb3aea0e37b7f10221508c83` |

`git ls-remote` after the push shows exactly these four heads. Each push succeeded on its first attempt.

Q-L2-1 (b) is carried out, and Contract's coe-A seal is now **0**. Q-L2-2 and Q-L2-3 are settled; see
*Dispositions*.

- **Rulings:**
  - EF-D1-W2 (B) with DL-66 (EF-H11-R5 (A)).
  - EF-D1-R1, settled by EF-W1-R (A) (SR1).
  - EF-D1-W3 (A).
  - Q-L2-1 (b), the coordinator's ruling of 2026-11-19 under EF-W1-R (A).
- **Run:** 2026-11-19, 01:10–02:25 UTC, in `$SP/land-384-387/`, where
  `$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Method:** no `lake build`, no cache get, and one Lean process at a time. The host had at most 3 `lean`
  processes at each start (`check/slot.log`).

## Commits (local, signed, every message ending with the two required trailer lines)

| Branch (local name) | Commit | Subject |
|---|---|---|
| `foundations/coin-sampling` (`tmp-land-378`) | `3473adda66d9c61c51ba640ed4c701e5cde0b6b1` | CoinSampling: readers of the bucket sampler's draw type, encoding and failure (+15, `Efficiency.lean`) |
| `foundations/coin-contract` (`tmp-land-384`) | `f96ae32ed861f33b67ebabf2b29344d2a66909cf` | CoinSampling: promote the shared sampler helpers into the contract (+85) |
| | `21f549c28317e96ae46edd92813ec01834791a3c` | Merge foundations/coin-sampling (bucketSampler readers) into the contract |
| | `40e12f64293833056e311ab7aaf5a62fb3006353` | CoinSampling: read the bucket sampler through its readers in drawSamplable_residue (proof only) |
| `iO/phase-a-base` (`tmp-land-iobase`) | `5382668bc9cc496355c83e7b77909d9647e089b3` | Merge foundations/coin-contract into the iO Phase A base (`--no-ff -S`; parents `5ed465f6`, `40e12f64`) |
| `land/ef-d1-lattice-families` (`tmp-land-387`) | `c4376f8e3cafa51e38048db36a8b4f3f38fa8cb3` | Merge iO/phase-a-base (with the #384 and #378 landing edits) into the EF-D1 landing |
| | `268c4bba061c19e21bd17351975f0ecb1119c955` | LE-d1-sr1 (diff identical to r2's `04006502`) |
| | `505e4a872bd42f80fa5b884978118a0fd7834d8b` | LE-d1-promote (diff identical to r2's `b7014700`) |
| | `18dd79c18c6f92e3bb3aea0e37b7f10221508c83` | LE-efd1-imp: `import TCSlib.Cryptography.LWE.Efficient` and a Contents line in `LWE.lean` (+2) |

- **Fast-forward.** Each local branch is a fast-forward of its remote. Every commit has one `gpgsig` and the
  exact trailer pair.
- **Earlier unpushed heads are superseded:** r2's `6e073201`, `2ede44f7`, `04006502` and `b7014700`.
- **What each change does:**
  - **#378.** The readers are `bucketSampler_Ω : bucketSampler.Ω y = Fin ⟦y⟧`,
    `bucketSampler_enc_cast : bucketSampler.enc y w = natToList |y| (cast (bucketSampler_Ω y) w)` and
    `bucketSampler_fail : (bucketSampler.sampler y s).fail = (bucket ⟦y⟧ s).fail`. All three are `rfl` with a
    "Glue." docstring.
  - **#384 promotion.** `DrawSamplable.comap` (new); `samplesEfficiently_comap` (EF-H11's statement and proof);
    `drawSamplable_restrict` (EF-D1's statement), now `h.comap fun κ _ => s κ`; `natToList_two_pow`;
    `polyTimeComputable_twoPowWord`; and `seedModulusWord` with `_eq`, `_eq_cons`, `listToNat_` and `length_`.
    Statements are the originals modulo the `CoinSampling.` prefix (decls2 text, checked). No import was added.
  - **#384 proof fix.** `drawSamplable_residue` builds its equivalence through `Equiv.cast (bucketSampler_Ω _)`
    and reads the encoding and the failure through `bucketSampler_enc_cast` and `bucketSampler_fail`. The
    statement is unchanged and the proof sketch is updated.
  - **SR1.** The worker's patch verbatim. `hs` and `CenteredSampleEq` with `_iff` and `_zero` are gone, and
    `dyadicExample` uses `centeredNoise 1`.
  - **Promote.** The local copies are deleted and every use names `CoinSampling.*`. `SIS/Efficient` imports
    `CoinSampling.Contract` in place of `LWE.Efficient`.
  - **LE-efd1-imp.** The line sits after `BitNoise`, and `git merge-tree` is clean against the records tip
    `eddf183f` and against `bff0567b`, next to #377's `Ratio` line. `LWE/Efficient`'s import closure does not
    contain the facade. With it, `LWE/Efficient` is back in root `TCSlib`'s closure (full order 1469), and the
    one check8b facade FAIL is gone.

## Re-check (r2b)

- **Trees.**
  - `$SP/olean-replay-efd1` was state-checked first: 1469/1469 OK at `e3fc2ce2`, and OK at the end. It was copied
    with `cp -al` to `replay2`.
  - `$SP/land-efr23/replay` gave 1470/1470 OK at `d898a09f`, before and at the end, and was copied to
    `replay393b`.
  - Snapshot #11 `snapmap verify`: 0/0/0 before, after the build and at the end.
  - The records tip `eddf183f` is no longer Lean-equal to `bff0567b`: only `GSW/Branching` and
    `GSW/DecryptFormula` changed, and neither is touched here. The check heads use `bff0567b`, as the brief asks.
- **#387 check head** (scratch merge of `18dd79c1` with `bff0567b`): `2291280b9a222298269b7ece1f82c07fbfd730cc`,
  tree `2614aca3…`, which equals the merge-tree. Never pushed.
  - **Plan:** 16 to build, 1453 reused.
  - **Build: 16/16 rc 0.** The modules are `BitNoise` and its 6 LWE/PRG downstream modules, `Pseudorandom`,
    **`Efficiency`**, `Contract`, `LWE/Efficient`, `LWE`, `SIS/Efficient`, `SIS`, `CoinSampling`, root `TCSlib`
    and `audits/garg-ch1-3/Checks`.
  - **Errors:** 0 `error:`/`error(`, 0 `sorry`.
  - **Warnings:** 5, all in `Flat`, from the pre-existing `simps` linter on a source unchanged since
    `bff0567b`.
  - **Accept:** `permod` is clean, the check gave **1469/1469 RESULT OK**, and all 16 rebuilt oleans have link
    count 1. `audits/pass-shelat/Checks` is not downstream of the change, and the state check covers it.
- **#393 scratch** (`fc095742` merged with `5382668b`, then with `bff0567b`): `4a28dafaf4e64866010184a9d5fcf62a84ee68ea`.
  - **Build:** 4 modules (`Efficiency`, `Contract`, `CoinSampling`, root), all rc 0 with 0 errors and 0 warnings.
    The check gave **1470/1470 OK**.
  - #393's 6 modules were re-elaborated as a probe: 6/6 rc 0. Not pushed.
- **Axioms** (`AxiomsHead`, census of 5 owners): 253 stored constants (Efficiency 50, Contract 40, BitNoise 17,
  LWE.Efficient 97, SIS.Efficient 49), all within `{propext, Classical.choice, Quot.sound}`.
  - The 30 named promoted, new and EF-D1 target declarations are all standard, including the three readers and
    `drawSamplable_residue`.
  - The `sorry` control reports `[sorryAx]`.
  - `SmokeHead` ran with rc 0 and 0 errors.
- **Canonical coe-A seal** (`mkseals_coe.py` A, unmodified, `SEAL_CHUNK=1000`):

  | Owner | Requests | Errors |
  |---|---|---|
  | `CoinSampling/Contract` | 1,063 | **0** (was 3 in r2; same requests) |
  | `LWE/BitNoise` | 6 | **0** |
  | `LWE/Efficient` | 3,013 | **0** |
  | `SIS/Efficient` | 1,100 | **0** |
  | `CoinSampling/Efficiency` | 1,055 | **3**, `src:208/215/222`: the private `binArith_{lt,sub,mod}_pairEncode` (pre-existing) |
  | `Efficiency` pre-edit (`9067223f`) | 1,055 | **3**, the same lines |

- **Paired controls:** ALL_OK.
  - Efficiency's 3 readers 3/3.
  - Contract `seedModulusWord_eq` 1/1.
  - BitNoise 2/2.
  - LWE 12/12.
  - SIS 5/5.
  - Sealed, each NEG fails once; unsealed, there are 0 errors and 0 stray errors.
- **Admissions:** 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque` tokens in the 6 changed files.
- **Lint:** `campaign_style_lint --check8b` gives 92 FAIL / 103 WARN, against 93/103 at the delivery's check
  head. The only difference is the removed `LWE.lean` facade FAIL; there is no new line. `style_lint`: 0 findings
  in 6 files.

## decls2 (pinned `decls2.py`, `fa81981a`)

| Comparison | Result |
|---|---|
| #378 `3473adda` vs `51dc7672` | **3 ADDED**: `bucketSampler_Ω`, `bucketSampler_enc_cast`, `bucketSampler_fail` |
| #384 `40e12f64` vs `8e01b720` (with `Efficiency.lean`) | **13 ADDED**: the 3 readers plus `DrawSamplable.comap`, `samplesEfficiently_comap`, `drawSamplable_restrict`, `natToList_two_pow`, `polyTimeComputable_twoPowWord`, `seedModulusWord`, `_eq`, `_eq_cons`, `listToNat_seedModulusWord`, `length_seedModulusWord` |
| #384 proof commit `40e12f64` alone | empty (proof only) |
| iO base `5382668b` vs `5ed465f6` | 13 ADDED (as #384) |
| #387 `18dd79c1` vs new base `5382668b` | **85 ADDED, 0 CHANGED, 0 REMOVED**, row for row equal to r2 |
| LE-efd1-imp alone | empty |
| #387 at delivery (`bd4c6f2d` vs `5ed465f6`) | 94 ADDED |

From 94 to 85:
- **Left #387's own diff:** the 8 promoted `LWE.*` names (they now come from the base) and `CenteredSampleEq`,
  `centeredSampleEq_iff` and `centeredSampleEq_zero`.
- **Joined it:** `LWE.bitNoise_sample_cast` and `LWE.centeredNoise_sample_cast`.
- **Other changes:** the remaining statement-text changes are SR1's 6 or the `CoinSampling.` prefix (8, prefix
  only).

## Dispositions

- **Q-L2-2. Three readers, not one.** The ruling named `bucketSampler_Ω` only. The sealed probe shows that it
  is not enough on its own:
  - **Encoding.** `bucketSampler_enc` is stated at `Fin`-typed draws, so it does not rewrite an `Ω`-typed draw
    under the seal ("did not find pattern").
  - **Failure.** `bucketSampler_sampler` puts `.fail` at the `Ω` type, so `fail_bucket_le`, stated at
    `Fin ⟦y⟧`, does not unify (heartbeat timeouts).
  - **The fix used here:** add `bucketSampler_enc_cast` (the analogue of SR1's `_sample_cast`) and
    `bucketSampler_fail`. Both are `rfl`, in our own file, so they fall under EF-W1-R (A).
  - **Also found:** the r2 seal had reported only 3 errors in `drawSamplable_residue`. The first error masked the
    encoding step, which had also been reading `bucketSampler`'s definition.
  - **Disposition (coordinator, 2026-11-19): accepted.** The three `rfl` readers in our own `Efficiency.lean`
    are covered by EF-W1-R (A).
- **Q-L2-3. `Efficiency.lean`'s own coe-A seal: 3 errors (pre-existing).**
  - **Where:** the private readers `binArith_lt_pairEncode`, `binArith_sub_pairEncode` and
    `binArith_mod_pairEncode` (`Efficiency.lean:205–222`, #378) read `Complexity.BinArith.lt`, `sub` and `mod`
    by `rfl`.
  - **Pre-existing:** the errors are identical before the edit, the three new readers add none, and the file's
    module docstring already discloses the debt ("`ClassP/BinaryArith` publishes no equation lemmas … Publishing
    them beside the definitions is a follow-up").
  - **Fix:** readers in the Complexity owner's `BinaryArith/AddSub.lean` and `Div.lean`, stated on encoded list
    pairs (`lt_def`, `sub_def`, `mod_def`, like the existing `beq_def`). Under EF-W1-R (A) that is an owner PR,
    not a landing edit.
  - **Options:**
    - (a) Ledger it as recorded debt and push now.
    - (b) Wait for the Complexity owner PR.

- **Disposition of Q-L2-3 (coordinator, 2026-11-19): (a).** Land now, on the footing of EF-H1-R2 (B) and
  EF-H12-R1 (A):
  - the three `binArith_{lt,sub,mod}_pairEncode` reads are recorded as bounded ledger debt (the coordinator
    records the row);
  - the `BinArith.lt`/`sub`/`mod` readers go on the Complexity owner PR list.

## Draft PR-description paragraphs

**#378:**
> **Landing edit (2026-11-19; Q-L2-1 (b), under EF-W1-R (A)).** Commit `3473adda` adds three `rfl` readers beside
> `bucketSampler` in `CoinSampling/Efficiency.lean`:
> - `bucketSampler_Ω : bucketSampler.Ω y = Fin ⟦y⟧`;
> - `bucketSampler_enc_cast`, the encoding of an `Ω`-typed draw;
> - `bucketSampler_fail`, the failure at `Fin ⟦y⟧`.
>
> With them, consumers such as #384's `drawSamplable_residue` read the bucket sampler through published
> readers rather than through its definition (Rule 10). decls2: 3 added. The owner and its downstream rebuild
> with rc 0. The paired controls (3 NEG, 3 POS) are exact. The file's own coe-A seal keeps its 3 known errors in
> the private `BinArith` readers (module docstring; Q-L2-3).

**#384:**
> **Landing edits (2026-11-19).**
> - **`f96ae32e`** (rulings EF-D1-W2 (B), EF-H11-R5 (A), ledger DL-66) adds to `CoinSampling/Contract.lean` the
>   sampler helpers that #387 (EF-D1) and EF-H11 had each stated locally:
>   - `DrawSamplable.comap` (new) and `samplesEfficiently_comap` (EF-H11's) reindex a sampler along a map of
>     public inputs;
>   - `drawSamplable_restrict` (EF-D1's) is now derived from `comap`;
>   - `natToList_two_pow`, `polyTimeComputable_twoPowWord` and `seedModulusWord` with four readers (EF-D1's) sit
>     beside `modulusWord`.
>
>   Statements are the originals, namespace aside, and no import or existing statement changes.
> - **Merge `21f549c2`** takes #378's `bucketSampler` readers.
> - **`40e12f64`** (Q-L2-1 (b)) re-proves `drawSamplable_residue` through them, proof only.
>
> decls2: 10 added in `Contract.lean`, plus #378's 3. Re-check on the iO base merged with `bff0567b`: rc 0, all
> new constants standard, and the coe-A seal of `Contract.lean` is **0 errors** (it had 3 pre-existing errors
> before this edit). `iO/phase-a-base` takes it in merge `5382668b`.

**#387:**
> **Updated (2026-11-19).** The branch merges `iO/phase-a-base` `5382668b`, which carries #384's and #378's
> landing edits, and adds three maintainer landing edits.
> - **LE-d1-sr1** `268c4bba` (EF-D1-R1 by EF-W1-R (A)):
>   - adds the `rfl` readers `bitNoise_sample_cast` and `centeredNoise_sample_cast` to `LWE/BitNoise.lean`;
>   - drops `hs` from `noise_efficient_of_bitNoise`;
>   - deletes `CenteredSampleEq` and its hypothesis, so `noise_efficient_centeredNoise` and
>     `EfficientFamily.ofDyadic` are unconditional;
>   - builds `dyadicExample` on `centeredNoise 1` (closes EFD1-F01).
> - **LE-d1-promote** `505e4a87` (EF-D1-W2 (B), DL-66):
>   - deletes the local copies of the helpers now in `CoinSampling/Contract.lean` and re-points every use;
>   - `SIS/Efficient` imports `CoinSampling.Contract`, no longer `LWE/Efficient` (EFD1-I1).
> - **LE-efd1-imp** `18dd79c1` adds `LWE.Efficient` to the `LWE.lean` facade. It merges cleanly with #377's line
>   on the records branch, and it puts `LWE/Efficient` back in root `TCSlib`'s closure, which it had left when
>   `SIS/Efficient` dropped its import.
>
> decls2 against the new base: 85 added, 0 changed, 0 removed (was 94). Re-check on the merge with `bff0567b`:
> 16 modules rc 0, including root and `audits/garg-ch1-3/Checks`, with state 1469/1469. Axioms are standard, and
> coe-A seals of `BitNoise`, `LWE/Efficient` and `SIS/Efficient` give 0 errors. Paired controls are ALL_OK, and
> the lint drops the facade FAIL with nothing new.

## State kept

- **Worktrees** under `$SP/land-384-387/`:
  - `wt378`, `wt384`, `wtio` and `wt387`: the local `tmp-land-*` branches, now equal to the pushed heads.
  - `mergewt2` (check head `2291280b` with probes) and `mergewt393b`.
  - `basewt` (`9067223f`, the pre-edit seals) and `dwt` (the decls2 checkouts).
  - The r2 `mergewt` and `mergewt393` are superseded.
- **Olean trees:** `replay2` (accepted at `2291280b`) and `replay393b` (accepted at `4a28dafa`). The r2
  `replay`/`replay393` are superseded: `replay` also holds a dev `Efficiency` olean outside its state.
- **Records:** `check2/` (plan, build, `permod`, state, `rule10/`, `rule10-base-eff/`, `decls2/`, `lint/`),
  `check393b/`, and r2's `check/`, `check393/`.
