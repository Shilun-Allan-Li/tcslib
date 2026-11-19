# EF-D1 · final r1 · landing r2: promotion into #384's `Contract.lean`, SR1 and re-point on #387

**Status: HELD, nothing pushed.** All five commits are made and signed locally, and every re-check passes
except one. The canonical coe-A seal of `CoinSampling/Contract.lean` gives **3 errors**. They all sit in the
**pre-existing** `drawSamplable_residue`, not in the promoted code. The seal of the pre-edit `Contract.lean`
gives the same 3 errors (see *Open question*). The brief requires 0 errors, so the three branches are not
pushed. The remote heads are unchanged: `foundations/coin-contract` `8e01b720…`, `iO/phase-a-base`
`5ed465f6…`, `land/ef-d1-lattice-families` `bd4c6f2d…`.

- **Rulings:** EF-D1-W2 (B) with DL-66 (EF-H11-R5 (A)), EF-D1-R1 settled by EF-W1-R (A) (SR1), and EF-D1-W3 (A).
  They are the decision-log rows of 2026-11-18.
- **Run:** 2026-11-19, 01:10–01:55 UTC, in `$SP/land-384-387/`, where
  `$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Method:** no `lake build`, no cache get, and one Lean process at a time. The host had at most 3 `lean`
  processes at each start (`check/slot.log`).

## Commits (local, signed, each message ending with the two required trailer lines)

| Branch (local name) | Commit | Tree | Subject |
|---|---|---|---|
| `foundations/coin-contract` (`tmp-land-384`) | `f96ae32ed861f33b67ebabf2b29344d2a66909cf` | `a4a40b65…` | CoinSampling: promote the shared sampler helpers into the contract (+85/−0, `Contract.lean` only) |
| `iO/phase-a-base` (`tmp-land-iobase`) | `6e073201feabf1258d7454a31c4f0c49f9f0b98c` | `5333ff6a…` | Merge foundations/coin-contract into the iO Phase A base (`--no-ff -S`; parents `5ed465f6`, `f96ae32e`; fast-forward of the remote) |
| `land/ef-d1-lattice-families` (`tmp-land-387`) | `2ede44f7439af9d85582e25c2d53942982c2aa90` | `68a4daf9…` | Merge iO/phase-a-base (with the #384 landing edit) into the EF-D1 landing (parents `bd4c6f2d`, `6e073201`) |
| | `04006502122bb7ca5cf65e12e4f3066fe2042e48` | `877cfdfc…` | LE-d1-sr1 (+35/−64: `BitNoise.lean`, `LWE/Efficient.lean`) |
| | `b7014700d93eb0c80aa5fb7afadbf098232d7f4c` | `3ab5aa3b…` | LE-d1-promote (+43/−92: `LWE/Efficient.lean`, `SIS/Efficient.lean`) |

- **#387 against the new base** (`6e073201..b7014700`): 4 files, +1,003/−0. `LWE/Efficient.lean` is 680 lines
  (was 771), `SIS/Efficient.lean` 310, `BitNoise.lean` +11 and `SIS.lean` +2.
- **Statements.** The promoted statements equal the originals modulo the `CoinSampling.` prefix (decls2 text
  comparison). `samplesEfficiently_comap` has EF-H11's statement and proof (exchange `4e787bc2`,
  `SecretSharing/Efficient.lean:157`).
  - `drawSamplable_restrict` is now `h.comap fun κ _ => s κ`.
  - `DrawSamplable.comap` is new.
  - `seedModulusWord` moved with its four readers (`_eq`, `_eq_cons`, `listToNat_`, `length_`).
    `seedModulusWord_uniform`, `seedModulus` and `modulusWord_seedModulus` stay in `LWE` (schedule-level; F03
    bridge).
  - No import was added to `Contract.lean`: everything needed is already in its closure. No LWE import.
- **SR1** is the worker's `scope/EF-D1-SR1-BitNoise.patch.txt` verbatim. `hs` is dropped, and `CenteredSampleEq`,
  `centeredSampleEq_iff` and `centeredSampleEq_zero` are deleted along with the hypothesis on
  `noise_efficient_centeredNoise`, `ofDyadic`, `ofDyadic_toFamily` and `ofDyadic_noiseInput`. `dyadicExample`
  uses `centeredNoise 1`.
- **`SIS/Efficient`** imports `CoinSampling.Contract` in place of `LWE.Efficient`, and its module note is reworded.

## Re-check

- **Trees.**
  - `$SP/olean-replay-efd1` was state-checked first: 1469/1469 RESULT OK at `e3fc2ce2`, and still OK at the end.
    It was copied with `cp -al` to `replay` (1501 files plus 3346 Mathlib symlinks).
  - For #393, `$SP/land-efr23/replay` was checked the same way (1470/1470 at `d898a09f`, OK at the end) and
    copied to `replay393`.
  - Snapshot #11 `snapmap verify`: 0/0/0 before, after the build and at the end.
  - The records tip `eddf183f` is no longer Lean-equal to `bff0567b`: 3 GSW-6b commits changed `GSW/Branching`
    and `GSW/DecryptFormula`. The check heads still use `bff0567b`, as the brief asks. Those two GSW files are
    not touched here.
- **#387 check head** (scratch merge of `b7014700` with `bff0567b`): `476ba3bd32a11df71784a7731bca49e9be4e0d28`,
  tree `aaf60797…`, which equals `git merge-tree --write-tree`. Never pushed.
  - **Plan:** 15 to build, 1454 reused.
  - **Build: 15/15 rc 0.** That is `BitNoise`, its 6 LWE/PRG downstream modules, `LWE`, `Contract`,
    `SIS/Efficient`, `SIS`, `CoinSampling`, root `TCSlib`, `audits/garg-ch1-3/Checks` and `LWE/Efficient`.
  - **Errors:** 0 `error:`/`error(`, 0 `sorry`.
  - **Warnings:** 5, all in `Pseudorandom/Generators/LWE/Flat`. They are the pre-existing `simps` linter
    warnings: the source is unchanged since `bff0567b`, and earlier replays show the same 5.
  - **Accept:** `permod` shows no mismatch, `stateplan update` took 15, the check gave **1469/1469 RESULT OK**,
    and all 15 rebuilt oleans have link count 1. `audits/pass-shelat/Checks` is not downstream of the change;
    its closure key is unchanged and the state check covers it.
  - **Note: `LWE/Efficient` is no longer in root `TCSlib`'s closure.** It was reachable only through
    `SIS/Efficient`'s import, and the `LWE.lean` facade line (LE-efd1-imp) is still pending. It was built
    explicitly through an extended order (`full-order-ext.txt`). `fullorder` of the head alone gives 1468.
- **#393 scratch** (`fc095742` merged with `6e073201`, then with `bff0567b`; never pushed):
  `4dfa92af3271ff86965e461f2731fcfa421951a0`, tree `c16f3317…`.
  - **Plan:** 3 to build (`Contract`, `CoinSampling`, root), 1467 reused. All 3 rc 0 with 0 errors, 0 `sorry`
    and 0 warnings. The check gave **1470/1470 OK**.
  - #393's 6 changed modules were re-elaborated as a probe (`runner_full`, no `-o`): 6/6 rc 0, 0 errors.
    They do not import `Contract`.
- **Axioms** (`AxiomsHead`, census of the 4 owners). There are 203 stored constants: Contract 40, BitNoise 17,
  LWE.Efficient 97 and SIS.Efficient 49. Every one is within `{propext, Classical.choice, Quot.sound}`, and none
  is non-standard.
  - The `sorry` control reports `[sorryAx]`.
  - The promoted, new and EF-D1 target declarations are each standard. `seedModulusWord`, `_eq` and `length_`
    use `[propext]`; the others use the three standard axioms.
  - `SmokeHead` (D1-P2 plus the unconditional `ofDyadic` and the `centeredNoise 1` example) ran with rc 0 and
    0 errors.
- **Canonical coe-A seal** (`mkseals_coe.py` A, unmodified, `SEAL_CHUNK=1000`):

  | Owner | Requests | Errors |
  |---|---|---|
  | `LWE/BitNoise` | 6 | **0** |
  | `LWE/Efficient` | 3,013 | **0** (no `CenteredSampleEq` residue) |
  | `SIS/Efficient` | 1,100 (was 3,046: the LWE closure is gone) | **0** |
  | `CoinSampling/Contract` | 1,063 | **3**, `src:436`, `src:449`, both in `drawSamplable_residue` (pre-existing) |
  | `Contract` pre-edit (`9067223f`, read-only on `olean-replay-efd1`) | 1,063 | **3**, the same 3 at `src:351`/`:364` (+85 = 436/449) |

- **Paired controls:** ALL_OK.
  - New: Contract `seedModulusWord_eq` 1/1, and BitNoise `bitNoise_sample_cast` and `centeredNoise_sample_cast`
    2/2. Sealed, each NEG fails once; unsealed, there are 0 errors.
  - Re-run: LWE 12/12 (the old C03 moved to Contract, and C13 was deleted with `CenteredSampleEq`) and SIS 5/5.
  - Stray errors: 0.
- **Admissions:** 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque` in the 4 changed files.
- **Lint:**
  - `campaign_style_lint --check8b`: old check head `e3fc2ce2` and new check head both give 93 FAIL / 103 WARN
    over 553 files, with an empty line-set diff. Only the INFO size lines differ. The `LWE.lean` facade FAIL is
    unchanged and pending LE-efd1-imp.
  - `style_lint`: 0 findings in 4 files.

## decls2 (pinned `decls2.py`, `fa81981a`)

| Comparison | Result |
|---|---|
| #384 `f96ae32e` vs `8e01b720` (iO base `6e073201` vs `5ed465f6` is identical) | **10 ADDED**: `DrawSamplable.comap`, `samplesEfficiently_comap`, `drawSamplable_restrict`, `natToList_two_pow`, `polyTimeComputable_twoPowWord`, `seedModulusWord`, `seedModulusWord_eq`, `seedModulusWord_eq_cons`, `listToNat_seedModulusWord`, `length_seedModulusWord` |
| #387 old `bd4c6f2d` vs old base `5ed465f6` | 94 ADDED |
| #387 new `b7014700` vs new base `6e073201` | **85 ADDED, 0 CHANGED, 0 REMOVED** |
| LE-d1-sr1 alone | 2 ADDED (the BitNoise readers), 3 REMOVED (`CenteredSampleEq`, `_iff`, `_zero`), 6 CHANGED (`noise_efficient_of_bitNoise`, `noise_efficient_centeredNoise`, `ofDyadic`, `ofDyadic_toFamily`, `ofDyadic_noiseInput`, `dyadicExample_noise`) |
| LE-d1-promote alone | 8 REMOVED (the `LWE.` copies), 8 CHANGED (prefix only, `seedModulusWord` → `CoinSampling.seedModulusWord`) |

From 94 to 85: the 8 promoted `LWE.*` names and the 3 `CenteredSampleEq` declarations leave #387's own diff,
and `LWE.bitNoise_sample_cast` and `LWE.centeredNoise_sample_cast` join it. Every statement-text change in the
remaining 83 shared rows is either SR1's or the `CoinSampling.` prefix.

## Open question (blocks the push)

**Q-L2-1. The pre-existing Rule-10 residue in `Contract.lean`.**
- **Where:** `drawSamplable_residue` (#384) builds `bucketSampler.Ω (modulusWord b κ q) ≃ ZMod q` from
  `Fin (listToNat …)`, and rewrites `listToNat (modulusWord …)` in `fail_bucket_le`'s goals.
- **Why it fails:** both steps read `bucketSampler`'s definition (`Ω y := Fin ⟦y⟧`, `CoinSampling/Efficiency.lean:308`,
  #378). Efficiency.lean publishes `bucketSampler_sampler`, `_raw` and `_enc`, but no `Ω` reader. Sealed, this
  gives 3 errors, identical before and after this edit. No earlier record mentions it.
- **Likely fix (not made: it touches #378's `Efficiency.lean` and a #384 proof):**
  - a reader `bucketSampler_Ω (y) : bucketSampler.Ω y = Fin (listToNat y) := rfl` in `Efficiency.lean`;
  - a proof-only rewrite of `drawSamplable_residue` through it (`Equiv.cast`).
- **Options:**
  - (a) Accept it as recorded pre-existing debt, for example a ledger row like DL-68, and push as is.
  - (b) Add the reader and the proof fix as a further landing edit (on #378 and #384, or on #384 alone) before
    pushing.

## Draft PR-description paragraphs (for when the push happens)

**#384:**
> **Landing edit (2026-11-19; rulings EF-D1-W2 (B), EF-H11-R5 (A), ledger DL-66).** Commit `f96ae32e` adds to
> `CoinSampling/Contract.lean` the sampler helpers that #387 (EF-D1) and EF-H11 had each stated locally:
> - `DrawSamplable.comap` (new) and `samplesEfficiently_comap` (EF-H11's) reindex a sampler along a map of
>   public inputs.
> - `drawSamplable_restrict` (EF-D1's) is now derived from `comap`.
> - `natToList_two_pow`, `polyTimeComputable_twoPowWord` and `seedModulusWord` with its four readers (EF-D1's)
>   sit beside `modulusWord`.
>
> Statements are the originals, namespace aside, and no existing declaration or import changes. decls2: 10 added.
> Re-check on the iO base merged with `bff0567b`: `Contract` and its downstream rc 0, all new constants standard
> axioms, and the paired control for `seedModulusWord_eq` passes. The coe-A seal shows only the 3 pre-existing
> `drawSamplable_residue` errors (see Q-L2-1). `iO/phase-a-base` takes it in merge `6e073201`.

**#387:**
> **Updated (2026-11-19).** The branch merges `iO/phase-a-base` `6e073201`, which carries #384's landing edit, and
> adds two maintainer landing edits.
> - **LE-d1-sr1** `04006502` (EF-D1-R1 by EF-W1-R (A)):
>   - adds the `rfl` readers `bitNoise_sample_cast` and `centeredNoise_sample_cast` to `LWE/BitNoise.lean`;
>   - drops `hs` from `noise_efficient_of_bitNoise`;
>   - deletes `CenteredSampleEq` and its hypothesis, so `noise_efficient_centeredNoise` and
>     `EfficientFamily.ofDyadic` are unconditional;
>   - builds `dyadicExample` on `centeredNoise 1` (closes EFD1-F01).
> - **LE-d1-promote** `b7014700` (EF-D1-W2 (B), DL-66):
>   - deletes the local copies of the helpers now in `CoinSampling/Contract.lean` and re-points every use;
>   - `SIS/Efficient` imports `CoinSampling.Contract` and no longer imports `LWE/Efficient` (EFD1-I1).
>
> decls2 against the new base: 85 added, 0 changed, 0 removed (was 94). Re-check on the merge with `bff0567b`:
> 15 modules rc 0, including root and `audits/garg-ch1-3/Checks`, with state 1469/1469. Axioms are standard, and
> coe-A seals of `BitNoise`, `LWE/Efficient` and `SIS/Efficient` give 0 errors. Paired controls are ALL_OK, and
> the lint is unchanged. Note: until LE-efd1-imp adds the `LWE.lean` facade line, `LWE/Efficient` is outside
> root `TCSlib`'s import closure.

## State kept (for the resume or the gate)

- **Worktrees** under `$SP/land-384-387/`:
  - `wt384`, `wtio` and `wt387`: the local branches `tmp-land-384`, `tmp-land-iobase` and `tmp-land-387` hold the
    unpushed commits.
  - `mergewt` (check head `476ba3bd` with probes), `mergewt393`, `basewt` (`9067223f`, the pre-edit seal) and
    `dwt` (the decls2 checkouts).
- **Olean trees:** `replay` (accepted at `476ba3bd`) and `replay393` (accepted at `4dfa92af`).
- **Exports:** `tree387` and `tree393`.
- **Records** in `check/` and `check393/`: plans, build logs, `permod`, state and link-count files, snapshot
  verifications, `rule10/` (probes, seals, `ctlcheck.log`), `rule10-base/` (the pre-edit seal), `decls2/` and
  `lint/`.
- **To push after Q-L2-1**, fast-forward only:
  - `git push origin tmp-land-384:foundations/coin-contract tmp-land-iobase:iO/phase-a-base`;
  - `git push origin tmp-land-387:land/ef-d1-lattice-families`.
