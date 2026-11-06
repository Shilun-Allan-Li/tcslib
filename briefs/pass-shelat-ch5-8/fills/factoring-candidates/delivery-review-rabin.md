# Delivery review: fill unit rabin (the Rabin candidates)

- **Delivery:** `inbox/fills/rabin/` on `exchange/pass-shelat-ch5-8` at
  `1ac1798200b4930bed90c2036314d6a75c09cde8` (REPORT.md, 12 patches, `src/`, `evidence/`).
- **Worker branch:** `fill/rabin`, head `8295c2054dc27b7757353b1c091b8ed1b81e0100` (the `From` line of
  patch 12), base `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1`, 12 commits.
- **Brief:** `brief-issued.md`, unit rabin (D3 for the permitted `sorryAx` sources), with `review.md`;
  issue notes `../NOTES-2026-11-07.md` items 1–7. **Policy:** `policy.md`.
- **Landing context:** `land/fac` at `816329e5a8c7d0330a6d28b73855c5ad59eb07b4` (fac and rsa
  landed on #210's head `3436321b`, where `Rabin.lean` is unchanged since `16a7d02d`).
- **Reviewed:** 2026-11-06. This was an independent run:
  - the patches were replayed at the issue base, and again with `git am -3` on the landing context;
  - Lean was re-run one module at a time with `scripts/lean_check_tree.sh` against a copy of
    `land-fac-oleans`, never with `lake build`;
  - the seal names were collected from the elaborated terms, not taken from the worker's list.
  - A container restart interrupted the collector run once. It was re-run in full, and every
    other log was confirmed complete.

## Verdict: **land after edits**

All 19 targets are filled. No statement changed, and no `sorry` or `axiom` was added.

On the landing context:
- `Rabin`, the facade and `audits/pass-shelat/Checks` elaborate with 0 errors and 0 warnings.
- 11 targets print the standard triple.
- The other 8 reach `sorryAx` **only** through dl-a's `statClose_rejectBlocksL`. That source is
  on D3's rabin list, and dl-a is not yet on this branch.
- With dl-a's `Concrete.lean` from `land/dl` (`b76e614d`), **all 19 targets and the 13 Rabin
  headlines and constructions print `[propext, Classical.choice, Quot.sound]`**. The module
  sweeps find 0 of 173 (Rabin), 0 of 158 (RSA) and 0 of 70 (Factoring) constants with
  `sorryAx`.

The other checks pass:
- every base statement is byte-identical;
- the 14 docstring changes are authorized and describe their proofs, with one notational nit;
- the 178 new declarations are all `private` and `rabin_`-prefixed;
- the rule-10 seal holds under this review's 57-name list (`PolyExpr.eval` left unsealed by
  ruling Q1). The only sealed failures are the two base proofs `rabinCollection_index` and
  `rabinBlumTrapdoor_index`, and their re-points were checked;
- every route departure is sound, including `δ n = 1` for `n < 3` and the bound `1/(64n²)`,
  which takes `BlumDensity` only as the hypothesis `hD`.

There are **no blockers and no majors**. The edits are minor and proof-, citation- or
docstring-only:
- **E1** replaces `rabin_appendEquiv`, an undisclosed copy of Mathlib's `Fin.appendEquiv`, by a
  citation (as rsa's E1 did).
- **E2** proves `rabin_pushesUniform_prod` from the library's `PushesUniform.prodMap`,
  `pushesUniform_id` and `PushesUniform.uprob_eq`. The REPORT's shared-lemma request 5 is then
  unnecessary.
- **E3** refreshes four frozen sketches that no longer describe their proofs
  (`polyTimeComputable_oddGenRaw`, `rabinSampler_spec`, `blumSampler_spec`,
  `blumFactoring_of_rabinBlum_oneWay`). It also drops "on the last two bits" from
  `polyTimeComputable_blumGenRaw`'s lead and disambiguates `blumFactorProb_le`'s chain. These are
  docstring changes only, under the user's standing ruling.

E1–E3 are applied on `land/rabin-review` as one commit, **`01402b335b950cfbc9b2897e051fdc104d1fb0ca`**,
and every check was re-run there. The remaining copies of the dl-a and rsa loop and numeral
helpers wait for the shared-lemma PR (DL-27/DL-28). Finding 5 lists them, and **D1** is the
ledger row.

## Checks

| # | Check | Result |
|---|---|---|
| 1 | Integrity | Scratch worktree `$SP/wt-rev-rabin` (detached at `16a7d02d`). `git am` of the 12 patches is clean (`am.log`). `Rabin.lean` equals `src/` byte for byte (`cmp`), and `src/` holds only that file. `git diff --stat`: 1 file, 2741 insertions and 82 deletions. The 82 deleted lines are the 19 `  sorry` and 63 lines of the 14 changed docstrings: the closing lines of the 7 short docstrings, and the 7 rewritten **Proof sketch** paragraphs. The worker's commit hashes are not reproducible, because `git am` sets a new committer date. The `From` line of patch 12 is `8295c205`, the stated head. |
| 1 | Landing replay | `git am -3` on `816329e5` is clean (`am-land.log`). The result, `ffd58919`, has `Rabin.lean` equal to `src/`. `Rabin.lean` is the only file changed against `816329e5`. |
| 2 | Statement freeze | Own declaration-level comparison (`tools/declfreeze_rev.py`, `declfreeze-rev.log`, `declfreeze-docdiff.log`). All 124 base declarations are present, in base order, with byte-identical headers. The 19 target bodies are filled, and no other base body changed. Docstrings changed only for the 14 targets of finding 3. All 178 new declarations are `private` with the prefix `rabin_`. The diff adds no `set_option`, `attribute`, `open`, `section`, `instance`, `@[simp]`, `sorry`, `axiom` or `native_decide`. The `decide`s it adds are numeric facts (`Nat.Prime 7`, `ds.length ≤ 3`). Base sorries: 19; at the head: 0. |
| 3 | Olean copy | `$SP/rev-rabin-oleans`, a copy of `land-fac-oleans`; the original was only read. `Concrete`, `Factoring` and `RSA` were rebuilt into the copy, and each `.olean` is byte-identical to the original by sha256, as is `Arithmetic` (`olean-verify.log`). |
| 3 | Elaboration (landing) | `module-checks.log`: `Rabin` 16 s, 0 errors, 0 warnings; facade 3 s; `Checks` 140 s, 0 errors. After E1–E3 (`edits/module-checks-edited.log`): `Rabin` 10 s, facade 4 s, `Checks` 148 s, all 0 errors and 0 warnings. |
| 3 | Axioms (landing) | `probe/Axioms.lean`, `axioms.log`, `axioms-summary.txt`. Standard triple (11): `oddFactorProb_le`, `blumFactorProb_le`, `blumFactoring_of_factoring`, `polyTimeComputable_oddGenRaw`, `_blumGenRaw`, `rabinSampler_spec`, `polyTimeComputable_rabinFactorRaw`, `_blumInvRaw`, `blumInv_spec`, `blumSampler_spec`, `polyTimeComputable_rabinRootRaw`. These are also standard: `rabin_symmetry`, `negligible_rabinErr`, both `_index` lemmas and the constructions `oddGen`, `blumGen`, `rabinCollection`, `rabinBlumTrapdoor`, `blumInv`, `rabinSampler`, `blumSampler`, `rabinFactorer` and `rabinBlumInverter`. With `sorryAx` (8): `rabinCollection_sampleClose`, `_invProbAt_le`, `_oneWay`, `rabinBlumTrapdoor_sampleClose`, `_invProbAt_le`, `_oneWay`, `blumFactorProb_le_invProbAt` and `blumFactoring_of_rabinBlum_oneWay`. The sorry-source probe lists exactly one source for each: `statClose_rejectBlocksL` (`Candidates/Concrete.lean`). **D3: pass.** Rsa's `polyTimeComputable_unitSampleStr` and S3 are filled on `land/fac`, so the REPORT's extra sources are gone. Sweep: Rabin 8 of 173, RSA 5 of 158 (rsa's dl-a sources), Factoring 0 of 70. |
| 3 | Integration (dl-a) | Scratch worktree at `ffd58919` with `Concrete.lean` from `land/dl` `b76e614d`, and a second olean copy. `order.txt` lines 62–72 (`Concrete` to `Rabin`) and the facade were recompiled, all rc 0 (`integration-dl.log`). The one warning is in the unchanged base `Collections.lean`, an unused simp argument. **All 32 prints are the standard triple; the sweeps find 0/173, 0/158 and 0/70** (`integration-dl-axioms-summary.txt`). Nothing remains. The worktree and the copy were removed afterwards. |
| 4 | Rule 10, own seal | See finding 7. 58 foreign definitions (wide pass) minus `PolyExpr.eval` gives 57 sealed. The whole-file sealed copy fails only at the base proofs `rabinCollection_index` and `rabinBlumTrapdoor_index`. With their re-points it has 0 errors. Controls C1–C12 close unsealed and fail sealed, and Q1a/Q1b show the need for ruling Q1. |
| 5 | Duplication | See findings 1, 2, 4 and 5. |
| 6 | Routes | See finding 6. |
| 7 | Toolchain | See finding 8. |
| — | Lint | `style_lint.py`: exactly 1 finding, the size line (3810 > 1000; `style-lint-head.log`). After E1–E3 it is the size line only (3814; `edits/style-lint-edited.log`). `campaign_style_lint.py --check8b`: no FAIL row for Rabin, so the seven short-sketch FAILs of the issue tree are gone. The size WARN is present, and the check-8 WARN lists the same 25 names as the worker's base run, so there is no new public `def`. The only FAIL is the base `ElGamal.lean` row (`campaign-lint-head.log`). Size: 3809 lines (1150 at the base), 3814 after E1–E3. This is the approved exception (D2, user ruling): noted only, not split. |

## Findings

1. **minor: `rabin_appendEquiv` is an undisclosed copy of Mathlib's `Fin.appendEquiv`.**
   - The private definition (10 lines) is field for field `Fin.appendEquiv` at `α = Bool`. The
     REPORT discloses it only as a copy of rsa's `rsa_appendEquiv`. Rsa's review found that copy
     to be Mathlib's, and `land/fac` already cites `Fin.appendEquiv` (rsa E1).
   - **E1** deletes the copy and cites `Fin.appendEquiv` in `rabin_fCoinsEquiv`,
     `rabin_fCoinsEquiv_ofFn`, `rabin_genCoinsEquiv` and `rabin_genCoinsEquiv_ofFn` (6
     occurrences). Two docstrings name it. The `show … from rfl` steps still hold.

2. **minor: `rabin_pushesUniform_prod` is a corollary of public library lemmas.**
   - The REPORT calls it "the product form of `PushesUniform.uprob_eq`" and requests it as a
     shared lemma (request 5).
   - `HardcoreBit/Basic.lean`, in the closure, already has `PushesUniform.prodMap` and
     `pushesUniform_id`. So the helper is
     `(h.prodMap pushesUniform_id).uprob_eq fun w => P w.1 w.2`.
   - **E2** replaces its two-line proof by that term. The helper is kept, because its stated form
     is what `rabin_inner_blum` uses. Request 5 is withdrawn.

3. **minor: docstrings.** The 14 changes are authorized. **E3** refreshes the stale ones.
   - **Authorization.** The 7 short docstrings were each expanded by an appended **Proof sketch**
     paragraph, with the lead kept: `blumFactoring_of_factoring`,
     `polyTimeComputable_blumGenRaw`, `rabinCollection_sampleClose`,
     `polyTimeComputable_blumInvRaw`, `rabinBlumTrapdoor_sampleClose`,
     `rabinBlumTrapdoor_oneWay` and `polyTimeComputable_rabinRootRaw` (brief, "Seven Rabin
     targets"). Seven **Proof sketch** paragraphs were rewritten, all for brief-marked
     **Route**/**Correction** targets:
     - `blumInv_spec` (step 2, Route);
     - `oddFactorProb_le` and `blumFactorProb_le` (step 4, Correction);
     - `polyTimeComputable_rabinFactorRaw` (step 6, Correction);
     - `rabinCollection_invProbAt_le`, `rabinBlumTrapdoor_invProbAt_le` and
       `blumFactorProb_le_invProbAt` (step 8, Correction).

     Each change is docstring only, and each statement is byte-identical.
   - **Accuracy.** Each of the 14 was checked line by line against its proof. All describe the
     proofs, for example:
     - `oddFactorProb_le`'s `1 − 3/|Π_n|` with `|Π_n| ≥ 6` (`rabin_six_le_card_primes`);
     - `blumInv_spec`'s CRT unit and `Equiv.symm_apply_eq` without reading `blumSqrt`
       (`rabin_blumInvNat_spec`);
     - `rabinFactorRaw`'s padded modulus word and the low-`n`-bit truncation;
     - the invProbAt sketches' structure (generator law first, `rabin_uexp_le`, `rabin_core`).

     One nit: `blumFactorProb_le` writes `Pr[E] ≥ Pr_{Π_n×Π_n}[p ≠ q ∧ E] ≥ Pr[E] − …`. Its
     second `Pr[E]` is over `Π_n × Π_n`, not over the distinct pairs, and E3 says so.
   - **Stale frozen sketches** (not targets of a Route or Correction, so the worker rightly left
     them). E3 refreshes them under the user's standing ruling: docstring only, statement
     unchanged.
     - `polyTimeComputable_oddGenRaw` (the REPORT asks for this refresh). The frozen text tests
       oddness "on the last bit", calls the fallback "the constant fallback numeral" and uses
       `H.prime`, `pairEq` and `H.le` in the validity test. The proof instead tests parity by
       `H.divMod` by `⟦2⟧` and `H.le`, as brief step 5 directs. It zero-pads the fallback to `m`
       bits by `H.sub`/`H.add`, and its validity test is `pairEq` alone, because both values are
       always class primes below `2^m` (`rabin_samplePrimePL_spec`).
     - `polyTimeComputable_blumGenRaw`: the kept lead says the test runs "on the last two bits".
       The proof (and the worker's appended sketch) reads the residue modulo 4 by `H.divMod`. E3
       drops the four words.
     - `rabinSampler_spec`: the proof reads the value back by canonical decoding
       (`rabin_enc_of_dec`, `natToList_val_natCast`), through `rabin_dec_unitSampleStr`.
     - `blumSampler_spec`: the proof shows QR membership as the square of
       `ZMod.unitOfCoprime v` (`mem_QR_iff`, `ZMod.natCast_mod`), and reads the value back by
       `rabin_blumEnc_of_dec`.
     - `blumFactoring_of_rabinBlum_oneWay`: "`h.hard`" is the `hard` clause read through
       `TrapdoorCollection.oneWay_iff` (P2).

4. **minor: the duplication disclosure is incomplete.** The REPORT's copy table is confirmed
   (finding 5). This review compared every `rabin_` declaration with the private helpers of
   `land/fac` (`RSA.lean`, `Factoring.lean`) and `land/dl` (`DiscreteLog`,
   `DiscreteLogHardcore`, `ElGamal`, `Concrete`). It used normalized text similarity
   (`tools/neardup.py`, `neardup.log`) and searched the library and Mathlib. The REPORT does not
   disclose:
   - **`rabin_appendEquiv`**: Mathlib `Fin.appendEquiv` (finding 1, E1).
   - **`rabin_pushesUniform_prod`**: the library's `PushesUniform.prodMap` + `uprob_eq`
     (finding 2, E2).
   - **`rabin_statClose_one`**: verbatim dl-a's private `dla_statClose_one`
     (`DiscreteLog.lean:1139`, similarity 1.00). The REPORT lists it as "the trivial bound from
     `statClose_iff`". No public form exists.
   - **`rabin_listToNat_mulStr`**: rsa's `rsa_listToNat_mulStr` (0.97).
   - **`rabin_prime_poly`**: rsa's `rsa_prime_poly` (0.81, the same `primeStr_eq` rewrite).
   - **`rabin_rS`, `rabin_rQ`, `rabin_rTest`**: rsa's `rsa_fS`, `rsa_fQ`, `rsa_fTest` (0.98–0.99).
     These are the same words for the same `p' q' = N` test of a factorer's answer, as data.
   - **`rabin_listToNat_four`/`_five`/`_seven`**: more members of the numeral family whose
     `_one`/`_two`/`_three` are disclosed.
   - **A fourth copy of the block loop.** `rabin_rb*` and `rabin_find?_range_lt` also match dl-c's
     `dlc_ss*` and `dlc_find?_range_lt` (`ElGamal.lean` on `land/dl`; 0.94–1.00).
     `rabin_find?_range_lt` is close to `OneWay.find?_range_eq_map_find?_finRange` in the
     closure. The origin of the loop family is Primality's private `spStep`/`length_spStep_*`
     (rsa review, finding 4).
   - **`rabin_comp`**: also rsa's `rsa_comp` and dl-b's `dlb_ptc`, besides the private
     `ptc_comp` the REPORT names. It is `PolyTimeComputable.comp` in applied form, and it is kept
     for notes item 7.
   - **The inner `hnum` of `rabin_drop_zeros_append`**: fac's `fac_natToList_mod`, carried over
     with rsa's copy.
   - **`rabin_mkDP`/`rabin_zOf`**: parallel to fac's `fac_pairDec` as well as rsa's
     `rsa_zsel`/`rsa_zOf`, which the REPORT names.

   Disclosed and confirmed:
   - the loop family, `rabin_listToNat_append`/`_zeros_append`, `rabin_drop_zeros_append`,
     `rabin_val_inv_zero_le`, `rabin_one_mod_spec`, `rabin_getD_spec`, `rabin_le_poly` and
     `rabin_listToNat_one`/`two`/`three` (rsa, and through rsa dl-a);
   - the "same pattern" items `rabin_sampler_runAt`, `rabin_coins_sampler`,
     `rabin_statClose_dec`, the coin-equivalence `_ofFn` lemmas and `rabin_uexp_le`;
   - the library near-duplicates `rabin_unitsCongr`, `rabin_card_primes_le` and
     `rabin_uprob_subtype_le`.

   The number theory is Mathlib's or TCSlib's throughout, as the REPORT says.

5. **minor (disclosed debt): which copies become citations now, and which wait.**
   - **Now** (public, on this branch): `Fin.appendEquiv` (E1) and `PushesUniform.prodMap` (E2).
     Nothing else can be cited now: every other source is `private` in a landed file (`RSA.lean`,
     `Factoring.lean`) or lives in dl-a, which is not on `land/fac`.
   - **Wait for the shared-lemma PR** (ledger DL-27 H1, folded with DL-28). These are the
     proposed homes, reconciled with the rsa review's E4 table:
     - `Candidates/Arithmetic.lean`:
       - `listToNat_append`, `listToNat_natToList_zero_append` and `natToList_zero_append_drop`
         retire `rabin_listToNat_append`, `_zeros_append` and `rabin_drop_zeros_append`;
       - `listToNat_mulStr` retires `rabin_listToNat_mulStr`;
       - `listToNat_singleton_true` and small numeral lemmas retire
         `rabin_listToNat_one`/`two`/`three`/`four`/`five`/`seven`;
       - fac's `natToList_mod` retires the inner `hnum`;
       - a zero-padding lemma, the REPORT's request 2, retires `rabin_pad`/`rabin_zpad` and
         `_eq`.
     - `Complexity/ClassNP/PolyTime.lean`: `PolyTimeComputable.comp'` (and `.congr`) retires
       `rabin_comp`.
     - `Randomized/Build/IterateFind.lean`: `IterateFind.find?_range_and_lt` retires
       `rabin_find?_range_lt`.
     - `Asymptotic/Sampling.lean`, two new entries for H1:
       - `statClose_one` retires `rabin_statClose_one` and `dla_statClose_one`;
       - `uexp_le_of_statClose` retires `rabin_uexp_le` and rsa's `rsa_uprob_pi_eval`
         device (the REPORT's request 4).
     - `Candidates/RSA.lean`, beside `sampleUnitL_spec`: a public
       `sampleUnitL_getD_spec`, new for H1, retires `rabin_getD_spec`/`rabin_one_mod_spec` and
       rsa's `rsa_getD_spec`/`rsa_one_mod_spec`.
     - `Candidates/Concrete.lean`, beside `DistinctPrimes`: a published selector, which would
       serve `rabin_mkDP`/`rabin_zOf`, `rsa_zsel`/`rsa_zOf` and `fac_pairDec`.
     - `rabin_val_inv_zero_le` (with rsa's copy) beside `xgcdStr_pairEncode`, and
       `rabin_le_poly`/`rabin_prime_poly` as bundle wrappers in applied form beside
       `ArithmeticFP`. These are optional.
   - **Wait for H2** (the statement-gated `polyTimeComputable_rejectBlocksL` in `Concrete.lean`,
     the REPORT's request 1 and the brief's rabin request). It retires `rabin_rbStep`, `_rbBlock`,
     `_rbAcc`, `_rbOut`, `_rbLoop`, their `_poly`/`_iterate`/`length_` lemmas, `rabin_rbFind_eq`,
     `rabin_spStart` and `rabin_spOut`/`_eq`/`_poly`. With rsa's `rsa_us*`, dl-a's `dla_ss*`
     and dl-c's `dlc_ss*`, H2 retires four copies.
   - **Keep:** `rabin_rS`/`_rQ`/`_rTest`. They are words of the Rabin root finder. A shared
     "factor check" word with rsa's `rsa_fS`/`_fQ`/`_fTest` is optional.
   - Notes items 4 and 7 asked the worker to cite where a lemma is public. It did so where it
     could, except for E1 and E2. Its citation of core `List.findSome?_guard`/`map_findSome?` in
     `rabin_rbFind_eq`, instead of copying `rsa_findSome?_ite`, is confirmed.

6. **note: the route departures are sound.**
   - **`rabinCollection_sampleClose` / `rabinBlumTrapdoor_sampleClose`: `δ n = 1` for `n < 3`
     (P3).**
     - The `n < 3` branch is `rabin_statClose_one`, by P3 `statClose_iff`, since any two
       probabilities lie in `[0, 1]`.
     - For `n ≥ 3`, S3 needs `Nat.size (pq) ≤ B(n) = 2(n + 2)` (`eval_rsaBlock`). The modulus has
       `Nat.size (pq) ≤ 2·max(n, 3)` (`rabin_size_le`), which is `≤ 2(n + 2)` for every `n ≥ 1`.
       So the branch is really needed only at `n = 0`, where `6 > 4 = B(0)`. Using it at `1`
       and `2` as well, as the brief directs, is harmless.
     - δ is negligible: `exp_neg_le_half_pow`, `Negligible.mono` from 3 (`rabin_negligible_delta`).
     - The Blum branch adds `pushesUniform_sqTo` (odd `p ≠ q`) with `statClose_of_pushesUniform`
       and `StatClose.trans`, at cost 0.
   - **`blumFactorProb_le`: `1/(64n²)` from `hD`.**
     - With `P = |Π_n|`, `B = |BlumPrimes n|`:
       `Pr[E] ≥ (B/P)² − (1/P)(B/P) = B(B−1)/P²`
       (`HardcoreBit.uprob_prod_and`, `OneWay.uprob_and_le_mul`, `rabin_uprob_val_eq_le`).
     - `hD n` (`n ≥ 6 ≥ 2`) gives `2^n ≤ 4nB`.
     - `10n < 2^n` gives `B ≥ 2`: otherwise `2^n ≤ 8n`.
     - `P ≤ 2^n` (`rabin_card_primes_le`).
     - Then `P² ≤ 4^n ≤ 16n²B² ≤ 64n²B(B−1)`, because `16B² ≤ 64B(B−1)` iff `B ≥ 4/3`. The
       algebra is `hkey` (`64n²B(B−1) − 16n²B² = 16n²B(3B − 4) ≥ 0`).
     - **`BlumDensity` is used only as the hypothesis `hD`.** It appears here, in `rabin_card_blum`
       (the pair law's density `2^n ≤ 4n|C|`, through `Equiv.subtypeSubtypeEquivSubtypeInter`) and
       in the theorems that thread it. Nothing tries to prove it, as the user ruled.
   - **`oddFactorProb_le`: `1 − 3/|Π_n|` with the diagonal included.** This replaces the frozen
     sketch's `2/|Π_n|`, which ignored `p = q` on the product. `|Π_n| ≥ 6` for `n ≥ 6`
     (`two_pow_le_two_mul_card_primes`, `10n < 2^n`) gives `Pr[E] ≥ 1/2`. Sound; it is a Correction
     target, and the sketch was rewritten.
   - **Generators (`rabin_genCore_eq`).**
     - The test decides `v.Prime ∧ P v` on every word, as brief step 5 requires.
       `rabin_oddAcc_spec` uses `Nat.Prime.eq_two_or_odd`, and `rabin_blumAcc_spec` the
       residue `v % 4`. Both read the remainder through `divModStr_pairEncode` at the width
       of the modulus word, so `≥ 1` and `≥ 3` are exact.
     - The validity test reduces to `p ≠ q`, which is exact for fixed-width numerals.
     - The fallback words `⟦3⟧`, `⟦5⟧`/`⟦7⟧` (length ≤ 3 ≤ m) are padded to `m` bits.
   - **`rabinFactorRaw` (`rabin_fOut_eq`).**
     - Every residue is computed modulo `W' = 0^{|K|} ++ N`, where `|K| = 1 + 2|z| + 2|x|`. So
       `modExpStr`, `divModStr`, `addStr`, `subStr` and `xgcdStr` read back exactly
       (`listToNat_natToList`), also when `N = 0`.
     - The test `z² mod N = x² mod N` is two `H.le` comparisons.
     - `d = ((x + N) ∸ (z mod N)) mod N` equals `((x : Z_N) − z).val`. The proof is
       `Nat.cast_sub`; when `N = 0`, the test forces `z = x`.
     - The low `n` bits are taken by `(⟦0⟧_n ++ g).drop |g|`, which is the brief's correction.
   - **`blumInvRaw`/`rabinRootRaw`.** The CRT word `rabin_crtW` is computed at padded widths, and
     the degenerate moduli `0` give `d ≤ 1` (`rabin_val_inv_zero_le`). It reads as `blumInvNat`
     (`rabin_listToNat_crtW`) and is truncated to `|y|` bits (`rabin_trunc_eq`). The root finder's
     cofactor `⟦N / s⟧` is exact since `N / s ≤ N`, and `s (N / s) = N` is tested by two `H.le`.
   - **The pair law and error accounting.**
     - `rabin_pairLaw`: `StatClose.prod` of two `rabin_statClose_sampler`s (each
       `(1 − 1/(4n))^{4n·n} ≤ e^{-n}`), `.map` through the selection, then
       `rabin_statClose_diag` (`1/|C| ≤ 4n/2^n`). The total is `2e^{-n} + 4n/2^n`.
     - `rabin_uexp_le` moves an index-dependent average along a close law by the uniform-family
       device (`Equiv.piSplitAt`).
     - `rabin_core` gives `2F + 2e^{-n}`.
     - So the totals are `2·factorProb + 4e^{-n} + 4n/2^n = 2·factorProb + rabinErr n`, exactly
       the statements.
     - `blumFactorProb_le_invProbAt` uses the law in the other direction (`hlaw.symm` in
       `rabin_blum_uexp`).

7. **note: rule 10 holds under this review's seal.**
   - **Collection** (`probe/Collect.lean`, `collect.log`, `collect-summary.txt`; re-run in full
     after the restart). The probe ran over 336 own constants: the 19 targets, the `rabin_`
     family and their auxiliaries, excluding the base `rabin_symmetry`. It collected the
     other-module, non-reducible, non-instance TCSlib definitions in the elaborated types and
     values: 55 names (narrow). The wide pass adds statements of used constants and bodies of
     used own definitions, transitively: 58 names. It adds `NUPPT.Uniform`, `coinsCongr` and
     `ofPolyTime`.
     - Foreign matchers: `polyTimeComputable_iterateFind.match_1` (read by `split` in
       `rabin_rbLoop_poly`, as in rsa), and `PolyExpr.eval.match_1` (left with `eval`).
     - None of the 58 is `@[simp]`.
   - **The worker's list** (58 names) is this review's 58, minus `PolyExpr.eval`, plus
     `instDecidablePredUnitsZModMemSubgroupQROfNeZeroNat` (an instance, which this collector
     does not seal). It is equivalent and slightly stricter. It left `eval` unsealed per Q1.
   - **Not sealable** (reducible, notation under policy §1):
     - `NUPPT.Coins`, `.coins`, `.adv`, `.advice`, `DistinctPrimes`, `Primes`;
     - the `Collection` projections, `PermCollection.toCollection` and
       `TrapdoorCollection.toPermCollection`.
   - **Result.** In the whole-file sealed copy with 57 names (`seal/RevSealedRabin.lean`/`.out`,
     9 s), all 19 targets, all 178 helpers and every other base proof elaborate, `rabin_symmetry`
     and the structure fields included. **The only errors are the base proofs
     `rabinCollection_index` and `rabinBlumTrapdoor_index`.** Each reads `Collection.index` and
     `NUPPT.runAt` through `show`, as fac's and rsa's `_index` did. They are not rabin's to edit
     and go on the base re-point list. The re-point is
     `rw [Collection.index_eq]` followed by
     `exact (congrArg pairFstD (oddGen_runAt H n r)).trans (pairFstD_pairEncode _ _)`
     (likewise with `blumGen_runAt`). Sealed with both re-points, the whole file has 0 errors
     and 0 warnings (`seal/RevSealedRepoint.lean`/`.out`).
   - **Controls** (`seal/RevControl.lean`/`.out`): the unsealed block passes, and the sealed
     block errs at each of C1–C12 and at Q1b only. The readings are:
     - C1 `natToList` by its body;
     - C2 `NUPPT.inParam` by `rfl`;
     - C3 `rejectBlocksL` by its body;
     - C4 `StatClose` by `Iff.rfl`;
     - C5 `Collection.index` by `rfl`;
     - C6 `polyTimeComputable_iterateFind.match_1` against a local `match`;
     - C7 `listToNat` by its body;
     - C8 `PushesUniform` by `Iff.rfl`;
     - C9 `sqTo` by `rfl`;
     - C10 `unitSampleStr` by its body;
     - C11 `sampleUnitL` by its body;
     - C12 `FactoringAssumption` by `Iff.rfl`.

     **Ruling Q1 confirmed:** `rabinTrials.eval n = 4n²` by `rfl` closes under the 57-name seal
     (Q1a) and fails once `eval` is added (Q1b). The fill reads `eval` that way in
     `rabin_genCore_eq`, `rabin_genIndex` and `rabin_genCoins_len`.
   - **Grep** (`tools/grepforeign.py`, `grep-foreign.txt`). The added code has 409 rewrite/simp
     lists and 49 `unfold`s. There are 10 lexical hits, none a rule:
     - terms inside `show … by` (lines 985–986, 2782);
     - arguments of `← h1 (NUPPT.inParam z).length` (1019, 1026);
     - the bound variables `p`, `q` of `dvd_mul_right p q` (2959, 2963).

     Every `unfold` names an own-file definition. Core and Mathlib reductions occur only in
     `rfl`/`show`/`change`, as the REPORT lists.
   - The REPORT's three seal-driven repairs (`statClose_iff`, `pushesUniform_iff`,
     `listToNat_eq`) are confirmed in patch 12.

8. **note: the toolchain.**
   - **What the worker did.** It could not resolve `release.lean-lang.org`, so it linked the
     official GitHub release archive `lean-4.25.0-linux.zip` (tag `v4.25.0`) with
     `elan toolchain link`.
   - **The evidence records no `lean --version` line** (not in `preflight.log`, `bootstrap.log`
     or `cache-probe.log`). The match with ours is shown indirectly:
     - The worker's narrowed Mathlib cache loaded: the cache probe is rc 0, and 71 + 21 modules
       bootstrapped against it.
     - Lean refuses `.olean` files written by a build with another commit hash. Ours is
       `Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)`.
       So the worker's binary is the official v4.25.0 build.
     - This review's own replay on that toolchain reproduces every result.
   - The toolchain has no bearing on the verdict. For later dispatches, ask for `lean --version`
     in `preflight.log`.

9. **nit: REPORT accuracy and style.**
   - **Accurate:** the targets and routes, the 178 helpers by role, D11 (fields `prime`,
     `divMod`, `le`, `mul`, `sub`, `add`, `modExp`, `xgcd`; no missing operation), the freeze
     result, the seal result and its two base failures, the lint lines, the sweep tail and the
     elaboration-cost note.
     - The REPORT's finding 1, a second unification trap (`fun v => v.Prime ∧ (· ≠ 2) v`
       against `fun v => v.Prime ∧ v ≠ 2` unfolding `rejectBlocksL`), is worth adding to notes
       item 7.
     - The axiom table is right for the issue base: there rsa's `unitSampleStr` and S3 were
       sorried, so 11 targets carried `sorryAx`. On the landing context only 8 do, through
       `statClose_rejectBlocksL` alone.
   - **Incomplete:** the duplication list (finding 4) and request 5 (finding 2).
   - **Style:**
     - The head has 283 lines over 100 characters; the base has 33. Most are one-line docstrings
       of private helpers (for example `rabin_rbLoop`, `rabin_rbFind_eq`). Policy sets no limit;
       E3 reflows the docstrings it touches.
     - `rabin_pairLaw`'s docstring has no separate **Proof sketch** paragraph (it is under the
       lint's threshold).
   - **Records:** `preship/probes/SorrySources.lean` is again absent, so the worker used the
     review's `#review_sorry` method, as in rsa.

10. **note: file size.** `Rabin.lean` is 3809 lines (1150 at the base), 3814 with E1–E3.
    This is the approved exception (D2): noted only, not split.

## Landing edits (exact)

The diff is `$SP/review-rabin/edits/landing-edits.diff`:
- it touches only `TCSlib/Cryptography/Candidates/Rabin.lean`;
- `git apply --check` is clean on the delivered `src/`;
- applying it reproduces `edits/RabinEdited.lean` byte for byte;
- the generator is `edits/apply_edits.py`.

It is applied on **`land/rabin-review` as commit `01402b335b950cfbc9b2897e051fdc104d1fb0ca`**
(parent `ffd58919`, the 12 delivery patches on `816329e5`).

- **E1** (finding 1). Delete `rabin_appendEquiv` (10 lines). Replace its six uses by
  `(Fin.appendEquiv _ _)`. End the docstrings of `rabin_fCoinsEquiv` and `rabin_genCoinsEquiv`
  with "(Mathlib's `Fin.appendEquiv`, then the length cast)".
- **E2** (finding 2). `rabin_pushesUniform_prod` keeps its statement. Its body becomes
  `(h.prodMap HardcoreBit.pushesUniform_id).uprob_eq fun w => P w.1 w.2`, and its docstring cites
  `PushesUniform.prodMap`, `pushesUniform_id` and `PushesUniform.uprob_eq`.
- **E3** (finding 3; docstrings only). It replaces the **Proof sketch** paragraphs of
  `polyTimeComputable_oddGenRaw`, `rabinSampler_spec` and `blumSampler_spec`. It drops "on the
  last two bits" from `polyTimeComputable_blumGenRaw`'s lead, splits `blumFactorProb_le`'s
  chain as `Pr_{Π_n × Π_n}[E] − Pr_{Π_n × Π_n}[E ∧ p = q]`, and names P2 in
  `blumFactoring_of_rabinBlum_oneWay`. The new sketch of `polyTimeComputable_oddGenRaw`:

  ```
  **Proof sketch.** The generator equals the string computation `rabin_genCore` with the test
  `rabin_oddAcc` ("prime, and the residue modulo `2` (`H.divMod` by `⟦2⟧`) reads `≥ 1`", which
  decides `p.Prime ∧ p ≠ 2` on every word, `Nat.Prime.eq_two_or_odd`) and the fallback words `⟦3⟧`,
  `⟦5⟧` (`rabin_genCore_eq`). That computation is polynomial-time (`rabin_genCore_poly`):
  `1^{max n 3}` by `polyTimeComputable_lenLe`/`_ite`; the coins are cut at `1^{4m³}`
  (`polyTimeComputable_pairTakePoly`/`_pairDropPoly rabinPrimeCoins`); each prime is the block
  loop over the repetition host `Complexity.polyTimeComputable_iterateFind` (`rabin_spOut_poly`),
  its fallback zero-padded to `m` bits by `H.sub` and `H.add` (the width `m` varies, so it is not a
  constant word); the validity test is `polyTimeComputable_pairEq` on the two numerals alone, since
  both are always primes of the class below `2^m` (`rabin_samplePrimePL_spec`); `N` by `H.mul`. -/
  ```

**Re-run on `01402b33`:**
- **Elaboration** (`edits/module-checks-edited.log`): `Rabin` rc 0, 0 errors and 0 warnings
  (10 s); facade rc 0; `Checks` rc 0 (148 s).
- **Axioms** (`edits/axioms-edited.log`): identical to the head. 11 targets are standard; 8 have
  the single source `statClose_rejectBlocksL`; sweeps 8/173, 5/158, 0/70.
- **Seal** (`edits/RabinEditedSealed.out`): only the two base `_index` proofs fail.
- **Freeze** (`edits/declfreeze-edited.log`): headers identical, the 19 targets filled, no other
  base body changed, 177 new declarations, all private `rabin_`. Docstring changes are the
  worker's 14 plus E3's four (`polyTimeComputable_oddGenRaw`, `rabinSampler_spec`,
  `blumSampler_spec`, `blumFactoring_of_rabinBlum_oneWay`).
- **Lint:** `style_lint.py` reports only the size line (3814). The campaign lint has no Rabin
  FAIL and the same 25 check-8 names.

**D1** (findings 4 and 5; ledger, no code). Add a row DL-29 for the rabin fill:
- the copies of finding 5, with their H1 and H2 homes;
- the undisclosed near-copies of finding 4: `rabin_statClose_one` = `dla_statClose_one`,
  `rabin_listToNat_mulStr`, `rabin_prime_poly`, `rabin_rS`/`_rQ`/`_rTest`, the fourth loop copy
  (dl-c) and `hnum`/`fac_natToList_mod`;
- the base re-point list: `rabinCollection_index` and `rabinBlumTrapdoor_index` (finding 7),
  beside fac's `factoringCollection_index` and rsa's `rsaCollection_index`;
- the REPORT's requests:
  - 1 (H2), 2 and 3 (H1): endorsed;
  - 4: endorsed as `Sampling.lean`'s `uexp_le_of_statClose`;
  - 5: withdrawn (E2).

## Not verified

- **The full 94-module sweep was not rerun.** This review checked `Rabin`, the facade and
  `Checks` on the landing context, and the 11-module chain `Concrete`…`Rabin` with dl-a's
  `Concrete.lean`.
- **Bare `simp`/`simpa` calls were not run through `simp?`.** No foreign definition is `@[simp]`
  (collector: `simpUnfold=false` for all 58), so they cannot unfold one.
- **The near-duplicate search is textual.** It uses `difflib` similarity ≥ 0.75 against the
  private helpers of the five candidate files, plus targeted greps of the library. Semantic
  duplicates under different proofs may remain.
- **The worker's toolchain was not inspected directly** (finding 8).

## Logs (`$SP/review-rabin/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- **Delivery and replay:** `deliv/` (`git archive` of `1ac17982`), `am.log`, `am-land.log`,
  `rabin.diff`, `removed-lines.txt`, `Rabin.base.lean`, `Rabin.head.lean`.
- **Freeze:** `tools/declfreeze_rev.py`, `declfreeze-rev.log`, `declfreeze-docdiff.log`,
  `filled.txt`.
- **Elaboration:** `run-checks.sh`, `olean-orig.sha`, `olean-verify.log`, `module-checks.log`.
- **Axioms:** `probe/Axioms.lean`, `probe/run1.sh`, `axioms.log`, `axioms-summary.txt`,
  `integration-dl.log`, `integration-dl-axioms.log`, `integration-dl-axioms-summary.txt`.
- **Rule 10:**
  - `probe/Collect.lean`, `collect.log`, `collect-summary.txt`;
  - `seal/narrow.txt`, `seal/wide-all.txt`, `seal/wide-rows.txt`, `seal/rev-sealed-names.txt`
    (57);
  - `seal/mkseal.py`;
  - `seal/RevSealedRabin.lean`/`.out`, `seal/RevSealedRepoint.lean`/`.out`;
  - `seal/RevControl.lean`/`.out`;
  - `tools/grepforeign.py`, `grep-foreign.txt`.
- **Duplication:** `tools/neardup.py`, `neardup.log`, `cmp/` (the comparison sources at
  `816329e5` and `b76e614d`).
- **Lint:** `style-lint-head.log`, `campaign-lint-head.log`.
- **`edits/`:**
  - `landing-edits.diff`, `apply_edits.py`, `RabinEdited.lean`;
  - `RabinEditedSealed.lean`/`.out`;
  - `module-checks-edited.log`, `axioms-edited.log`, `axioms-edited-summary.txt`;
  - `declfreeze-edited.log`, `style-lint-edited.log`, `campaign-lint-edited.log`.

**Worktrees and records:**
- The issue-base worktree `$SP/wt-rev-rabin` was removed.
- `$SP/wt-rev-rabin2` (branch `land/rabin-review`, head `01402b33`) and the olean copy
  `$SP/rev-rabin-oleans` are kept. The copy now holds `Rabin.olean` for that head.
- The integration worktree and its olean copy were removed after their runs.
- `$SP/land-fac-oleans` was only read.
- The exchange checkout `$SP/wt-exchange` was only fetched by this review. Its HEAD moved at
  22:33 (a `pull --rebase` and the commit "Gate 07 round 3 staged"), by another agent.
- No TCSlib source outside `land/rabin-review` was changed, and nothing was pushed.
