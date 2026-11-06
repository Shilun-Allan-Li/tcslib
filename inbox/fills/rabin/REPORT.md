# Fill report: unit rabin (`TCSlib/Cryptography/Candidates/Rabin.lean`)

**Status: final. 19 of 19 targets filled; 0 partial; 0 escalated; no E-API, no E-RES.**
No statement changed; no `sorry` and no `axiom` added. The owned file checks with 0 errors,
0 `sorry` warnings and 0 other warnings. Every target passes D3 (below).

## Base, environment, preflight

- **Base:** `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (`git rev-parse`), fetched from
  `cryptography/pass-shelat-ch2-4-eqlemmas`. Local branch `fill/rabin`, head
  `8295c2054dc27b7757353b1c091b8ed1b81e0100` (12 commits). It was never pushed and never rebased.
- **Exchange commit read at start:** `22e3c69`, a descendant of `fe9b979c46c63d083e5e004ad91c0c3dec3edead`.
  I read the brief, the addendum v1 and `NOTES-2026-11-07.md`. Items 4 and 7 of the notes were
  applied (see Rule 10, Duplication and Findings).
- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4.
  - The memory cgroup is v1 with `memory.limit_in_bytes = 9223372036854771712` (no limit), so
    the headroom is `MemAvailable` = 15.39 GiB (floor 4 GiB).
  - The clone's filesystem is `/dev/vda` (ext4) with 29.40 GiB free (floor 12 GiB). No tmpfs
    was used.
  - **PASS.**
- **Toolchain:** Lean 4.25.0.
  - `release.lean-lang.org` does not resolve from this host, so `elan` could not fetch the
    toolchain.
  - I downloaded the official archive `lean-4.25.0-linux.zip` from
    `github.com/leanprover/lean4/releases/tag/v4.25.0` into `/workspace/toolchain` (ext4) and
    registered it with `elan toolchain link`.
  - After this, the disk had 26.8 GiB free (re-check floor 8 GiB).
- **Cache:**
  - **Store** (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` did not exist (0
    archives), so every archive was downloaded by this session.
  - **Fetch** (`evidence/logs/cache-get.log`): the narrowed fetch of the 75 roots in
    `evidence/logs/mathlib-roots.txt` (identical to `inputs/rabin/roots.txt`).
    "Attempting to download 2344 file(s)", "Decompressing 2344 file(s)", exit 0, no failed
    download.
  - **Packages** (`evidence/logs/packages-check.log`): "RESULT: PASS: every present package
    matches the manifest; absent: doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean". No module of the
    order list imports an absent package.
  - **Checks:** no zero-size olean. The cache probe (`import Mathlib.Algebra.BigOperators.Field`)
    returned rc 0.
- **Bootstrap** (`evidence/logs/bootstrap.log`, then `bootstrap-rest.log`):
  - first the 71 modules of `order.txt` that `Rabin.lean` imports, in order, all rc 0;
  - before the sweep, the remaining 21 modules (73–93 of the list), all rc 0.
  - The base owned file gave rc 0 with exactly the 19 `sorry` warnings
    (`evidence/logs/base-owned-check.log`).
- **How checks ran:** one Lean process at a time. Never `lake build`; never an unfiltered
  `lake exe cache get`.
  - Module checks used `scripts/lean_check_tree.sh` through `evidence/chk.py`, which logs start,
    end, wall time and child max RSS, because `/usr/bin/time` is absent.
  - The owned module takes 11–14 s and at most 3.1 GB. Its checks are listed in
    `evidence/logs/module-checks.log`.
  - Scratch probes were elaborated with plain `lean` against the same tree (`evidence/probes/probe.sh`).
- **Note:** the clone's `AGENTS.md` says not to run Lean from the shell. Following the user's
  instruction (only the brief, the addendum and the notes are instructions), I used the brief's
  `scripts/lean_check_tree.sh`.

## Targets (brief order)

| # | Target | State | Route |
|---|---|---|---|
| 1 | `rabinSampler_spec` | filled | As sketched: activation `rabin_sampler_runAt` (`NUPPT.runAtL_ofPolyTimeUniform`, P5), `rabin_dec_unitSampleStr` (`unitSampleStr_eq`, `listToNat_rabinIndexOf`, `sampleUnitL_spec` or the fallback), canonical decoding `rabin_enc_of_dec`, `rabinEval_spec`. |
| 1 | `blumSampler_spec` | filled | Activation `rabin_blumSampler_runAt` (`modExpStr_pairEncode`); the generated index is `BlumValid` (`rabin_blumValid_indexOf`); `v² mod N` is coprime to `N`; QR membership as the square of `unitOfCoprime v`; `blumEval_spec`. |
| 2 | `blumInv_spec` | filled | Brief's **Route**, without reading `blumSqrt`. `rabin_blumInvNat_spec`: the CRT unit `crtUnits⁻¹(y_p^{p/4+1}, y_q^{q/4+1})` is a residue root whose residue is `blumInvNat p q y.val` (`ZMod.coe_mul_inv_eq_one`, `crtUnits_fst`/`_snd`, injectivity of `ZMod.chineseRemainder`). Then `Equiv.symm_apply_eq` on `blumPermAt`. Proof sketch rewritten. |
| 3 | `rabinCollection_sampleClose` | filled | `δ n = 1` for `n < 3` (P3 `statClose_iff`), `e^{-n}` otherwise. S3 at `N = pq` (`Nat.size (pq) ≤ 2·max(n,3) ≤ B(n)` for `n ≥ 1`) mapped through `rabinDec` (`rabin_statClose_dec`); coins by `NUPPT.coinsEquivPoly`, domain by `rabinCollection_domEquiv`. Docstring expanded. |
| 3 | `rabinBlumTrapdoor_sampleClose` | filled | S3 mapped through `v ↦ blumDec ⟦v² mod N⟧`, then `pushesUniform_sqTo`, `statClose_of_pushesUniform`, `StatClose.trans` (`rabin_statClose_blumDec`). Docstring expanded. |
| 4 | `oddFactorProb_le` | filled | Brief's **Correction**: `OneWay.uprob_eq_one_div_card`, `factorProb_eq`. Conditioning bound `rabin_uprob_subtype_le` (from `uprob_subtype_prod_eq`, `uprob_and_eq_mul_subtype`). `Pr[both odd] ≥ 1 − 3/\|Π_n\| ≥ 1/2`, with the diagonal included, since `\|Π_n\| ≥ 6` for `n ≥ 6`. Proof sketch rewritten. |
| 4 | `blumFactorProb_le` | filled | `Pr[E] ≥ (B/P)² − (1/P)(B/P) = B(B−1)/P² ≥ 1/(64n²)` from `hD`, `10n < 2^n` and `P ≤ 2^n` (`HardcoreBit.uprob_prod_and`, `OneWay.uprob_and_le_mul`). Proof sketch rewritten. |
| 5 | `polyTimeComputable_oddGenRaw` | filled | `rabinGenRaw = rabin_genCore` (`rabin_genCore_eq`), polynomial-time by `rabin_genCore_poly`. The restricted prime loop is the generic block loop over `Complexity.polyTimeComputable_iterateFind` (`rabin_spOut_poly`, `rabin_rbFind_eq`). The test `rabin_oddAcc` (`H.prime`; parity by `H.divMod` by `⟦2⟧`, then `H.le`) decides `v.Prime ∧ v ≠ 2` on every word. The sketch was kept; its deviations are listed below. |
| 5 | `polyTimeComputable_blumGenRaw` | filled | Same helpers, test `rabin_blumAcc` (residue mod 4 by `H.divMod`, then `H.le`). Short docstring expanded into a Proof sketch. |
| 6 | `polyTimeComputable_rabinFactorRaw` | filled | Brief's **Correction**: string computation `rabin_fOut` (`rabin_fOut_eq`, `rabin_fOut_poly`). Every residue is computed modulo the modulus word with leading zeros, so all numerals read back exactly, also for the degenerate `N = 0`. `(x − z) mod N = ((x + N) ∸ (z mod N)) mod N`. The low `n` bits are `(⟦0⟧_n ++ g).drop \|g\|`, not `pairTakePoly var`. P9. Proof sketch rewritten. |
| 7 | `polyTimeComputable_blumInvRaw` | filled | Exact CRT word `rabin_crtW` (`rabin_listToNat_crtW`), truncated to the width of `y` (`rabin_trunc`). Short docstring expanded. |
| 7 | `polyTimeComputable_rabinRootRaw` | filled | `rabin_rOut`: cofactor by `H.divMod`; test `p'q' = N` by `H.mul` and two `H.le` (the widths differ, so not `pairEq`); the CRT word. Short docstring expanded. |
| 8 | `rabinCollection_invProbAt_le` | filled | See "The reductions". Proof sketch rewritten (a **Correction** target). |
| 8 | `rabinBlumTrapdoor_invProbAt_le` | filled | See "The reductions". Proof sketch rewritten. |
| 8 | `blumFactorProb_le_invProbAt` | filled | See "The reductions". Proof sketch rewritten. |
| 9 | `blumFactoring_of_factoring` | filled | As sketched (P14, `blumFactorProb_le`, `Negligible.mul_pow`, `.const_mul`, `.mono` from 6). Short docstring expanded. |
| 9 | `rabinCollection_oneWay` | filled | As sketched (P14; `rabinCollection_invProbAt_le` + `oddFactorProb_le`, threshold 6; `Collection.invProbAt_nonneg`). |
| 9 | `rabinBlumTrapdoor_oneWay` | filled | P2 `TrapdoorCollection.oneWay_iff`; `rabinBlumTrapdoor_invProbAt_le`, `blumFactoring_of_factoring`. Short docstring expanded. |
| 9 | `blumFactoring_of_rabinBlum_oneWay` | filled | As sketched (P2; `blumFactorProb_le_invProbAt`, `negligible_rabinErr`, `uprob_nonneg`). |

### The reductions (step 8)

The three bounds share one structure, and their error is exactly `rabinErr n`.

1. **Generator's law first.** The generator's coins split into the two prime segments
   (`rabin_genCoinsEquiv`, `HardcoreBit.uexp_comp_equiv`). The index is `⟦pq⟧_{2n}` for the
   selection `rabin_X P z0` of the two restricted samplers' values (`rabin_genIndex`,
   `rabin_genParams_pq`, `rabin_zOf_pq`). The fallback pair is `z0 = (3,5)` or `(3,7)`.
2. **The pair law**, `rabin_pairLaw`: the private helper generic in `P` that the brief asks for.
   - **Statement.** The selection is within `2e^{-n} + 4n/2^n` of the uniform distinct class
     pair, given the density `2^n ≤ 4n·|C|`.
   - **One sampler.** Each sampler is `statClose_rejectBlocksL` with the class test
     (`rabin_statClose_sampler`).
   - **Combination.** `StatClose.prod`, then `StatClose.map` through the selection, then the
     diagonal `rabin_statClose_diag` (`1/|C| ≤ 4n/2^n`).
   - **Density by class.** For odd primes, `rabin_card_odd` (from
     `two_pow_le_two_mul_card_primes`). For Blum primes, `rabin_card_blum` (from `hD`, by
     `Equiv.subtypeSubtypeEquivSubtypeInter`).
3. **Transfer of the average.** The inversion probability at an index is a probability over
   coins that depend on the index. Its average along the generator's law is moved to the
   uniform pair by `rabin_uexp_le`, the uniform-family device of the rsa fill (`Equiv.piSplitAt`,
   `uprob_fst`, `StatClose.abs_uprob_sub_le_prod`).
4. **At the ideal pair, the core lemma `rabin_core`.** Its four steps are:
   - the symmetry lemma `rabin_symmetry`;
   - `gcd_sub_eq_prime_of_sq_eq_sq`;
   - `rabinFactorStep` outputs the factor;
   - S3 for the unit of `A'` (cost `e^{-n}`, paid twice through the factor 2). The coins of
     `A'` split as `rabin_fCoinsEquiv` with `rabinFactorer_runAt`.
5. **The collections enter the core in different ways.**
   - **Odd** (`rabin_inner_odd`): the decoder is transported to `Z_{pq}^*` along
     `rabin_unitsCongr`, which is `ZMod.ringEquivCongr` on units.
   - **Blum** (`rabin_inner_blum`): `y ∈ QR_N` is reparametrized by `w = y²` (`blumPermAt`),
     and `w = r²` for a uniform unit `r` (`pushesUniform_sqTo`, `rabin_pushesUniform_prod`).
   - **Factorer to inverter** (`rabin_inner_inv`): whenever `A` factors, the root finder
     inverts every `y` (`rabin_blumInvNat_spec` with the factor order `(p,q)` or `(q,p)`).
6. **Error accounting.** The ideal side is `2 F + 2e^{-n}`, where `F` averages to
   `oddFactorProb`/`blumFactorProb` (`uprob_prod`). The generator adds `2e^{-n} + 4n/2^n`. The
   total is `rabinErr n`. `blumFactorProb_le_invProbAt` uses the pair law in the other direction
   (`rabin_blum_uexp`).

## New private declarations (178, all `private`, all `rabin_`-prefixed; no new public declaration)

By role. The full list is in `evidence/logs/declfreeze.log` and in the source.

- **Samplers:**
  - `rabin_one_mod_spec`, `rabin_getD_spec`, `rabin_sampler_runAt`, `rabin_blumSampler_runAt`;
  - `rabin_enc_of_dec`, `rabin_blumEnc_of_dec`, `rabin_N_pos`, `rabin_rabinMod_indexOf`;
  - `rabin_unitSampleStr_indexOf`, `rabin_dec_unitSampleStr`;
  - `rabin_blumValid_indexOf`, `rabin_blumMod_indexOf`.
- **Inverter:** `rabin_blumInvNat_cast_left`/`_right`, `rabin_blumInvNat_spec`, `rabin_blumInv_runAt`.
- **Closeness:**
  - `rabin_coins_sampler`, `rabin_coins_blumSampler`, `rabin_statClose_one`, `rabin_size_le`;
  - `rabin_negligible_delta`, `rabin_statClose_dec`, `rabin_pushesUniform_sqTo`,
    `rabin_statClose_blumDec`.
- **Conditioning (step 4):**
  - `rabin_uprob_subtype_le`, `rabin_uprob_distinct_ge`, `rabin_uprob_val_eq_le`;
  - `rabin_uprob_diag_le`, `rabin_uprob_snd_val_eq_le`, `rabin_ten_mul_lt_two_pow`;
  - `rabin_six_le_card_primes`, `rabin_card_primes_le`, `rabin_uprob_blum`.
- **Block loop.** The generic helper is `rabin_spOut_poly`, which uses `rabin_rbFind_eq`.
  - Combinator and search: `rabin_comp`, `rabin_find?_range_lt`.
  - Loop data `rabin_rbStep`, `_rbBlock`, `_rbAcc`, `_rbOut`, `_rbLoop`. These are data for
    the public host; no new host.
  - Their `_poly` lemmas, `rabin_rbStep_iterate`, `rabin_length_rbStep_*`, `rabin_rbLoop_poly`,
    `rabin_rbFind_eq`.
  - Padding and the sampler: `rabin_pad`, `_pad_eq`, `_pad_poly`, `rabin_spStart`,
    `rabin_spOut`, `_spOut_eq`, `_spOut_poly`.
- **Generators:**
  - `rabin_listToNat_one`/`two`/`three`/`four`/`five`/`seven`;
  - `rabin_le_poly`, `rabin_prime_poly`, `rabin_mod_poly`;
  - `rabin_oddAcc`, `rabin_blumAcc` and their `_poly`/`_spec`;
  - the words `rabin_gU`, `_gC1`, `_gC2`, `_gP`, `_gQ`, `_gValid`, `_gA`, `_gB`,
    `_genCore` and their `_poly` lemmas;
  - `rabin_gU_eq`, `rabin_samplePrimePL_spec`, `rabin_genCore_eq`.
- **`A'`:**
  - `rabin_listToNat_append`, `_zeros_append`, `rabin_drop_zeros_append`, `rabin_mod_lt_two_pow`;
  - the words `rabin_fC1`, `_fC2`, `_fX`, `_fY`, `_fZ`, `_fK`, `_fW`, `_fSq`, `_fTest`, `_fD`,
    `_fG`, `_fOut`;
  - `rabin_fOut_poly`, `rabin_fOut_eq`.
- **CRT words and the root finder:**
  - `rabin_val_inv_zero_le`, `rabin_listToNat_mulStr`, `rabin_zpad` (with `_listToNat_zpad`,
    `_length_zpad`, `_zpad_poly`);
  - `rabin_cE`, `_cPow`, `_cInv`, `_cTerm`, `_cSum`, `_crtW` and their `listToNat` lemmas,
    `rabin_crtW_poly`;
  - `rabin_trunc` (with `_eq`, `_poly`);
  - `rabin_rS`, `_rQ`, `_rTest`, `_rOut` (with `_eq`, `_poly`).
- **Reductions:**
  - `rabin_uexp_le`, `rabin_appendEquiv`, `rabin_coins_factorer`, `rabin_factorerCoins_len`;
  - `rabin_fCoinsEquiv` (with `_ofFn`), `rabin_F`, `rabin_core`;
  - `rabin_mkDP` (with `_p`, `_q`), `rabin_zOf`, `rabin_C`, `rabin_RDP`, `rabin_diagEquiv`;
  - `rabin_statClose_diag`, `rabin_uprob_C`, `rabin_statClose_sampler`, `rabin_X`, `rabin_pairLaw`;
  - `rabin_genCoins_len`, `rabin_genCoinsEquiv` (with `_ofFn`), `rabin_genParams_pq`,
    `rabin_zOf_pq`, `rabin_idx`, `rabin_genIndex`;
  - `rabin_unitsCongr` (with `_val`, `_symm_val`), `rabin_rabinF_idx`, `rabin_Qcoll`;
  - `rabin_inner_odd`, `rabin_card_odd`, `rabin_oddFactorProb_eq`, `rabin_z35`;
  - `rabin_pushesUniform_prod`, `rabin_blumValid_idx`, `rabin_inner_blum`, `rabin_card_blum`;
  - `rabin_blumFactorProb_eq`, `rabin_z37`, `rabin_coins_blumGen`, `rabin_blum_uexp`,
    `rabin_inner_inv`.

Every private proof longer than about 20 lines has a **Proof sketch.** (`style_lint.py`
reports no missing sketch).

### Duplication disclosure, and helpers close to existing lemmas (notes, item 4)

**Copies of other units' private proofs** (rsa's `RSA.lean` and dl-a's `DiscreteLog.lean`, in
their deliveries: not landed, not in my imports), re-proved under my prefix:

| Copy | Source | Size |
|---|---|---|
| `rabin_find?_range_lt` | `rsa_find?_range_lt` (itself dl-a's) | 18 lines |
| `rabin_rbStep`, `_rbBlock`, `_rbOut`, `_rbStep_poly`, `_rbBlock_poly`, `_rbStep_iterate`, `rabin_length_rbStep_*`, `_rbLoop`, `_rbLoop_poly` | the `rsa_us*` / `dla_ss*` loop family. Adapted: the header carries `1^B` and `1^k`, and the test `acc0` is a parameter | about 80 lines |
| `rabin_listToNat_append`, `rabin_listToNat_zeros_append`, `rabin_drop_zeros_append` | `rsa_listToNat_append`, `rsa_listToNat_zeros_append`, `rsa_drop_zeros_append` (the first re-proves the private `foldl_bits_eq` of `Asymptotic/Sampling.lean`) | 35 lines |
| `rabin_val_inv_zero_le`, `rabin_one_mod_spec`, `rabin_getD_spec`, `rabin_le_poly`, `rabin_listToNat_one`/`two`/`three` | `rsa_val_inv_zero_le`, `rsa_one_mod_spec`, `rsa_getD_spec`, `rsa_le_poly`, `rsa_listToNat_*` | about 40 lines |
| `rabin_appendEquiv` | `rsa_appendEquiv` | 10 lines |

**Same pattern, own proof:**
- `rabin_sampler_runAt`, `rabin_coins_sampler`, `rabin_dec_unitSampleStr`,
  `rabin_statClose_dec` and the proof of `rabinCollection_sampleClose` have the shape of their
  rsa counterparts (`rsa_sampler_runAt`, …, `rsaCollection_sampleClose`). The brief asked not to
  copy that proof. I wrote these for `rabinDec`/`RabinParams`, with the extra `n < 3` branch.
- `rabin_fCoinsEquiv_ofFn` and `rabin_genCoinsEquiv_ofFn` follow `rsa_genCoinsEquiv_ofFn`.
- `rabin_uexp_le` is a generic form of the device of `rsa_uprob_pi_eval`/`rsa_step_ii`.
- `rabin_mkDP`/`rabin_zOf` follow `rsa_zOf`.

**Near-duplicates of the library:**
- `rabin_comp` is the private `ptc_comp` of `Randomized/Closure.lean`.
- `rabin_enc_of_dec` and `rabin_blumEnc_of_dec` repeat the inline `encD_decD` proofs of
  `rabinCollection` and `rabinBlumTrapdoor` (own file); the definitions' blocks are frozen.
- `rabin_uprob_subtype_le` is derived from Concrete's `uprob_and_eq_mul_subtype` and
  `uprob_subtype_prod_eq`; it is the upper-bound form of `one_sub_div_le_uprob_subtype`.
- `rabin_pushesUniform_prod` is the product form of `PushesUniform.uprob_eq`.
- `rabin_statClose_one` is the trivial bound from `statClose_iff`.
- `rabin_unitsCongr` wraps Mathlib's `Units.mapEquiv` and `ZMod.ringEquivCongr`, with
  `ZMod.ringEquivCongr_val`.
- `rabin_card_primes_le` is `Fintype.card_subtype_le`.
- In `rabin_rbFind_eq` I avoided a copy of `rsa_findSome?_ite` by citing core's
  `List.findSome?_guard` and `List.map_findSome?`.

**Mathlib first.** The number theory is Mathlib's or TCSlib's published API:
- `Nat.Prime.eq_two_or_odd`, `ZMod.coe_mul_inv_eq_one`, `ZMod.chineseRemainder`,
  `Prod.fst_zmod_cast`, `ZMod.cast_natCast`, `ZMod.cast_eq_val`, `ZMod.val_natCast`;
- `ZMod.ringEquivCongr_val`, `Nat.size_le`, `Fintype.card_subtype_compl`, `Equiv.piSplitAt`;
- TCSlib's `crtUnits_*`, `mem_QR_mul_iff`, `sq_pow_div_four_succ`, `pow_div_four_succ_mem_QR`,
  `sq_crtUnits_symm`, `pushesUniform_sqTo` and `gcd_sub_eq_prime_of_sq_eq_sq`.

### Requested shared lemmas

1. **A public `polyTimeComputable_rejectBlocksL`** for a polynomial-time test, as the brief
   anticipates. `rabin_spOut_poly` with `rabin_rbFind_eq`/`rabin_spOut_eq` is a generic version
   (`k = B`, `T = 4m²`, padded output). rsa (`rsa_us*`) and dl-a (`dla_ss*`) build the same loop.
2. **`listToNat_append`, leading zeros, the truncation `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`, and
   zero padding** (`rabin_pad`), beside `listToNat`/`natToList`. This repeats rsa's request.
3. **A public applied-form composition** `PolyTimeComputable.comp'`. This repeats rsa's
   request.
4. **`rabin_uexp_le`.** The average of `c ↦ Pr[Q c]` along `StatClose` laws, with
   index-dependent coins. It belongs in `Asymptotic/Sampling.lean`, and it is also what rsa's
   `rsa_step_ii` needed.
5. **`rabin_pushesUniform_prod`**, next to `PushesUniform.uprob_eq`.

## Rule 10

- **Seal** (`evidence/seal/RabinSealed.lean`, `evidence/logs/seal-main.log`). The 58 sealed
  names are in `evidence/seal/seal-list.txt`.
  - **How the list was built.** A probe over the elaborated module (`evidence/probes/ForeignDefs.lean`,
    output `evidence/seal/foreign-defs-by-decl.txt`) lists, for every declaration of the
    module, private ones included, the definitions of other TCSlib modules that occur in its
    type or value. The seal is the union over all declarations, minus the names below.
  - It includes the compiler-generated matcher `Complexity.polyTimeComputable_iterateFind.match_1`,
    which `rabin_rbLoop_poly` reads by `split`, as rsa's `rsa_usLoop_poly` does.
  - It includes the bundle string functions (`modExpStr`, `xgcdStr`, `divModStr`, `addStr`,
    `subStr`, `mulStr`, `leStr`, `primeStr`), and `rejectBlocksL`, `sampleUnitL`,
    `unitSampleStr`, `listToNat`, `natToList`, `natToBits`, `crtUnits`, `QR`, `sqTo`, `uprob`,
    `uexp`, `StatClose`, `PushesUniform`, the `NUPPT` layout functions, `Collection.index`/
    `invProbAt`/`SampleClose` and `FactoringAssumption`.
  - No foreign definition is `@[simp]`, so no `[-simp]` was needed.
- **Result.** All 19 filled bodies and all 178 `rabin_` helpers elaborate sealed. The only two
  errors are in frozen base proofs, not in targets:
  - `rabinCollection_index` and `rabinBlumTrapdoor_index` both use `show` through
    `Collection.index`/`NUPPT.runAt`. I use them as published lemmas.
  - A `Collection.index_eq`-based proof (P1) would replace those readings at the next statement
    window.
- **Three readings found by the seal and replaced before delivery:**
  - `intro` through `StatClose`, replaced by P3 `statClose_iff`;
  - application of `PushesUniform`, replaced by `HardcoreBit.pushesUniform_iff`;
  - `[false] = natToList 1 0` by `rfl`, replaced by `listToNat_eq` and a core `rfl`.
- **Not sealed** (`evidence/seal/not-sealed.txt`):
  - `PolyExpr.eval` (notation, notes item 2; it is read in `rabin_genCoins_len` and in two
    `rfl`s of `rabinPrimeCoins`/`rabinTrials` evaluations);
  - the reducible abbreviations `DistinctPrimes`, `NUPPT.Coins` and `Primes`;
  - the structure projections `NUPPT.coins`/`adv`/`advice`, the `Collection` fields,
    `PermCollection.toCollection`/`perm` and `TrapdoorCollection.toPermCollection`/`inv`. These
    are never unfolded.
- **Controls** (`evidence/seal/SealControl{Unsealed,Sealed}.lean`, `evidence/logs/seal-control.log`).
  Three readings by `rfl` close unsealed (rc 0) and fail sealed (3 errors):
  - `listToNat [true] = 1`;
  - `NUPPT.advInput n y = pairEncode (1^n) y`;
  - `z.p = z.1.1.1`.
- **Exceptions: none.** Every foreign TCSlib definition is read through a published lemma: P1,
  P2, P3, P5, P6, P9, P10, P12, P14, and the "already published" list. Core and Mathlib
  reductions occur only in `rfl`/`show`/`change`:
  - `List.foldl` after `listToNat_eq`;
  - Fin/Subtype projections after `DistinctPrimes.p_eq`/`q_eq`;
  - the inverse in `Z_0` (`rabin_val_inv_zero_le`, `show (Int.sign e).natAbs ≤ 1`);
  - `Equiv.prodComm` and `Prod.fst_zmod_cast` on `ZMod.chineseRemainder`;
  - the square of a QR element (`change`).
  - Own definitions (`rabinGenParams`, `rabinF`, `rabinEnc`, `blumEnc`, `blumPermAt`, the raw
    string functions) are unfolded by `rw`/`unfold`.
- **E-API: none.**

## D11

- **Fields used:**
  - **generators:** `prime` (test), `divMod` (parity or residue mod 4), `le` (comparison with
    `⟦1⟧`/`⟦3⟧`), and `mul` (`N`). Two fields are outside the brief's table for this row:
    `sub` and `add`, for the zero padding of the fallback numerals and of the sampled word to
    `m` bits;
  - **`rabinFactorRaw`:** `modExp`, `divMod`, `add`, `sub`, `xgcd`, `le`, plus those of
    `unitSampleStr` through the cited `polyTimeComputable_unitSampleStr`;
  - **`blumInvRaw`:** `divMod`, `add`, `modExp`, `xgcd`, `mul`, and `sub` (zero prefixes and the
    truncation);
  - **`rabinRootRaw`:** `divMod`, `mul`, `le`, `sub`, and those of `blumInvRaw`.
- **Missing operations: none.**
- **Sketch deviations** for `polyTimeComputable_oddGenRaw`. Its sketch is frozen (not a
  Route/Correction target). A refresh is suggested.
  - Parity is read by `H.divMod`, not by the last bit (brief step 5).
  - The validity test is `pairEq` on the two prime numerals only. Both values are always primes
    of the class below `2^m` (`rabin_samplePrimePL_spec`), so the other tests of `rabinGenParams`
    hold automatically.
  - The fallback numerals are zero-padded constants (`H.sub`, `H.add`), not constant words: the
    width `m` varies.

## Checks

- **Owned file:** 0 errors, 0 warnings, no `sorry` (rc 0, 14 s).
- **Sweep** (`evidence/logs/sweep.log`): the owned file, then every later module of `order.txt`
  that imports it (the facade). The other modules of the list were built first
  (`bootstrap-rest.log`).
  ```
  == SUMMARY TCSlib/Cryptography/Candidates/Rabin rc=0 sorry-warnings=0 errors=0 other-warnings=0
  == SUMMARY TCSlib/Cryptography/Candidates rc=0 sorry-warnings=0 errors=0 other-warnings=0
  ```
- **Axiom prints** (`evidence/logs/axioms.log`, probe `evidence/probes/AxiomsRabin.lean` with a
  copy of the review's `#review_sorry` method; `preship/probes/SorrySources.lean` is not in the
  issue tree).
  - **No `sorryAx`:** these 8 targets print `[propext, Classical.choice, Quot.sound]`:
    `oddFactorProb_le`, `blumFactorProb_le`, `blumFactoring_of_factoring`,
    `polyTimeComputable_oddGenRaw`, `polyTimeComputable_blumGenRaw`,
    `polyTimeComputable_blumInvRaw`, `blumInv_spec`, `polyTimeComputable_rabinRootRaw`.
  - **With `sorryAx`** (the triple plus `sorryAx`), with the sources (`ALL`):

    | Target | Sources |
    |---|---|
    | `rabinSampler_spec`, `blumSampler_spec`, `polyTimeComputable_rabinFactorRaw` | `polyTimeComputable_unitSampleStr` |
    | `rabinCollection_sampleClose`, `rabinBlumTrapdoor_sampleClose` | `polyTimeComputable_unitSampleStr`, `statClose_sampleUnitL` (S3) |
    | `rabinCollection_invProbAt_le`, `rabinCollection_oneWay`, `rabinBlumTrapdoor_invProbAt_le`, `rabinBlumTrapdoor_oneWay` | `polyTimeComputable_unitSampleStr`, S3, `statClose_rejectBlocksL` |
    | `blumFactorProb_le_invProbAt`, `blumFactoring_of_rabinBlum_oneWay` | `polyTimeComputable_unitSampleStr`, `statClose_rejectBlocksL` |

    `polyTimeComputable_unitSampleStr` is reached through the samplers' types:
    `rabinSampler`/`blumSampler` carry it, and so does `rabinFactorer`.
  - **D3: pass.** Every source is in rabin's permitted set (rsa's
    `polyTimeComputable_unitSampleStr` and S3, and dl-a's `statClose_rejectBlocksL`). No own
    target remains sorried, and no machine-layer declaration is reached.
- **Lint:**
  - `style_lint.py` reports exactly one finding, the line count (3810 by the lint's count, > 1000). This is the
    approved size exception; the file is not split (`evidence/logs/style-lint.log`).
  - `campaign_style_lint.py --check8b` shows no FAIL row for `Rabin.lean`. The seven FAIL rows
    of the issue tree are gone, and their docstrings now carry Proof sketches.
  - It shows the size WARN, and the check-8 WARN list is identical to the issue tree's 25
    names, so there is no new public `def` (`evidence/logs/campaign-lint.log`; base run
    `campaign-lint-base.log`). The only FAIL left is the base `ElGamal.lean` row.
- **Statement freeze** (`evidence/declfreeze.py`, `evidence/logs/declfreeze.log`):
  - **Result:** PASS.
  - **Base declarations:** all 124 keep their headers byte-identical, and every non-target body
    is identical.
  - **New declarations:** the 178 are all private and `rabin_`-prefixed; there is no new public
    declaration.
  - **Changed docstrings:** only those of the 14 allowed targets:
    - the seven short ones;
    - the Route/Correction targets of steps 2, 4, 6 and 8 (`blumInv_spec`,
      `oddFactorProb_le`, `blumFactorProb_le`, `polyTimeComputable_rabinFactorRaw` and the
      three invProbAt bounds).
  - **Scope:** the diff touches only the owned file.
- **Final file length:** 3809 lines (was 1150).

## Findings and notes for the maintainer

1. **Notes item 7 is confirmed, and there is a second trap.**
   - Writing composites in applied form and folding by `unfold` kept the checks at about 12 s.
   - **The second trap:** two elaborations of the same predicate that differ only up to beta
     made unification unfold `rejectBlocksL`. One was `fun v => v.Prime ∧ (· ≠ 2) v` from a
     generic `P`; the other was `fun v => v.Prime ∧ v ≠ 2`. The decidability instances differ
     between the two.
   - The result was a hang: over 5 min, or 150 s with the step sorried.
   - **Fix:** name the composite once (`rabin_X P z0`), and pass instance-carrying proofs
     through `have`s with explicit types.
2. **Two frozen base proofs read `Collection.index`/`NUPPT.runAt` by `show`.** They are
   `rabinCollection_index` and `rabinBlumTrapdoor_index`, and they are the only seal failures.
   P1's `Collection.index_eq` would remove the readings.
3. **Sketches to refresh** at the next docstring window: `polyTimeComputable_oddGenRaw` (see
   D11).
4. **No escalation.** All 19 statements are true as stated. `BlumDensity` is used only as the
   hypothesis `hD`.

## Delivery

`inbox/fills/rabin/` on `exchange/pass-shelat-ch5-8`:
- `REPORT.md`;
- `patches/` (`git format-patch 16a7d02d..fill/rabin`, 12 patches);
- `src/TCSlib/Cryptography/Candidates/Rabin.lean`;
- `evidence/` (logs, seal files, probes, `declfreeze.py`, `chk.py`).

Replay check: `git am` of `patches/` onto `16a7d02d` reproduces `src/` byte for byte.

The pushes were `fill rabin: checkpoint 1` to `checkpoint 11`, then `fill rabin: final` (pushed twice: the second push corrects the commit and patch counts in this report).
