# Sampler bridge: implementation report

Implementation of the approved design (`design-r1.md`, `Skeleton.lean`, rulings of records `1a9a3295`).
Uncommitted maintainer record.

## Head

| Item | Value |
|---|---|
| Branch | `foundations/coin-sampling`, pushed to origin. No PR opened. No other branch pushed. |
| Base | `cbce64d1c135c710b7c036968ed9d4f21414aa72` (`foundations/subexp`, draft PR #374) |
| Head | `51dc767269bf81c4c7450d9a6430ad6bd3016470` (`git ls-remote` agrees) |
| Diff | 10 files, +1877 lines: 8 new modules, plus one import line each in `TCSlib.lean` and `TCSlib/Cryptography/Games.lean` |
| Signing | 9 commits, each with `git commit -S` (SSH), each staged by explicit path, each with the two required trailer lines |

The 9 commits, in order:

1. `5bfdeca5` Games: closeness and output inclusion.
2. `46c227a1` Contract and mixture identity.
3. `b7bfd797` Bucket sampler and weighted buckets.
4. `2b115add` Transfer.
5. `b3e684c2` Asymptotics.
6. `e33bee26` Instances.
7. `2fab24e9` Efficiency.
8. `6c65010f` Facade and export.
9. `51dc7672` Dedup fix: reuse `NumberTheory.bitsToNat_eq_listToNat` (see Helpers).

## Modules

Every file is under 1000 lines (sizes below). Every line is at most 100 characters.

| Module | Lines | Public declarations |
|---|---|---|
| `TCSlib/Cryptography/Games/Closeness.lean` | 269 | 24 |
| `TCSlib/Cryptography/CoinSampling/Basic.lean` | 487 | 43 |
| `TCSlib/Cryptography/CoinSampling/Buckets.lean` | 241 | 20 |
| `TCSlib/Cryptography/CoinSampling/Transfer.lean` | 173 | 11 |
| `TCSlib/Cryptography/CoinSampling/Asymptotic.lean` | 147 | 9 |
| `TCSlib/Cryptography/CoinSampling/Instances.lean` | 173 | 15 |
| `TCSlib/Cryptography/CoinSampling/Efficiency.lean` | 327 | 21, plus 3 private readers |
| `TCSlib/Cryptography/CoinSampling.lean` (facade, `## Contents`) | 56 | 0 |
| **Total** | | **143** (skeleton: 114) |

The declarations, by module:

- **Closeness.**
  - `Close`, `close_iff`, `expect_mem_unit`.
  - `Close.nonneg`, `.refl`, `.symm`, `.mono`, `.trans`, `close_of_expect_eq`.
  - `Close.bind_left`, `.bind_right`, `.bind`, `.map`, `.abs_prob_sub_le`, `.simulate`, `.abs_accept_sub_le`.
  - `advantage_le_of_close`.
  - `OutputsSubset`, `outputsSubset_iff`, `allOutputs_bind_iff`.
  - `OutputsSubset.refl`, `.trans`, `.bind`, `.simulate`.
- **Basic.**
  - `uexp_comp_eq_sum_fiber`, `uprob_apply_coord`.
  - `CoinSampler`, `fail`, `fail_eq`, `fail_nonneg`, `fail_le_one`.
  - `uprob_dec_eq_some`, `uexp_comp_dec` (the mixture identity), `statClose_some`, `statClose_getD`.
  - `option_map_equiv_eq_some_iff`, `congr`, `congr_dec`, `fail_congr`, `reindex`, `reindex_dec`, `fail_reindex`.
  - `block`, `block_apply`, `blockEquiv`, `blockEquiv_apply`, `uprob_block`.
  - `piDec`, `piDec_eq`, `piDec_eq_some_iff`, `piDec_eq_none_iff`, `pi`, `pi_dec`, `fail_pi_le`.
  - `uprob_halves`, `prodDec`, `prodDec_eq`, `prodDec_eq_some_iff`, `prodDec_eq_none_iff`, `prod`, `prod_dec`,
    `fail_prod_le`.
  - `ofRejection`, `ofRejection_dec`, `fail_ofRejection`.
  - `forall_comp_getD`, `forall_comp_elim`.
- **Buckets.**
  - `bucketDec`, `bucketDec_eq`, `bucketDec_eq_some_iff`, `bucketDec_eq_none_iff`.
  - `card_filter_finProdFinEquiv_symm_snd`, `uprob_bucketDec_eq_some`.
  - `bucket`, `bucket_dec`, `fail_bucket` (exact: `(2^s mod N)/2^s`), `fail_bucket_lt`, `fail_bucket_le`.
  - `ofEquiv`, `ofEquiv_dec`, `fail_ofEquiv`.
  - `RatSeed`, `ratSeed_eq`, `uprob_ratSeed_fst`, `weighted`, `weighted_eq`, `fail_weighted`.
- **Transfer.**
  - `allOutputs_sample_iff`.
  - `draw`, `draw_eq`, `drawD`, `drawD_eq`, `expect_draw`.
  - `close_draw_bind`, `close_drawD_bind`, `close_simulate_draw`.
  - `outputsSubset_drawD`, `allOutputs_draw_bind`.
- **Asymptotic.**
  - `polyExpr_eval_le_mul_pow`, `subexpSmall_polyExpr_mul`.
  - `drawSlack`, `drawSlack_eq`, `abs_two_inv_pow_le`.
  - `negligible_drawSlack`, `subexpSmall_drawSlack`, `fail_bucket_schedule_le`, `mul_fail_le_drawSlack`.
- **Instances.**
  - `zmod`, `zmod_dec`, `fail_zmod`, `fail_zmod_le`.
  - Non-vacuity checks `uprob_zmod_three_four_eq_some` and `fail_zmod_three_four` (below).
  - `noiseSeeds`, `noiseSeeds_eq`.
  - `LWESeed`, `lweSeed_eq`, `lweSeeds`, `lweSeeds_eq`, `fail_lweSeeds_le`.
  - `statClose_lweSample_coins`, `distAdv_lweSample_coins_le`.
- **Efficiency.**
  - `encodeOption`, `encodeOption_none`, `encodeOption_some`.
  - `UniformSampler` and its readers `toNUPPT`, `toNUPPT_eq`, `toNUPPT_uniform`, `toNUPPT_coins`, `toNUPPT_runAt`,
    `expect_toNUPPT_runAt`.
  - `bucketRaw`, `bucketRaw_eq`, `bucketRaw_layout`.
  - `bitsVal_replicate_false_append_true`, `two_pow_sub_mod_eq`, `bucketRaw_eq_binArith`.
  - `polyTimeComputable_bucketRaw`.
  - `bucketSampler`, `bucketSampler_sampler`, `bucketSampler_raw`, `bucketSampler_enc`.
  - Private readers `binArith_lt_pairEncode`, `binArith_sub_pairEncode`, `binArith_mod_pairEncode`.

**Non-vacuity.** The concrete instance is `zmod 3 4`: residues modulo 3 from four coins.
- Each residue is drawn with probability `5/16` (`uprob_zmod_three_four_eq_some`).
- The sampler fails with probability `1/16` (`fail_zmod_three_four`). This is below the design bound `N/2^s = 3/16`.
- Check: `3 · 5/16 + 1/16 = 1`.

### Deviations from the skeleton

1. **`ProbComp.Close.simulate` takes an extra hypothesis `(hε : 0 ≤ ε)`.**
   - The skeleton statement is false without it. Take an oracle family with no oracles: the only computations are returns,
     the per-call hypothesis is vacuous, and `Close (m·ε)` with `ε < 0` fails.
   - `close_simulate_draw` passes `fail_nonneg`, so its statement is unchanged.
2. **`OracleComp.OutputsSubset.simulate` is generalized.** It works for any target specification, not only `unifSpec`. The
   proof is the same.
3. **The `pi` and `prod` decoders are factored out** as the public `piDec` and `prodDec`, with readers. This avoids
   proving the same characterization twice: once inside the structure field and once in the lemma.
   - `pi_dec_eq_some_iff` and `pi_dec_eq_none_iff` became `piDec_eq_some_iff` and `piDec_eq_none_iff`, with
     `pi_dec : (pi n S).dec = piDec n S`.
   - `prod_dec` now reads `(S.prod S').dec = prodDec S S'`. The old formula is `prodDec_eq`.
   - New: `prodDec_eq_some_iff` and `prodDec_eq_none_iff`.
4. **`block` is now `CoinSampling.block`** (area namespace) with explicit `{n s}`. The new `blockEquiv` and `uprob_block`
   give the block marginals.
5. **`allOutputs_sample_iff` is now `CoinSampling.allOutputs_sample_iff`.** It is generic in `T`, so it no longer sits
   under `CoinSampler`.
6. **`outputsSubset_drawD` puts `[Nonempty Ω]` before `S`.** The statement is otherwise unchanged.
7. **`uprob_ratSeed_fst` drops `[DecidableEq α]`.** It was unused.
8. **`subexpSmall_drawSlack` keeps `0 < c` as `_hc0`.** The proof does not use it; it is the hypothesis of [JLS26]. The
   proof goes through the new general lemma `subexpSmall_polyExpr_mul`.
9. **`close_iff_epsClose_dist` is not implemented.** This is the interop reader, marked optional in design §4.3. It needs
   two new readers (`expect` as a sum over `dist`, and the `[0,1]`-weight bound by `statDist`). See "What is left".
10. **The bucket comparison** in `polyTimeComputable_bucketRaw` follows design §4.6: threshold `2^s − (2^s mod N)` by
    `BinArith.mod` and `sub`, test by `lt`, residue by `mod`, and `fromLEPoly .var` at the argument's width.
11. **Added glue that the skeleton does not have.** These are mostly readers that policy requires next to each definition
    ("definitions land with their lemmas"):
    - `expect_mem_unit`, `option_map_equiv_eq_some_iff`, `uexp_comp_eq_sum_fiber`, `uprob_apply_coord`, `uprob_halves`.
    - `card_filter_finProdFinEquiv_symm_snd`, `fail_weighted`, `fail_zmod`, `noiseSeeds_eq`, `lweSeeds_eq`.
    - `abs_two_inv_pow_le`, `mul_fail_le_drawSlack`, `toNUPPT_eq`, `bucketSampler_enc`.
    - `bucketRaw_eq_binArith`, `bitsVal_replicate_false_append_true`, `two_pow_sub_mod_eq`.

**Citation [Lem19], verified.** I read the arXiv version 1805.10941v4 (28 Dec 2018), pages 1–6.
- §3.2, Algorithm 4 (the Java algorithm) is exactly the bucket test: accept iff `x ∈ [0, 2^L − (2^L mod s))`, return
  `x mod s`.
- Lemma 2.1 gives the equal counts of each remainder.
- The final venue is ACM TOMACS 29(1), 2019, cited as such.
- Every docstring that cites it records the **deviation**: one round, giving up instead of looping.
- The reference is **not ingested** under `blueprint/src/references/`, and no blueprint entries were touched.

Other tags used: [PS10, Lemma 51.17 / Definition 181.1 / Definition 23.4], [Sho04, §1.1], [Gar26, Lemma 3.1 / §1.2],
[JLS26, Definition 2.1], [Pei16, Definitions 4.2.1 / 4.2.3], [AB09, §7.2]. These are the forms already used in the library.
Everything else carries a "Glue" note.

## Helpers and searches (duplication rule)

**Reused, not re-proved:**
- Sampling and probability:
  - `statClose_getD_of_uniform_of_some` (as `statClose_getD`).
  - `uniformFromBits` with `_eq_some_iff`, `_eq_none_iff`, `uprob_uniformFromBits_eq_some/_none`, `bitsToNat_def`.
  - `rejectionSample_uniform_of_some`, `uprob_rejectionSample_none`.
  - `uprob_comp_eq_sum_fiber`, `uprob_exists_le`, `uprob_or_le`, `uprob_comp_equiv`, `uprob_fst`, `uprob_true`,
    `uprob_eq_uexp`, `uprob_eq_card_filter`.
  - `uprob_pi_forall_dep` (`Asymptotic/Permutations`), `HardcoreBit.uprob_prod_and`, `OneWay.uprob_congr`.
  - The `StatClose` API (`statClose_iff`, `.map`) and `distAdv_le_of_statClose`.
- Games: `expect_bind`, `expect_map`, `abs_expect_sub_le`, `expect_sample_equiv`, `Bridge.expect_sample_eq_uexp`,
  `sample_eq`, `sampleFin_eq`, `AllOutputs.bind`, `allOutputs_true`, the `simulate_*` lemmas, `costBoundedBy_query`.
- Asymptotics: `negligible_two_pow_neg`, `Negligible.mono`, `Negligible.polyExpr_mul`, `subexpSmall_two_pow_neg`,
  `SubexpSmall.mono`, `.mul_pow`, `.const_mul`, `PolyExpr.eval_le`.
- Machines:
  - `NUPPT.ofPolyTimeUniform` with `_uniform`, `coins_`, `runAtL_`, `coinsEquiv_ofPolyTimeUniform(_ofFn)`.
  - The layout projections and `NUPPT.layout_eq`, `NUPPT.advInput_eq`.
  - `BinArith.polyTimeComputable_mod/sub/lt/cons`, `bitsVal_append_singleton`, `bitsVal_eq_zero_iff`,
    `LogProg.bitsVal_bits`.
  - `Encoding.BinaryArith.toLE/fromLEPoly` with `bitsVal_toLE`, `fromLEPoly_pairEncode` and the poly-time lemmas.
  - `EnsembleLemmas.polyTimeComputable_zeros`, `polyTimeComputable_ite`, `polyTimeComputable_const`.
  - `NumberTheory.bitsToNat_eq_listToNat`, `LWE.decisionAdvantage_eq`.
- Mathlib: `finProdFinEquiv` (and its `symm_apply`), `Fin.coe_modNat`, `Fin.appendEquiv`, `Equiv.piSplitAt`,
  `Equiv.curry`, `finSigmaFinEquiv`, `ZMod.finEquiv`, `Fintype.sum_option`, `Finset.sum_fiberwise`,
  `Nat.div_add_mod(')`, `Matrix.of`.
- Not needed: `OneWay.statClose_pi` (`pi` carries its own exact union bound) and `Nat.count_modEq_card` (the
  `finProdFinEquiv` fibre count was enough).

**New helpers, each searched first (grep of `TCSlib/`, Mathlib and core):**

| Helper | Search result | Status |
|---|---|---|
| `uexp_comp_eq_sum_fiber` | no real-valued fibre lemma; only `uprob_comp_eq_sum_fiber` (events) and `uprob_comp_eq_sum_map` (FinDist) exist | new glue |
| `uprob_apply_coord` | the `piSplitAt`+`uprob_fst` step exists only inline in `uexp_le_of_statClose` | **disclosed** (inline step published) |
| `option_map_equiv_eq_some_iff`, `uprob_halves`, `blockEquiv`/`uprob_block`, `expect_mem_unit` | none | new glue |
| `card_filter_finProdFinEquiv_symm_snd` | no fibre count for `modNat`; `Nat.count_modEq_card` is in another form | new glue |
| `polyExpr_eval_le_mul_pow` | none public; the same majorant is inline in `Negligible.polyExpr_mul` | **disclosed** |
| `subexpSmall_polyExpr_mul` | none (`Subexponential` has `mul_pow`, `const_mul` only) | new |
| `two_pow_sub_mod_eq` (`2^s − 2^s % N = ⌊2^s/N⌋·N`) | none in core or Mathlib (only inside `Nat.div_eq_sub_mod_div`'s proof) | new glue |
| `bitsVal_replicate_false_append_true` | none | new glue |
| private `binArith_lt/sub/mod_pairEncode` | `ClassP/BinaryArith` publishes no equation lemmas for `lt`, `sub`, `mod` (only `beq_def`) | **disclosed** `rfl` readers |
| `bitsToNat_eq_listToNat` | **found** `NumberTheory.bitsToNat_eq_listToNat` after first writing one | removed in `51dc7672`; the existing lemma is used |

**Disclosed overlaps, not otherwise needed:**
- `uexp_comp_dec` with `statClose_getD_of_uniform_of_some`: the Q8 overlap, below.
- `uprob_apply_coord` with `uexp_le_of_statClose`.
- `polyExpr_eval_le_mul_pow` with `Negligible.polyExpr_mul`.
- The three BinArith readers.

## Checks

- **How each module was checked.**
  - Copy: `cp -al` of snapshot #10 into `$SP/ol-sampler`, with `scripts/lean_check_tree.sh` and `TCSLIB_OLEANS` pointed at
    it.
  - One Lean process at a time.
  - No `lake build`. No `lake exe cache get`.
- **Base modules first.** `Foundations/Subexponential` and the `Foundations` facade: rc 0.
- **Sweep in dependency order, after the last edit.** Each module gave rc 0, 0 `error`, **0 warnings** and no `sorry`:
  - `Games/Closeness`, then the `Games` facade.
  - `CoinSampling/Basic`, `Buckets`, `Transfer`, `Asymptotic`, `Instances`, `Efficiency`.
  - The `CoinSampling` facade.
- **The root `TCSlib.lean`** gave rc 0, so the full import closure loads with no name clash.
  - This needed the procedure's Mathlib overlay in my copy only: `mloverlay.sh`, plus `NthRootLemmas.olean` copied with
    hash `c0a9cff0…`.
- **Snapshot #10 is unmodified.** `snapmap.py verify` against `olean-snapshot.map-cf6a2266.tsv` gave 1478 files, extra 0 /
  changed 0 / missing 0, RESULT OK.
- **Lint.**
  - `python3 -I scripts/style_lint.py` on the 8 new files and `Games.lean`: **0 findings**.
  - `TCSlib.lean` keeps its two findings from the base (no `# Title`, no `## Contents`). They are not touched by the added
    import line.
- **Axioms.** I ran a scratch file: a meta command calling `collectAxioms` on every theorem and definition of each new
  module, plus `#print axioms` on the headline theorems.
  - Every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. Some, such as
    `OutputsSubset.simulate`, depend on no axioms at all.

    | Module | Declarations | Non-standard axioms |
    |---|---|---|
    | Closeness | 24 | none |
    | Basic | 54 (incl. generated) | none |
    | Buckets | 20 | none |
    | Transfer | 11 | none |
    | Asymptotic | 9 | none |
    | Instances | 16 | none |
    | Efficiency | 37 | none |

  - **The efficiency layer is sorry-free.** `polyTimeComputable_bucketRaw`, `bucketSampler`, `toNUPPT_runAt` and
    `expect_toNUPPT_runAt` reach no `sorryAx`.
  - All the TM tooling used is clean: `BinArith.polyTimeComputable_mod/sub/lt/mul/div`, `polyTimeComputable_ite`,
    `toLE`/`fromLEPoly`, `polyTimeComputable_zeros`, `polyTimeComputable_inArg`, `runAtL_ofPolyTimeUniform`.
  - Control: the same scratch file reports `sorryAx` for `Turing.FinTM.lengthBitsTM_computes`
    (`ClassP/TimeConstructible`), so the check does detect it.

## Q8: the temporary overlap and its follow-up

**The overlap.** `CoinSampler.uprob_dec_eq_some` and `CoinSampler.uexp_comp_dec` (with `uexp_comp_eq_sum_fiber`), in
`CoinSampling/Basic.lean`, prove the exact mixture identity. That identity repeats the fibre decomposition `hdec` and the
`p + q·|γ| = 1` step inside the proof of `statClose_getD_of_uniform_of_some`
(`Asymptotic/Sampling.lean`).
- `Asymptotic/Sampling.lean` is in Stage 2 scope (25 `scope.tsv` rows and 1 S2-A item; job on `cleanup/stage2-s2a`), so
  this PR does not edit it.
- The overlap is disclosed in the module docstring and in `uexp_comp_dec`'s docstring.
- `statClose_getD` applies the old lemma; it does not re-prove it.

**Follow-up, once S2-A merges.**
1. In `Asymptotic/Sampling.lean`, beside `statClose_getD_of_uniform_of_some`, state the abstract mixture identity for a
   raw sampler `S : Ω → Option γ` that satisfies `huni`:
   `uexp (F ∘ S) = Pr[S = none]·F none + (1 − Pr[S = none])·uexp (F ∘ some)`. Move `uexp_comp_eq_sum_fiber` there with it.
2. Re-derive `statClose_getD_of_uniform_of_some` from that identity, taking `F` to be the indicator of the test set
   composed with `getD d`. This is a proof-level change; the statement is unchanged.
3. Make `CoinSampler.uprob_dec_eq_some` and `uexp_comp_dec` one-line applications of the moved identity, and delete the
   local `uexp_comp_eq_sum_fiber`.

The identity must live in `Sampling.lean`, not in `CoinSampling/Basic.lean`. `Basic` imports `Sampling` (through
`Permutations`), so the old lemma cannot be derived "from the new module" without an import cycle.

## What is left

- **`ProbComp.close_iff_epsClose_dist`.** This is the interop with `EpsClose`/`StatClose` laws (design §4.3, optional). It
  needs the readers `expect = Σ dist·g` and `|Σ (p−q)·g| ≤ statDist` for `g ∈ [0,1]`.
- **Equation lemmas for `Complexity.BinArith`.** Publish `lt_pairEncode`, `sub_pairEncode` and `mod_pairEncode` (and
  `add`, `mul`, `div`) in `ClassP/BinaryArith`. Then replace the three private `rfl` readers in `Efficiency.lean`.
- **A shared `PolyExpr` majorant.** Publish the majorant (`PolyExpr.eval_le_mul_pow`) beside `PolyExpr.eval_le` and
  rewrite both `Negligible.polyExpr_mul` and `polyExpr_eval_le_mul_pow` on top of it.
- **Publish the coordinate marginal** `uprob_apply_coord` in `Foundations/Probability` (after Stage 2), and use it in
  `uexp_le_of_statClose`.
- **Q8 follow-up** (above).
- **Backlog row for Q9.** Make `BB1Machine.draw` an instance once `rejectBlocksL`'s uniformity on success is published.
  There is no retrofit in this PR.
- **[Lem19] ingest.** Ingest it under `blueprint/src/references/` if blueprint entries for this area are wanted.
- **Consumer side, Q10, for the sPRG and PHFE jobs.** The modulus must reach the honest machines through their input,
  then compose `bucketRaw` into their raw maps.
- **The local `foundations/coin-sampling` branch** stays in the main repository. I removed the worktree and the scratch
  trees.
