# Generic rejection helper review

Owned helper: `TCSlib/Cryptography/Randomness/Extraction/Rejection.lean`.
Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.

## Searches before implementation

The following read-only searches were performed against the issue base or the checkout at that base:

```sh
git grep -n -E '^(theorem|lemma).*probTrue|probTrue_map|map_uniform|uniform.*map|map.*uniform|uniform.*prod|prod.*uniform|mixture|mix_apply|convex' eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9 -- TCSlib/InformationTheory
git grep -n 'private.*\(uniform\|rejection\|map.*prob\|probTrue_map\|flat\|probTrue.*uniform\)' eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9 -- TCSlib/Cryptography TCSlib/InformationTheory
rg -n '(sum.*(equiv|bij)|sum_pi|Fin\.sum_univ_succ|piFinSucc)' TCSlib/InformationTheory TCSlib/Cryptography/Foundations
rg -n 'theorem .*map_uniform|theorem .*uniform_map|theorem .*probTrue_map|theorem .*map_map|theorem .*map_prod_snd|theorem .*uniform_prod|theorem .*mixture|def mixture|def select|def law' TCSlib/InformationTheory TCSlib/Cryptography TCSlib/Complexity/Randomized
rg -n 'map_apply_expect|accepted_flat|failure_pow|branch_apply|select_uniform_law' TCSlib --glob '*.lean'
```

`FinDist` had public primitive readers but no general pushforward composition, uniform-bijection,
pushforward acceptance, product-pushforward, or convex-mixture source theorem. Existing public
`FinDist.probTrue_eq_expect`, `expect_prod`, `probTrue_not`, `map_apply`, `uniform_apply`,
`prod_apply`, `flat_apply`, `hasMinEntropy_iff`, and `isSource_iff_hasMinEntropy` are imported and used.

The search found `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean`
`uprob_comp_eq_probTrue_map`, which concerns the separate `uprob` interface and a uniform input.
The helper's `probTrue_map` instead treats arbitrary `FinDist` inputs and follows from the
published expectation and pushforward readers. No source or proof was copied from that file.

A final broader name/content search is retained verbatim in
`logs/rejection-duplication-search.log`.

## Promotion requests

All declarations in `Randomness.Rejection` are generic in a finite type and should be considered
for promotion to the finite-distribution layer after this exclusive-ownership fill:

- Pushforward facts: `map_uniform_equiv`, `sum_map`, `expect_map`, `probTrue_map`,
  `map_apply_expect`, `map_map`, `map_prod_snd`, `uniform_prod`.
- Probability bounds: `probTrue_nonneg`, `probTrue_le_one`.
- Tuple decomposition: `tupleEquiv` and its four forward/inverse readers.
- Rejection sampling: `select`, `select_zero`, `select_succ`, `law`, `law_zero`, `law_succ`,
  `select_uniform_law`, `branch_apply`, `law_succ_apply`, `law_succ_probTrue`, `law_probTrue`,
  `law_apply`, `uniform_probTrue`, `accepted_nonempty`, `accepted_flat_apply`, `law_apply_flat`,
  `failure_pow_nonneg`, `failure_pow_le_one`, `law_eq_mixture`, `accepted_flat_isSource`,
  `law_isSource`.
- Convex mixtures: `mixture`, `mixture_apply`, `mixture_isSource`.

No missing foreign reader was identified. In particular, `FinDist.hasMinEntropy_iff` exposes
the pointwise source bound; neither `IsSource` nor `HasMinEntropy` is unfolded.

## Overlap disclosure

No private proof from another file was copied or re-derived from examination of its proof.
No overlap item is asserted. Nearby public results were imported where applicable.

## Edge cases

`law_probTrue` includes `q=0` and `q=1`. The pointwise and flat-mixture formulas assume `q>0`,
as supplied by checkpoint 1; neither divides by `1-q`. The law construction works for singleton
types, hence `n=0`. No lower bound on the cardinality is needed for the mixture source theorem.
