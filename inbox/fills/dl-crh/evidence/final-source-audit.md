# Final source audit: dl-crh

This is a static review against issue base
`eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`. It runs no Lean or Lake process,
does not edit Lean, and does not replace the required kernel, axiom, seal,
explicit-unfold, style-lint, or admission-sweep evidence.

## Scope and source snapshot

The reviewed diff contains exactly these eight Lean files. SHA-256 values identify
the source bytes read for the preservation check; later edits require checking the
affected audit assertions again.

| File | Lines | SHA-256 |
|---|---:|---|
| `TCSlib/Cryptography/Candidates/DiscreteLog.lean` | 1209 | `ef7cf001f483ce0a5c47025924ee9c10fb78a9b59f73e4e5482091ad05a2aa67` |
| `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean` | 726 | `c14c9abe370d276469444e93d31a661fda699b86e5429a05dd9d1c28aa030896` |
| `TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean` | 130 | `adffb2ec4b9a064aa2a21948ab8a0b79510efda5b1d9be8b48bbc055e02bd221` |
| `TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean` | 63 | `1ab5d3ece9c424a456e380d2e40eba45b6f0a8f76b69d12d03bd36842eecd6cb` |
| `TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean` | 191 | `79669605ededcae778a0d719f0db5bd6a998f221ded322fd283c65e04411aaa4` |
| `TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean` | 68 | `bf943d5aea5c9da86ada6d9171576b40949b96f2dc4882699dd66112f00f610b` |
| `TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean` | 334 | `6029adc4b767dfa376b1dd3b4748ecf664d7bc62bd28e470e3304c9cf168b6c1` |
| `TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean` | 92 | `398337fbdf7e1e2d46f6658262ee47cf887a5d3707e18c6c8807dda9f0a55c15` |

The owned module and all six new helpers remain below 1000 lines. The provider
file was already 1192 lines at the issue base. Its diff is exactly 17 added lines,
zero deleted lines, containing the two user-authorized readers `expGenFun_eq` and
`expSampleRaw_eq`. The inherited provider size and narrow exception must remain
visible in the report; this audit does not claim that every changed file is below
1000 lines.

## Preservation and prose

A substring comparison used the exact runnable source
`evidence/tools/final_source_preservation.py`; its raw output is
`evidence/logs/final-source-preservation.json`. The command was
`python3 -I evidence/tools/final_source_preservation.py` from the proof checkout.
It found:

- The frozen statement of `dlHash_crh`, up to `:= by`, is unchanged.
- All 16 other original owned-module declaration bodies are preserved exactly:
  `dlHashIdx`, `dlHashIdx_eq`, `dlHashGenFun`, `dlHashGenFun_eq`, `dlHashPow`,
  `dlHashPow_eq`, `dlHashMul`, `dlHashMul_eq`, `dlHashEval`, `dlHashEval_eq`,
  the five original polynomial-time theorems, and `dlHash`.
- All 17 original declaration docstrings, including the target's statement and
  proof sketch, are preserved as exact substrings.
- The original `dlHash` simps declaration remains unchanged with
  `isSimp := false`. No new global simp attributes or public abbreviations were
  added in the owned/helper files.

The module title drops the statement-phase label, the main-results status now
says proved, and the contents list names all six helper modules. The original
source notes about the bounded exponent domain and full group remain intact.
Every new public declaration reviewed has natural-language prose; substantive
long proofs have adjacent proof sketches. The reduction's selected subtraction
direction agrees with its docstrings and the frozen route.

No mathematical weakening or deletion of a pre-existing declaration was found.
The provider diff is additive only and matches the scoped authorization in
`evidence/authorization.md`.

## Rule 10 source inspection

No new explicit `unfold` or `delta` occurs in the owned/helper files. The only
explicit `dsimp` occurrences are three reductions of the local `width` let in
`Reduction.lean` (lines 191, 258, and 259 in this snapshot).

The original owned efficiency proofs still name their own definitions
`dlHashGenFun`, `dlHashPow`, and `dlHashMul` in `simp only`; those bodies are in
the same file and were preserved exactly. Other named local lets, such as
`width`, `u`, `w`, and `z`, are local proof data rather than foreign definitions.
`Function.comp_apply` is an equation theorem. The remaining inspected foreign
TCSlib reads use published equations, contracts, iff characterizations, or
field readers, including:

- `expGenFun_eq`, `expSampleRaw_eq`, `expEval_spec`, `expEnc_eq`, `expF_eq`,
  `expOrd_of_valid`, `expValid_iff`, and `wellFormedIndex_iff`;
- `NUPPT` layout, coin, construction, and run readers;
- arithmetic-string equations and lossless-value readers;
- `splitBits_fst/snd`, `ofFn_drop_take`, padding readers, and the new
  split-word readers;
- CRH hash/compression/collision readers and the generic probability contracts.

Helpers do not import or unfold the owned module. Their cross-helper consumers
use public readers: for example, the reduction uses the encoding lemmas, the
owned evaluator uses `expUnit_pow_val`, and the final sampler switch uses
`expEval_natToList_val`.

`Sampling.residueFinEquiv_val` ends by `rfl` after eliminating the modulus cases;
that reduction concerns a same-file definition and core/Mathlib representations.
It is not an explicit unfolding of a foreign TCSlib definition. Whole-file seals
remain necessary to check implicit definitional dependencies mechanically.

## Duplication and promotion bookkeeping findings

The ledger already records conservative overlap with:

1. `Candidates/DiscreteLogHardcore.lean dlb_expo_val`;
2. `Candidates/Factoring.lean fac_listToNat_inj`;
3. `Asymptotic/UniversalPadding.lean ofFn_splitCoins_symm_cast`.

The public `Authentication.ofFn_coins_split` was found during the split-word
search. The new lemmas concern `splitBits` itself, use its pointwise public
readers, and reuse the stronger public window theorem `ofFn_drop_take`. They do
not restate or transcribe the coin-word theorem or its proof. The analogous
public seed equivalences in `EnsemblesLemmas` were also inspected; `sumCoinsEquiv`
adds the arbitrary-machine sum-polynomial interface and consumes existing
machine/cast/split readers.

The following bookkeeping updates are required before the final report is
sealed. These are report/promotion findings, not requests to change the Lean:

- Add the Sampling declarations to the central promotion ledger:
  `residueFinEquiv`, its equation/value readers, `sampleBelowL_uprob_le`, and
  `expEval_natToList_val`. The first four are already promotion-requested in
  Sampling's module prose, but absent from the central ledger at review time.
- `expEval_natToList_val` is a general candidate evaluator reader. Its proof
  explicitly consumes the PUBLIC `expEval_spec` and specializes its encoding
  through PUBLIC `expEnc_eq` and `WellFormedIndex.dlW_eq`; it does not copy or
  re-prove `expEval_spec`, and no private overlap is needed for this reader.
- Add the conservative disclosure
  `overlap: TCSlib/Cryptography/Candidates/DiscreteLog.lean dla_statClose_expDec`.
  The sampled-to-uniform residue relabeling overlaps mathematically with a
  substep of that private theorem. Here the equivalence is independently built
  from Mathlib's public `ZMod.finEquiv`, and the switch reuses public
  `statClose_sampleBelowL`, `StatClose.comp_equiv_right`, and
  `StatClose.abs_uprob_sub_le_prod`. The private manual equivalence and decoder
  proof were not copied. This updates the ledger's earlier promise to record
  later re-derivation of that submaterial.
- Explicitly promotion-request `Algebra.expUnit_pow_val` to the candidate
  group interface, and `Reduction.modularDifference`, its equation/value readers,
  and `polyTimeComputable_modularDifference` to the generic arithmetic layer.

The final REPORT must carry every overlap item rather than merely leave it in
this audit. No undisclosed copied proof was identified by this review.

## Search and review provenance

The review used `git diff --name-only`, `git diff --unified=0`, and
`git diff --numstat` against the issue base; complete reads of all six helpers;
the owned module and both provider additions; and a `python3 -I` preservation
check. Searches included:

```text
rg 'ofFn.*splitBits|splitBits.*ofFn|theorem ofFn_coins_split' TCSlib
rg 'coinsEquiv.*(Add|add|split|Split)|Coins.*≃|coinsEquivPoly|splitCoins_symm|ofFn_splitCoins' TCSlib/Complexity/Randomized TCSlib/Cryptography/Asymptotic
rg 'expect_sample.*uexp|uexp.*expect_sample|residueFinEquiv|ZMod.*≃ Fin|expEval.*natToList|natToList.*expEval|modularDifference|residue_difference' TCSlib
rg 'addStr.*subStr|subStr.*pairEncode m' TCSlib/Cryptography/Candidates TCSlib/Cryptography/Asymptotic
rg '\b(unfold|delta|dsimp)\b' TCSlib/Cryptography/Hashing/FromDiscreteLog.lean TCSlib/Cryptography/Hashing/FromDiscreteLog/*.lean
```

The inspected overlap providers were the named private declarations above.
No external project code or additional mathematical source was used in this
review. The final theorem uses the issued compression, collision-shape,
efficient-reduction, statistical-switch, and negligible-bound route.
