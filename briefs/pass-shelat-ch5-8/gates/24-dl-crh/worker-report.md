# dl-crh — final proof report

**Status: proof complete, with the recorded user scope and lint exceptions.**
`TCSlib.Cryptography.Authentication.dlHash_crh` is proved with its original statement.
The proof branch `fill/dl-crh` remains local. Only the assigned exchange delivery path is used.

Issue pack: `b436d19a0310265b214447ea6710deba32df6dd8`. Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Final proof commit: `fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16`. Lean: `leanprover/lean4:v4.25.0`.
Pinned Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

## Delivered mathematics and edge cases



1. **Read the honest key.** The user-authorized provider readers are
   `expGenFun_eq` and `expSampleRaw_eq`
   (`TCSlib/Cryptography/Candidates/DiscreteLog.lean:486`, `:657`).
   `dlHashIdx_layout` and `dlHashGenFun_layout` expose generator and sampler tape
   segments (`TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:91`, `:121`).
   `dlHashGenFun_key` (`:141`) proves the sampled exponent, including the fallback,
   is below the positive order and identifies the key as `⟨i, expF i z⟩`.
   The published coin equivalence and activation readers separate the two honest
   tapes (`dlHash_coinsEquiv`, `:446`; `dlHash_gen_runAt`, `:474`).

2. **Compression.** `dlHashEval_expF` (`FromDiscreteLog.lean:264`) identifies
   evaluation with the numeral of the unit `(if b then g^z else 1) * g^x`.
   `dlHashEval_range` (`:324`) proves exact output width `n` and positive value
   below `p`. `dlHash_compresses` (`:489`) uses the generator threshold, this
   range lemma, and `card_boundedInput`/`card_boundedRange`
   (`FromDiscreteLog/Encoding.lean:152`, `:164`). The cardinalities are `2m` and
   `p-1=m`, with `m>0`; hence the range is strictly smaller than the domain.

3. **Collision shape and extraction.** Equal selectors cancel their common unit
   factor. `unitCollision_selector_ne` (`FromDiscreteLog/Algebra.lean:76`) then
   applies published `expF_injective` (`Candidates/DiscreteLog.lean:299`) and
   bounded residue canonicity. For unequal selectors, `unitCollision_extract`
   (`Algebra.lean:110`) uses the generator's order and modular addition to recover
   `z.val`: the residue of `x' + (m-x)` if the first selector is true, or
   `x + (m-x')` otherwise. `dlHashEval_collision`
   (`FromDiscreteLog.lean:292`) connects distinct bit inputs and their equal
   evaluations to this unit-group statement.

4. **The concrete NUPPT reduction.** `collisionPost`
   (`FromDiscreteLog/Reduction.lean:85`) pads/truncates the finder output to two
   `(n+1)`-bit inputs, reads their exponent prefixes and the first selector, and
   evaluates the selected modular difference through subtraction, addition, and
   division. `polyTimeComputable_collisionPost` (`:116`) proves its efficiency.
   `collisionReduction` (`:290`) wraps the raw finder/output composition using
   `NUPPT.ofPolyTime`; its coin, advice, and activation readers (`:301`, `:306`,
   `:311`, `:317`, `:328`) retain the finder's tapes and advice.
   `collisionPost_split` (`:222`) covers arbitrary raw finder outputs.
   `dlHash_reduction_success` (`FromDiscreteLog.lean:581`) removes padding from
   the proved exact-length hash values, applies extraction, and proves that the
   reduction writes and decodes the canonical `n`-bit numeral of `z.val`.
   `dlHash_ideal_collision_le` (`:631`) transports equal-length finder/reduction
   coins and lifts that pointwise implication to uniform probabilities.

5. **Distribution switch and negligibility.** `collision_accept_eq`
   (`FromDiscreteLog/Probability.lean:50`) reads the CRH game as a generator-coin
   average of finder-coin probabilities. The specialized reader
   `dlHash_collision_accept_eq` (`FromDiscreteLog.lean:549`) separates the honest
   sampler tape as well. `sampleBelowL_uprob_le`
   (`FromDiscreteLog/Sampling.lean:81`) applies the published sampler closeness
   with independent auxiliary finder coins and relabels the ideal seed through
   Mathlib's value-preserving finite-residue equivalence. The canonical evaluator
   reader at `Sampling.lean:66` identifies the resulting ideal key with `expF i z`.
   Averaging and the reduction bound give `dlHash_collision_bound`
   (`FromDiscreteLog.lean:658`): for `n ≥ G.n₀`, collision acceptance is at most
   `G.dlProb B n + (1/2)^n`. The target proof (`:710`) combines `hDL B`,
   `negligible_two_pow_neg`, addition, and eventual domination. It chooses the
   collision probability itself as the all-parameter negligible upper bound.

## All six brief edge cases

| Edge case | How the delivered proof covers it |
|---|---|
| Parameters below `G.n₀` | Compression is explicitly eventual (`dlHash_compresses`, main file `:489`). Security uses `Negligible.mono` with threshold `G.n₀` in `dlHash_crh` (`:710`), so it imposes no invalid asymptotic bound below the threshold. The chosen bound equals actual collision acceptance at every parameter. |
| Invalid indices | Pointwise algebra/evaluation/reduction lemmas explicitly require `ExpValid`. The generated-index proof obtains it from `G.valid` and `hV` above the threshold (`dlHashGenFun_key`, `:141`; `dlHash_collision_bound`, `:658`). It makes no security or range claim for arbitrary invalid externally supplied indices. |
| Equal selectors `b=b'` | `unitCollision_selector_ne` (`Algebra.lean:76`) cancels the common factor and applies `expF_injective`; bounded equal exponents and equal selectors contradict input distinctness. |
| Equal exponent prefixes `x=x'` | Unequal selectors are still permitted. `unitCollision_extract` (`Algebra.lean:110`) has no exponent-inequality assumption; its modular-difference formula gives `m mod m=0` in this case. The reduction therefore recovers the zero challenge rather than discarding this collision. |
| Inputs outside `D_i` | `dlHashCollision_iff` (`FromDiscreteLog.lean:533`) retains both exponent-below-`m` guards. `dlHash_collision_accept_eq` (`:549`) proves this is exactly the CRH game's guarded event. `dlHash_reduction_success` (`:581`) consumes those guards; no unguarded finder output is counted as a successful collision. |
| Honest `y=g^w` with `w=0` | `dlHashGenFun_key` (`:141`) handles both an accepted zero and the sampler's fallback zero. The unit formula and extraction theorems quantify over every residue `z`, with no nonzero hypothesis. Thus the identity key and collisions with equal exponent prefixes are included in the same proof. |

No new hardness assumption, full-length-prime assumption, or narrowed adversary
class is introduced. The full-group equation `m=p-1` is used for compression;
the collision reduction itself only needs the valid exponentiation-group data.


## Scope, declarations, and sketch

Eight Lean files changed: the owned hashing module, six helpers, and the two expressly authorized
reader equations in Candidates/DiscreteLog.lean. No target or existing declaration type changed;
the separate source-preservation check retains all 16 other original bodies and all 17 original
declaration docstrings byte-for-byte, together with the frozen target statement.
the stored metadata comparison reports no kind/type/reducibility/abbreviation/simp/instance/protected delta.
The hashing title drops statement phase, Main results records the proof, and Contents lists all six helpers.
The sketch follows compression, selector inequality, the concrete reduction, and the sampler switch.

The complete 69-entry source declaration inventory, with qualified names, kinds, visibility, files,
and source lines, is `evidence/new-declarations-final3.md` and `evidence/new-declarations-final3.json`, generated by
`python3 -I evidence/tools/new_declarations.py`. Both private helper declarations are included.
Generated kernel constants are included separately in the stored-constant census.

## Promotions and resolved reader requests

The initial missing-reader escalation was resolved by the user's scoped authorization for
`expGenFun_eq` and `expSampleRaw_eq`; both are delivered with equation docstrings and no simp attribute.
No outstanding foreign-reader request remains.

- Encoding: ofFn_splitBits_fst, ofFn_splitBits_snd, inputWord_split, inputWord_take, inputWord_drop, inputWord_ext, inputWord_num_ext, boundedInputEquiv, boundedInputEquiv_apply, boundedInputEquiv_symm_apply, card_boundedInput, and card_boundedRange → shared authentication/bit-vector encoding.
- Algebra: private residue_difference → shared natural modular arithmetic; expUnit_pow_val → the candidate unit-power interface.
- Coins: sumCoinsEquiv, sumCoinsEquiv_eq, and sumCoinsEquiv_symm_ofFn → the shared randomized/collection coin interface.
- Reduction: modularDifference, modularDifference_eq, modularDifference_value, and polyTimeComputable_modularDifference → the shared arithmetic string layer. The local padding-idempotence argument in collisionPost_split is a candidate shared padStr lemma.
- Probability: expect_sample_eq_uexp → the shared games bridge/probability layer; collision_accept_eq → Hashing/CollisionResistant.
- Sampling: residueFinEquiv, residueFinEquiv_eq, and residueFinEquiv_val → finite-residue encoding; sampleBelowL_uprob_le → the candidate sampler interface; expEval_natToList_val → canonical candidate-evaluator readers.

Searches and detailed provenance are retained in `evidence/PROMOTION.md` and the delivered tools/logs.
Existing public lemmas are imported. No private provider proof was copied.

## All four overlap disclosures

**overlap: TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean dlb_expo_val**

Arbitrary-natural unit-power values were rederived from public val_units_pow, coe_expUnit, and expValid_iff.

**overlap: TCSlib/Cryptography/Candidates/Factoring.lean fac_listToNat_inj**

Equal-width numeral injectivity was rederived through public numeral canonicity in inputWord_num_ext.

**overlap: TCSlib/Cryptography/Asymptotic/UniversalPadding.lean ofFn_splitCoins_symm_cast**

Coin-cast concatenation was rederived using public ofFn_arrowCongr_finCongr and ofFn_splitCoins_symm.

**overlap: TCSlib/Cryptography/Candidates/DiscreteLog.lean dla_statClose_expDec**

Overlapping residue relabel/statistical-switch submaterial uses public sampler closeness and Mathlib ZMod.finEquiv; the private implementation was not copied.

## Checks and admissions

The original seven pack checksums and 170 issue-source checksums passed; original raw evidence remains
verbatim in `evidence/initial-escalation.zip`. The canonical final sweep under
`evidence/logs/final-sweep-repaired/` checked all 176 modules, one module per
`scripts/lean_check_tree.sh` call, with zero errors. Source/log hashes are bound in raw results.
The earlier complete pass under `logs/final-sweep/` also built previously unbuilt downstream
prerequisites. It remains labeled preliminary; `evidence/sweep-phases.md` records why the fully
bootstrapped order was then checked again. No running Lean process was interrupted.
The admission comparison is exactly 22 → 21: only `dlHash_crh` was removed, with no added admission.
`evidence/admission-delta-repaired.json` retains every warning and its source/log location.

No project `lake build` or unfiltered cache fetch was used. Python commands use `python3 -I`.
Development failures, repairs, raw logs, probe sources, manifests, request records, and tools are retained.

## Axioms and stored metadata

Target axioms: `propext`, `Classical.choice`, `Quot.sound`.
All-stored census: base 172, final 265; 93 added stored constants and 0 removed.
Metadata changes: 0. New nonstandard-axiom dependencies: 0.
The full raw census, including generated matchers/projections, is delivered and named in the summary.

Every axiom delta:

- `TCSlib.Cryptography.Hashing.FromDiscreteLog` / `TCSlib.Cryptography.Authentication.dlHash_crh`: `['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']` → `['Classical.choice', 'Quot.sound', 'propext']`.

Inherited final nonstandard entries: 0; none is new or worsened:


## Rule 10 seals, controls, and explicit scan

A excludes exactly `Complexity.PolyExpr.eval` as notation; B seals it. Both seal all ordinary
foreign TCSlib definitions in the full import closure, including eligible generated matchers and
definition instances; recorded abbreviation/status exclusions remain visible in request records.
Base covers the two pre-existing changed files; all six new helpers are absent at base. Final covers
all eight files. Every harness and mask check is valid, and there are zero new failing declarations.

Current baseline/final source declaration results, by side/owner/variant:

### Explicit reuse of the unchanged original baseline

Fresh final-source evidence belongs to `final3`. The four original baseline seals,
eight baseline control runs, baseline census, and 208-row baseline scan/review remain in
their actual `final2` paths; they were not copied or relabeled as fresh runs.
The reuse record binds all original raw evidence, the unchanged 98-source baseline closure,
and 98 runtime-object verifications. Fresh final-source snapshots, seals, controls, census,
and manual scan review are separately checked against the repaired current proof bytes.
Binding record: `evidence/probes/Rule10/final3/baseline-reuse.json`.

### Harness revision and measured pilot equivalence

This report uses final-source edition `final3` and harness revision `batch2048-ordinary-local-attribute-api-v2`.
The optimization pilot/benchmark is historical evidence from `final2`.
Its original-source/request preservation claims refer to that historical before/after harness
comparison. They do not assert that the pilot's source snapshot equals the repaired final
proof source snapshot. The fresh final-source evidence is independently bound above.
The original final1 probes, logs, and versioned tools are retained. Performance investigation
identified 24 full-environment scans and 12 mask snapshots for the original 1409-request base-A
probe. The revision
uses batches of at most 2048 requests through the same ordinary registered local attribute API,
with component/mask checks at install and EOF. It does not use a direct reducibility setter,
unsafe reducibility, or source/proof changes. Static assembly alone was explicitly insufficient;
the delivered completed provenance also contains actual native controls and a full base-A pilot.

The optimized unsealed/reader controls passed; each sealed negative failed exactly once.
The complete optimized base-A failure set equals the completed original base-A failure set.
Measured original base-A duration: 637.935793 seconds; optimized base-A:
56.96355 seconds (ratio 11.199).
Actual logs, API source hashes, assembly data, and comparisons: `evidence/probes/Rule10/final2/seal-provenance.json`.
The complete base/final seals, controls, census, and full per-row scan reviews are separately
required by this report; pilot results do not substitute for those checks.

### base / TCSlib.Cryptography.Candidates.DiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_A_DlCrh_base_A_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### base / TCSlib.Cryptography.Candidates.DiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_B_DlCrh_base_B_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### base / TCSlib.Cryptography.Hashing.FromDiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_A_DlCrh_base_A_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### base / TCSlib.Cryptography.Hashing.FromDiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_B_DlCrh_base_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Candidates.DiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Candidates.DiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Algebra.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Algebra.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Coins.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Coins.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Encoding.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Encoding.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Probability.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Probability.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Sampling.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Sampling.001.log`.

None.

### Superseded final2 seal failures and their repairs

The superseded final2 runs checked source commit `5a24269932a72f672104b18280609879dd992c82`. Their source failures
are disclosed below even though every fresh final3 source seal now has zero errors. The generator
rehashes each original raw log and checks every diagnostic against the mapped native records;
the final3 success does not erase these earlier findings.

| Variant | Failing declaration | Diagnostics | Original source lines | Raw probe lines |
|---|---|---:|---|---|
| B | `TCSlib.Cryptography.Authentication.dlHash_collision_accept_eq` | 1 | 556 | 666 |
| B | `TCSlib.Cryptography.Authentication.dlHash_compresses` | 3 | 511, 512, 514 | 621, 622, 624 |
| A | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split` | 1 | 242 | 352 |
| B | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split` | 1 | 242 | 352 |

Original raw-log bindings (shared logs intentionally occur for both affected declarations):

- B / `TCSlib.Cryptography.Authentication.dlHash_collision_accept_eq`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`;
  SHA-256 `fccb646130f454d0e540c5ea868ea6b0a04f13c98c7169f2256eecdb51f8b000`.
- B / `TCSlib.Cryptography.Authentication.dlHash_compresses`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`;
  SHA-256 `fccb646130f454d0e540c5ea868ea6b0a04f13c98c7169f2256eecdb51f8b000`.
- A / `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`;
  SHA-256 `466b9ffcf10b96592b9f69f3951ed13f1546affc52064c481d05e5fd472a831c`.
- B / `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`;
  SHA-256 `e96e6ca1cbf671e0aa777b261109a37c9565b600cbefeefb37f8b6b113d71d1c`.

The four variant/declaration rows contain six diagnostics in three raw logs:

- `collisionPost_split` (A and B, one diagnostic each): the original `simpa` required an implicit
  dependent transport of the padded-word width. The repair first proves `hwidth` with the public
  polynomial-evaluation readers, then uses `congrArg (fun k : ℕ => List.ofFn (padFin k raw)) hwidth`,
  reverses that equality, and composes it with the public `ofFn_padFin_eq_padStr` equation.
- `dlHash_compresses` (B, three diagnostics) and `dlHash_collision_accept_eq` (B, one diagnostic):
  combined simplification normalized dependent input widths before the CRH field/hash readers
  could match while `PolyExpr.eval` was sealed. The repair stages simplification: first
  `dlHash_inDom`, `dlHash_inRange` where needed, `CRH.hash_eq`, `dlHash_eval`, pair/guard readers;
  then `dlHash_domLen`, `dlHash_rangeLen`, and the published polynomial evaluation equations.

All three theorem headers/types are byte-identical before and after these repairs, as checked
again by this generator. No statement, hardness assumption, global simp attribute, or mathematics
changed. Fresh final3 seals validate the repaired bytes: all 16 final owner/variant runs have
zero failing declarations, including Reduction A/B and the owned module B.

base: 8 control probe runs, 120 per-case checks, 28 sealed negatives; each negative fails exactly once and every expected positive/unsealed case passes.

base explicit scan: 208 individually reviewed rows. Raw scanner foreign-definition candidates: 0; raw unresolved rows before manual review: 10. Final manual disposition: pending 0, new foreign-definition BODY-reading violations 0. Review: `evidence/probes/Rule10/final2/base-explicit-manual-review.json`.

final: 32 control probe runs, 520 per-case checks, 122 sealed negatives; each negative fails exactly once and every expected positive/unsealed case passes.

final explicit scan: 595 individually reviewed rows. Raw scanner foreign-definition candidates: 4; raw unresolved rows before manual review: 15. Final manual disposition: pending 0, new foreign-definition BODY-reading violations 0. Review: `evidence/probes/Rule10/final3/final-explicit-manual-review.json`.

The four raw final candidates are the following registered built-in simproc invocations:

- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean:124`, `TCSlib.Cryptography.Authentication.FromDiscreteLog.unitCollision_extract`: `↓reduceIte`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean:126`, `TCSlib.Cryptography.Authentication.FromDiscreteLog.unitCollision_extract`: `↓reduceIte`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:279`, `TCSlib.Cryptography.Authentication.dlHashEval_expF`: `↓reduceIte`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:281`, `TCSlib.Cryptography.Authentication.dlHashEval_expF`: `↓reduceIte`.

The finalized per-row review retains the pinned `builtin_simproc` registration and the
`.simproc` → `.addSimproc` elaborator path. These `↓reduceIte` items invoke the registered
simproc, which produces proofs through `ite_cond_eq_true` / `ite_cond_eq_false`; they do not
ask simp to unfold the metaprogram's definition body. The raw candidate counts remain 0/4
and raw unresolved counts remain 10/15; manual clearance means zero newly introduced
foreign-definition body readings, not zero raw candidates.

## Lint and explicit exceptions

Required lint: **222 FAIL / 102 WARN**, versus baseline **216 FAIL / 102 WARN**.
The exact six added FAIL entries are the frozen ancestor Hashing.lean facade's direct-import
diagnostics for Algebra, Coins, Encoding, Probability, Reduction, and Sampling. All six helpers are
exported through the owned FromDiscreteLog facade. The user explicitly authorized:

> Acknowledge exactly six lint false positives

This is an exception to literal zero-new-FAIL lint, not a claim that the lint mechanically passed.
No other added FAIL is accepted. Raw baseline/final logs and every changed WARN message are in
`evidence/style-delta-repaired.md` / `evidence/style-delta-repaired.json`; the inherited provider-size warning changes 1192 → 1209 lines,
and its missing-reader warning list drops expSampleRaw after its new equation reader.
The scoped provider exception preserves this pre-existing over-1000-line file without unrelated
splitting. Every owned/new hashing file remains below 1000 lines. No global simp attribute was added.

## Host, cache, and bootstrap

Resumption preflight: 12 CPUs; physical RAM 19,327,352,832 bytes; APFS free space
264,007,364,608 bytes (>12 GiB). Native non-cache memory-use proxy 12,238,684,160 bytes and
headroom proxy 7,088,668,672 bytes (>4 GiB). macOS lacks Linux cgroup/MemAvailable counters;
the native proxy is explicitly not claimed to be Linux MemAvailable. Raw native readings and
subsequent resource logs are retained under `evidence/logs/resume-1/`.
The user overrode host serialization to at most three Lean processes. This worker checks one
module at a time in its own olean tree and counts other host processes before launch. Exact
authorizations and the authorized coordination-note provenance are in `evidence/authorization.md`.

Only the 87 issued Mathlib roots were fetched. The narrowed cache command exited 0:
2,339 files decompressed, zero files downloaded, from the pre-existing hash-addressed archive store
(32,667 files; 1,595,387,830 bytes; precise originating sessions unknown). All 11 present packages
match manifest URLs/revisions; doc-gen4, UnicodeBasic, BibtexQuery, and MD4Lean are absent.
No empty olean was found; the Mathlib-root import probe and bootstrap passed. No dependency tree
was copied or reused from another session, and no memory-backed scratch filesystem was used.
Module timestamps and native maximum-memory outputs are retained. Checks standardized on Lean -j4
without self-imposed timeouts; earlier wrapper versions and their logs remain delivered.

## Patch reproduction and transport history

The complete 4-patch series from the exact issue base reproduces all eight changed/new files
byte-for-byte. `evidence/patch-reproduction-repaired/result.json` records every reproduced/head hash:

- `TCSlib/Cryptography/Candidates/DiscreteLog.lean`: `ef7cf001f483ce0a5c47025924ee9c10fb78a9b59f73e4e5482091ad05a2aa67`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean`: `9d500a96e0e112a092ec0f2e548c5a648752dba89faa4bee40272ef55fcf78d0`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean`: `adffb2ec4b9a064aa2a21948ab8a0b79510efda5b1d9be8b48bbc055e02bd221`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean`: `1ab5d3ece9c424a456e380d2e40eba45b6f0a8f76b69d12d03bd36842eecd6cb`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean`: `79669605ededcae778a0d719f0db5bd6a998f221ded322fd283c65e04411aaa4`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean`: `bf943d5aea5c9da86ada6d9171576b40949b96f2dc4882699dd66112f00f610b`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean`: `27e4d37dc581ff2db70336b8b19ce3a92531de09c0e42ff260a9ffd4685b04c6`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean`: `398337fbdf7e1e2d46f6658262ee47cf887a5d3707e18c6c8807dda9f0a55c15`.

Patch files:

- `0001-Prove-discrete-log-hash-compression-and-collision-ex.patch`.
- `0002-Prove-the-collision-finder-reduction-recovers-discre.patch`.
- `0003-Complete-the-discrete-log-hash-collision-resistance-.patch`.
- `0004-Make-dependent-length-transports-explicit-under-Rule.patch`.

Exchange records already pushed only under `inbox/fills/dl-crh/`:

- checkpoint 1: reader escalation: `396c734fac3ba4a0e8d06320517f56017962f734`.
- initial escalation final record (proof remained admitted): `dc9846a2d46aca5be8fe6d48f2c9064090a48014`.
- checkpoint 2: compression and collision shape: `cb64931761fae93c916535fc454f8c5a5a4bcab0`.
- checkpoint 3: concrete reduction and collision-to-DL success: `88cca5e5dd801753da004f86c982f1f80f0a270a`.

The final exchange push identity belongs in the final chat, not recursively inside its own payload.
The payload contains REPORT.md, the full patch series, exact src bytes, and all evidence. Packaging
generates manifests after this report and verifies exact path-set/hash equality and ZIP bytes; its
actual output is retained separately. The fallback ZIP has `dl-crh/` at its root.

## Bound report inputs

- `evidence/probes/Rule10/final3/summary.json`: `fa1887f91bae1faaa9b5620942e463d11ae87cbc1bef56aad2db197ecc60438b`.
- `evidence/probes/Rule10/final2/base-explicit-manual-review.json`: `9ff0fcf99932d2a46b42d9e086a333f1425d8bca6cb651ad5236794a48256afd`.
- `evidence/probes/Rule10/final3/final-explicit-manual-review.json`: `110377418a1d9992224a598bb8ee6477906b7ccd961cf172eedac2850591e3b6`.
- `evidence/admission-delta-repaired.json`: `b133743a17f1b9573501b63de18978dc2e53ee1b016ead9c913df01d96a9decd`.
- `evidence/style-delta-repaired.json`: `cc01140ef7ea2ea98593708354a1604df6ec5698e38dcab2021099bf63ceb2af`.
- `evidence/new-declarations-final3.json`: `f94d72655e4cabcf6f8467dde3d80f6a104d442ffa245d53b33c43bc60e15a2c`.
- `evidence/proof-route-final3.md`: `b2b816a6f1ae755106cf816d096947465944321a274bf7c60e06f2e10b415738`.
- `evidence/logs/final-source-preservation-repaired.json`: `3805dfc5098162881b07d706421559a784d8b7bbae8f00e3eb22fde7beba4b9d`.
- `evidence/patch-reproduction-repaired/result.json`: `78f92a60be48ca49eced8b86c3d24165fc98aaddc901a0befcca3c7a7397f29b`.
- `evidence/logs/rule10/final2/seals-final/results.jsonl`: `c01d37a576d9c150c8aa18cb34059ed3dbebaf5d06ca9c8bd5fbbdd432200094`.
- `evidence/probes/Rule10/final2/seal-provenance.json`: `47da8df048526401948663d2c5f89d5252b546a382bdacc9df67773913fc5178`.
- `evidence/probes/Rule10/final3/baseline-reuse.json`: `f111e21dd9b7ce9a20e426f0a89b02d9a875294f589a36d4dfb6550ddee128b4`.

Proof commit: `fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16`. Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
