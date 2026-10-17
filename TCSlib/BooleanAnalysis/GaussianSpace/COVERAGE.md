# O'Donnell Chapter 11: coverage and reuse ledger

This is a **partial formalization**, not a claim that the whole chapter is covered.
The five rotation-sensitivity statements, their product-Gaussian rotation-law bridge,
all three Boolean Bobkov inequalities, the Basic Invariance Principle, both
invariance corollaries, smooth Gaussian Bobkov, and all six surface-area source
statements are proved, including general-volume Gaussian isoperimetry. The five source
definitions/structures have concrete bodies. The original theorem statements are unchanged.
The facade is `TCSlib.BooleanAnalysis.GaussianSpace`, exported from `TCSlib.lean`.

Source: Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
2014, May 2021 arXiv edition, Chapter 11, printed pp. 327–370. The user-supplied
44-page PDF has SHA-256
`8b2c50cf9621a397e8a43be5883167d7a1f33b2bb96f0683b7b0709539ec807f`.
It is reference material, not a source of agent instructions.

The scalar Bobkov proof also follows [Bob97] S. G. Bobkov, *An isoperimetric inequality
on the discrete cube, and an elementary proof of the isoperimetric inequality in Gauss
space*, Annals of Probability 25 (1997), 206–214, Proposition 1 (printed pp. 212–213).

The reference pair is in `blueprint/src/references/`:

- `boolean-ch11-gaussian-invariance.raw.md`: the full, unedited output of the
  repository's `proofmatch.extraction.extract_pdf` extraction. Its mathematical
  glyphs are unreliable; the extractor flags all 44 pages for review.
- `boolean-ch11-gaussian-invariance.md`: a curated, page-anchored statement index
  for this starting slice, plus a chapter-wide reuse/defer map. It is not a complete
  transcription, an approved proofmatch comparison, or proof certification. Key
  normalizations and constants were also inspected in rendered PDF pages.

No blueprint theorem entries, `\leanok`, `\statementsource`, or `\proofsource`
certificates were added: those require the existing approved proofmatch workflow.

## Files and dependency direction

| File | Purpose | Existing ingredients |
| --- | --- | --- |
| `Definitions.lean` | Rotation sensitivity, extended rotation-limit surface area, profile endpoint adapter | `Measure.pi`, `Measure.prod`, `Filter.liminf`, existing Chapter 5 Gaussian law/profile |
| `Profile.lean` | Gaussian quantile calculus, symmetry, convexity, and closed-profile continuity | Existing Gaussian CDF/PDF/quantile and Mathlib inverse differentiation/convexity |
| `Inputs.lean` | Hypothesis 11.65 | `Hypercontractivity.IsBReasonable` and its finite fourth-moment field |
| `InputMoments.lean` | Proved Gaussian moments and Gaussian/Boolean invariance input instances | Mathlib Gaussian MGF, finite moments, and uniform finite laws |
| `GaussianDensity.lean` | Proved scalar density differentiation and bounded Lipschitz first derivatives of Gaussian averages | Parametric integration, Gaussian moments and integrable envelopes |
| `ProductDensity.lean` | Proved product density and affine Gaussian integration formulas | Finite-product integration and scalar Gaussian law transformations |
| `ProductDifferentiation.lean` | Proved continuous differentiability of bounded product Gaussian averages | Scalar envelopes, product rule, parametric integration and dominated convergence |
| `ProductBounds.lean` | Proved first/Hessian coordinate kernel integrability and moment bounds | Explicit quadratic domination and Gaussian coordinate second moments |
| `ProductHessian.lean` | Proved second differentiation and Lipschitz first derivatives of product Gaussian averages | Local integrable Hessian envelopes, coordinate moment bounds, and the mean value inequality |
| `Rotation.lean` | Proved rotation subadditivity and balanced grid bound | Mathlib Gaussian rotation invariance, product-law equivalences, symmetric differences, and finite sums |
| `Halfspace.lean` | Proved unit Gaussian projection and normalized halfspace crossing limit | Existing weighted Gaussian sums, Gaussian CDF calculus, and dominated convergence |
| `IndicatorSmoothing.lean` | Proved exact integral approximation, mean preservation, and contraction of rotation variation | Existing Gaussian rotation coupling, product-measure conditioning, and the four-Gaussian coupling |
| `IndicatorRegularity.lean` | Proved differentiability and bounded Lipschitz derivatives of averaged indicators | Product-density representation and cosine scaling of the existing derivative |
| `ProfileApproximation.lean` | Proved vanishing profile integral for averaged indicators | Compact uniform continuity, exact integral approximation, and rotation continuity |
| `SmoothVariation.lean` | Proved smooth gradient bound from normalized rotation variation | Chain rule, Gaussian directional moments, Tonelli, and Fatou |
| `SurfaceArea.lean` | Proved surface-area limits, halfspace formula, and Gaussian isoperimetry | Rotation bounds, Gaussian Bobkov, smooth variation, and averaged indicators |
| `Bobkov.lean` | Boolean two-point/full inequalities and noise monotonicity | `expect`, `derivative`, `noiseOp` |
| `Bobkov/TwoPoint.lean`, `Cube.lean` | Scalar profile estimates and cube length identities | Bobkov's original calculus proof, existing coordinate restrictions and Euclidean norms |
| `Bobkov/Interpolation.lean`, `Noise.lean`, `Tensorization.lean` | Symmetric-pair contraction and dimension induction | Mathlib concavity/compactness, existing noise kernel and semigroup law |
| `BooleanBlocks.lean` | Proved finite-index and array Boolean Bobkov adapters | Existing cube Bobkov, coordinate equivalences, finite currying |
| `Bobkov/DiscreteApproximation.lean` | Proved first-order Taylor control of normalized Boolean block derivatives | Lipschitz derivatives, coordinate updates, and the mean value inequality |
| `GaussianBobkov.lean` | Proved smooth Gaussian Bobkov and additive profile/gradient bound | Normalized Boolean block convergence, discrete Taylor bounds and Euclidean length estimates |
| `Invariance.lean` | General-input C4 invariance and two quantitative corollaries | Existing multilinear polynomials/evaluation, independence, cube variance/influence, iterated derivatives |
| `NormalizedSums.lean` | Proved degree-one Lipschitz Gaussian approximation | Fourth-order invariance, Gaussian projection, and the input-moment instances |
| `NormalizedBlocks.lean` | Proved finite-dimensional normalized Boolean block convergence | Scalar comparison, Mathlib Portmanteau and continuity of finite products |
| `Invariance/Coordinates.lean`, `Moments.lean` | Coordinate decomposition and fourth moments | Existing cube derivative, coefficient identities, general-input Bonami |
| `Invariance/Taylor.lean`, `Replacement.lean` | Cubic cancellation and single-coordinate replacement | Mathlib Taylor theorem, independent integration, finite fourth moments |
| `Invariance/Sequence.lean`, `Smoothing.lean` | Telescoping, law transport, and Lipschitz smoothing | Product marginals, identical distributions, Mathlib interval averages and calculus |

The geometric definition layer does not import the Boolean Fourier/Bonami development.
`Inputs` supplies that independent definition layer for `Invariance`.

## Added source statements

Names below are relative to `BooleanAnalysis.GaussianSpace`.

| Source | Declaration | Status / representation note |
| --- | --- | --- |
| Def. 11.42 | `rotationSensitivity` | Concrete definition, using the ellipse coupling in the proof of Thm. 11.43 |
| Thm. 11.43 proof | `measurePreserving_gaussianRotation` | Proved adapter: coordinatewise Mathlib rotation invariance preserves the existing product Gaussian vector law |
| Thm. 11.43 | `rotationSensitivity_subadditive` | Proved binary-angle statement via rotation invariance and the symmetric-difference triangle inequality |
| Thm. 11.43 | `rotationSensitivity_sum_le` | Proved full finite-angle statement using Mathlib's finite-sum bound for subadditive functions |
| Thm. 11.43, final assertion | `rotationSensitivity_div_nat` | Proved equal-step statement with positive integer divisor |
| Cor. 11.44 proof; Thm. 11.52 proof | `rotationSensitivity_pi_div_two` | Proved exact independent-endpoint formula `2α(1-α)` |
| Cor. 11.44 | `rotationSensitivity_balanced_grid` | Proved for volume one half and angle `π/(2ℓ)` |
| Def. 11.48 | `gaussianSurfaceArea` | Concrete ENNReal lower-limit definition; right-limit equivalence is proved |
| Def. 11.48; Eq. (11.14) | `surfaceArea_rotation_limit` | Proved, including infinite surface area, by continuity and subadditivity |
| Discussion preceding Def. 11.48 | `surfaceArea_congr_ae` | Proved via equality of every rotation sensitivity under null modifications |
| Prop. 11.49 | `surfaceArea_halfspace` | Proved for a closed halfspace with unit normal and arbitrary threshold by conditional CDF increments |
| Thm. 11.51 | `rotationSensitivity_le_surfaceArea` | Proved for every positive angle by the subadditive lower-limit bound |
| Thm. 11.52 | `surfaceArea_volume_lower_bound` | Proved by independence at angle `π/2` and normalization |
| §11.4, Gaussian Isoperimetric Inequality | `gaussian_isoperimetric` | Proved for interior volume `α∈(0,1)` through smooth Gaussian Bobkov and averaged indicators; endpoint bound is ENNReal nonnegativity |
| Def. 5.26; §11.4, Eq. (11.15) | `closedGaussianProfile` | Concrete adapter: reuse the existing interior profile and set endpoint values to zero |
| §11.4, Eq. (11.15) | `bobkovFunctional` | Concrete expected length using the existing discrete gradient |
| §11.4, Bobkov's Two-Point Inequality | `bobkov_two_point` | Proved on the full closed interval, including endpoints, using [Bob97, Proposition 1] |
| §11.4, Bobkov's Inequality (11.15) | `bobkov_inequality` | Proved for all `[0,1]`-valued cube functions by coordinate induction and the triangle inequality |
| §11.4, Gaussian Bobkov | `gaussian_bobkov_smooth` | Proved for unit-interval functions with explicit bounded Lipschitz derivative family |
| Thm. 11.55 | `bobkovFunctional_noise_monotone` | Proved on correlation interval `[0,1]`; deterministic bounded-supremum argument replaces the source's stopped walk |
| Hyp. 11.65 | `HasInvarianceMoments` | Concrete Prop structure reusing 9-reasonability |
| §11.6, Basic Invariance Principle, Eq. (11.29) | `basic_invariance_principle` | Proved exact `(C/12)9^k Σ Inf²` bound for arbitrary independent input laws |
| Cor. 11.67 | `invariance_small_influences` | Proved exact `(C/12)k9^k ε` bound |
| Cor. 11.68 | `invariance_lipschitz` | Proved universal `K c 2^k ε^(1/4)` bound with explicit `K = 16`; four interval averages replace the source's mollifier |

The Basic Invariance Principle is **unnumbered** in this edition. Definition 11.63,
Remark 11.64, and Hypothesis 11.65 precede it; it should not be cited as Theorem 11.64.

## Local reuse: no parallel definitions or restatements

- `ThresholdFunctions/GaussianTail.lean` already defines `standardGaussianMeasure`,
  PDF, CDF, tail, quantile, and `gaussianIsoperimetric`. These supply Notation 11.1.
  Its profile is a totalized real-quantile expression intended on `(0,1)`, so the
  zero endpoint adapter is necessary for Bobkov's full `[0,1]` statement. No new
  Gaussian density, quantile construction, or interior profile is introduced.
  `Profile.lean` derives quantile/profile derivatives, reflection, squared-quantile
  convexity, and continuity of the endpoint adapter from those existing definitions.
  The Bobkov proof uses the existing cube derivatives, restrictions, finite expectation,
  noise kernel, zero-dimensional identity, and semigroup law. Its interpolation helper
  generalizes to continuous nonnegative profiles satisfying the scalar two-point bound
  and carries arbitrary extra Euclidean coordinates through the dimension induction.
- `ThresholdFunctions/Gaussian.lean` already contains `kolmogorovDistance`,
  `berryEsseen` (currently `sorry`), `gaussianQuadrantProbability`, the proved
  `sheppard_formula`, `majority_stability_limit`, and `majority_is_stablest`
  (currently `sorry`). Even an existing `sorry` statement is excluded from new skeletons.
- `ThresholdFunctions/Basic.lean` supplies `MultilinearPolynomial`, `.eval`,
  `.HasDegreeAtMost`, noise stability, and maximum influence. `Polynomial.lean`
  supplies `MultilinearPolynomial.fourierCoeff_eval`.
- `Hypercontractivity/RandomVariables/Basic.lean` supplies `evalMultilinearRV` and
  `evalMultilinearRV_memLp`; `RandomVariables/Polynomial.lean` supplies the proved
  `independent_multilinear_reasonable` fourth-moment estimate needed by the proof plan.
  The shared `RandomVariables/Moments.lean` now supplies orthonormal monomial and
  polynomial first/second-moment identities, together with coordinate-support evaluation lemmas.
- `Hypercontractivity/MomentBounds.lean` supplies `IsBReasonable`.
- `Hypercontractivity/Cube/Basic.lean` supplies `cubeVariance`; influence and its
  coefficient formulas already exist in `BooleanAnalysis/Basic.lean`.
  Thus Def. 11.63 uses `cubeVariance F.eval` and `influence i F.eval`, with no new
  coefficient-variance/influence definitions.
  The shared cube layer now also bounds total influence by degree times variance and
  the squared-influence sum by degree times the maximum influence under variance at most one.
- Existing `KKL.noisyInfluence`, `lowDegreePart`, and `highDegreePart` are the
  planned inputs for Cor. 11.69; do not add another truncation/notability API.
- Mathlib already supplies `MemLp`, `Lp`, integrals, product measures, independence,
  iterated derivatives, distance to sets, and smoothing infrastructure.
  The Lipschitz proof uses four native interval averages: the approximation error is
  `4cη`, and the fourth derivative is bounded by `8c/η³`. Its general expectation-comparison
  helper also covers separate probability spaces and zero comparison scale.
- `ProbabilityTheory.IsGaussian.map_rotation_eq_self` supplies centered Gaussian
  rotation invariance. `Rotation.lean` lifts the scalar result through
  `measurePreserving_pi` and `measurePreserving_arrowProdEquivProdArrow`; no new
  Gaussian construction or external package is needed. All six declarations in
  `Rotation.lean` were checked with Lean LSP and use only `propext`,
  `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## External duplication audit (2026-10-14)

This was source inspection, not installation or fresh upstream kernel checking.
No external code or design was copied; the new statements and proof plans follow OD14.
The checked-out project remains on Lean 4.25.0 with Mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Toolchains/dependencies were not changed.

| Library and inspected revision | Concrete source evidence | Decision |
| --- | --- | --- |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e) | `RingTheory/Polynomial/Hermite/{Basic,Gaussian}.lean`: `Polynomial.hermite`, recurrence, degree, and Gaussian derivative formulas | Do not redefine probabilists' Hermite polynomials (Def. 11.29) |
| [gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert/tree/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e), Lean 4.30.0 | `GaussianHilbert/HermitePolynomials.lean`: `hermiteEval`, `hermiteMultiEval`, `stdGaussianFin`, `hermiteMulti_orthogonality`, `hermiteMulti_dense`; `WienerChaos.lean`: Hilbert sum/projections | Omit Hermite/product-Gaussian/density/basis duplicate skeletons; normalization and local API integration remain future work |
| Same revision | `OUEigenfunctions.lean`: `ouGenerator1D`, `ouGenerator`, `mehlerFun`, `mehlerOp`, `ouSemigroupAct`, `mehlerOp_eq_ouSemigroupAct`; `HypercontractivityFromBE.lean`: `ouSemigroupAct_eLpNorm_hypercontractive` | Omit overlapping OU/noise/spectral/hypercontractivity statements; time parameter is `t≥0`, correlation `exp(-t)` |
| [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups/tree/0b5dd80ad918f7e8ab23bb2fac5eb9c7d373a795), Lean 4.30.0 | `MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`: `GaussianFin.ouSemigroupFin_mean`, `_contraction`, `_selfAdjoint`, `_compose`, `_gradient_decay`; `EuclideanHypercontractive.lean`: `stdGaussianFin_satisfiesLogSobolev`, `stdGaussianFin_isHypercontractive` | Omit duplicated foundation; some statements use an explicit regularity/core domain, so full OD14 domain coverage is not asserted |
| [ProbabilityApproximation](https://github.com/Polarnova/ProbabilityApproximation/tree/a2fc5bda874d9b69186c0ba165bf79f3b9897662), Lean 4.32.0 | `ProbabilityApproximation/ChenShao/{NonuniformBerryEsseen,UniformBerryEsseen}.lean`: `nonuniformBerryEsseen`, `uniformBerryEsseen_thirdMoment` | Exclude Berry–Esseen (including the user's example) and already-covered scalar normal-approximation statements |
| Same revision | `ConvexGeometry/GaussianShell.lean`: `standardGaussianBoundaryContent`; `BallGaussianPerimeter.lean`: `standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant` | Do not duplicate the Gaussian-weighted frontier Hausdorff integral or convex perimeter upper bound |
| [openai/math](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a), Lean 4.34.1 | `lean/OAI/Computability/MaxCut/Estimates/Clip.lean`: `OAI.OptimalMaxCut.MISProof.majority_is_stablest`, `untruncated_majority_is_stablest`; `Degree.lean` | Exclude balanced MIS; inspected proof files have substantive proofs, but their transitive dependencies were not freshly kernel-checked |
| [atlas-lean](https://github.com/facebookresearch/atlas-lean/tree/8004bc185206d3d34cc6a7cf0840edca89cf64ce), `v1/Atlas/BooleanFunctions/code/` | `GaussianStability.lean` defines correlated noise/operator/stability; `Borel.lean` and `GaussianBorelCorollary.lean` state balanced/general halfspace extremality; `MajorityStablest.lean` states MIS variants | Exclude equivalent definitions/statements even where upstream proof obligations remain `sorry` |
| Same revision | `Invariance.lean`: C3 **Boolean-to-Gaussian** invariance, with error proportional to `2^(3d/2) Σ Inf^(3/2)`; `LindebergBound.lean` has a supporting `sorry` | Distinct from the added **arbitrary-law C4** estimate with exact `(C/12)9^k Σ Inf²`; do not duplicate the C3 theorem |

The source's rotation-limit area is deliberately different from the frontier Hausdorff
integral: the former is invariant under null modifications, whereas the latter need not
be for arbitrary sets. A comparison on sufficiently regular sets is integration work,
not an asserted global equality. No theorem about the upstream frontier integral is
repeated here.

The current concrete Gaussian hypercontractivity proofs were inspected separately from
older module prose mentioning abstract axioms. Upstream audit prose is not treated as
a fresh transitive-axiom check in this project.

Search boundary: all local `TCSlib/BooleanAnalysis` sources; pinned Mathlib; direct
inspection of the repositories above; targeted public GitHub/web searches for Hermite,
OU, Borell, Bobkov, invariance, rotation sensitivity, Gaussian surface area, and MIS.
`shlyakhtenko/free-bobkov-hermite` concerns a different free/semicircle inequality and
was not comprehensively audited. No equivalent of the added statements was found in
this bounded search. Global nonexistence across GitHub cannot be certified by search.

## Chapter-wide omissions and next integration steps

| Source range | Reuse / explicit remaining work |
| --- | --- |
| §11.1, Notation 11.1–Fact 11.13 | Reuse local Gaussian laws and Mathlib Lp; upstream correlated/Mehler noise exists. Independent normalized Boolean blocks and their finite-dimensional Gaussian convergence are now proved using the existing cube API. |
| §11.1, Props. 11.15–11.17; Thms. 11.22–11.23 | External contraction/smoothing/density/hypercontractivity overlap. Audit full Lp endpoints and negative correlations before proposing any genuinely missing bridge. |
| §11.1, Def. 11.24–Prop. 11.28; Gaussian LogSob | Reuse external OU calculus/LogSob; operator domains and core-to-L2 closure need explicit integration. No vague-domain skeleton is added. |
| §11.2, Def. 11.29–Prop. 11.40 | Mathlib Hermite polynomials and upstream Gaussian Hilbert/chaos/spectral theory. Normalization and coefficient/L2 transport remain future adapter work. |
| §11.3, Borell; Cor. 11.20/Sheppard material | Existing local Sheppard and external Borell statements. Only the distinct rotation-sensitivity development is new. |
| §11.4, Def. 11.48 relaxation/Minkowski equivalences | The rotation definition/right-limit assertion, the one-sided smooth gradient bound, and averaged-indicator approximation are proved. Full relaxation/attainment equalities and sufficiently regular boundary comparisons remain deferred until their exact function/set classes are fixed. |
| §11.4, Example 11.50 | Convex upper bounds already external. Ball/PTF bounds and interval formulas are deferred for representation/overlap review, not silently counted as covered. |
| §11.4, Claim 11.54 | A proof-internal stopped-walk claim; no new stochastic-process model is introduced in this starting skeleton. |
| §11.5, Def. 11.57 and smoothing/scalar consequences | Reuse Mathlib distance/mollification APIs and external Berry–Esseen. Exact remaining scalar test-function adapters are deferred. |
| §11.6, Def. 11.63; Hyp. 11.65; Eq. (11.29); Cors. 11.67–11.68 | Existing polynomial/variance/influence APIs plus the new moment bundle and three general-law invariance statements. |
| §11.6, Remark 11.66; Cors. 11.69–11.70; Carbery–Wright; Thm. 11.71 | Existing C3 overlap is excluded. Smoothed/no-notables, Lévy/CDF bounds, and arbitrary-polynomial anticoncentration require their own representation/duplication review before addition. |
| §11.7, Thms. 11.72–11.74; general-volume MIS (11.39) | Existing balanced MIS is excluded. Max-Cut/UG-hardness models and the exact quantitative general-volume/no-notables bound are deferred, not replaced by a weaker fresh MIS statement. |
| Exercises and historical notes | Reference extraction retains them; they are outside this starting slice. |

External libraries are **reuse/integration targets**, not imports already available in
this Lean 4.25.0 environment. Changing the toolchain or adding dependencies needs a
separate request. Incompatible upstream availability is not a reason to copy a theorem
into another `sorry` skeleton.

## Validation

See `VALIDATION.md` for language-server diagnostics, axiom inspection, independent
semantic review, and repository hygiene checks. The completed source statements
have no `sorry` dependencies; unrelated chapter results remain outside this scope.
