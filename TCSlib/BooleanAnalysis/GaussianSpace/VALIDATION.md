# Chapter 11 validation record

The opening sections record the original 2026-10-14 skeleton. The completion
records below give the later proof and verification status.

Validated 2026-10-14 in the existing Lean 4.25.0 project environment. This is a
statement-only contribution: **17 new theorem/lemma statements remain unproved**.
The five definitions/structures have concrete bodies. No existing `sorry` was filled.

## Lean language-server checks

The Lean language server reported `partial: false`, `timed_out: false`,
`success: true`, and no failed dependencies for every file below:

| File | Errors | Intended `sorry` warnings |
| --- | ---: | ---: |
| `GaussianSpace/Definitions.lean` | 0 | 0 |
| `GaussianSpace/Inputs.lean` | 0 | 0 |
| `GaussianSpace/Rotation.lean` | 0 | 5 |
| `GaussianSpace/SurfaceArea.lean` | 0 | 6 |
| `GaussianSpace/Bobkov.lean` | 0 | 3 |
| `GaussianSpace/Invariance.lean` | 0 | 3 |
| `BooleanAnalysis/GaussianSpace.lean` facade | 0 | 0 |
| `TCSlib.lean` root export | 0 | Error-filtered query |

These are completed language-server elaboration diagnostics in the current
environment, not a claim of a from-clean project build or a sorry-free project.
No shell `lean`, `lake build`, toolchain changes, or dependency updates were used.
An initial nonexistent Mathlib import and a missing NNReal notation scope were
corrected before these final results; transient dependency-load failures did not
remain in the completed diagnostics.

## Transitive axiom inspection

`lean_verify` reported exactly `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`, for all five new completed definitions/structures:

- `BooleanAnalysis.GaussianSpace.rotationSensitivity`
- `BooleanAnalysis.GaussianSpace.gaussianSurfaceArea`
- `BooleanAnalysis.GaussianSpace.closedGaussianProfile`
- `BooleanAnalysis.GaussianSpace.HasInvarianceMoments`
- `BooleanAnalysis.GaussianSpace.bobkovFunctional`

Representative theorem checks, covering every theorem-bearing module, reported
the same standard axioms **plus the expected `sorryAx`**:

- `rotationSensitivity_subadditive`
- `gaussian_isoperimetric`
- `bobkov_inequality`
- `basic_invariance_principle`
- `invariance_lipschitz`

Source inspection confirms that every one of the 17 theorem/lemma bodies is just
`sorry`, with no proof attempt or axiom disguised as a completed theorem.
Upstream external repositories were source-audited, not imported or kernel-checked
in this environment; their proof status is separately qualified in `COVERAGE.md`.

## Independent semantic review

A separate read-only reviewer compared all 22 new public mathematical declarations
with the chapter source and the reused local definitions. It found no mathematical
fidelity blockers. The review explicitly checked:

- `sqrt(π/2)` rotation-to-area normalization and infinite `ENNReal` limits;
- unit-normal halfspace coefficients and measurable-set hypotheses;
- Bobkov's discrete derivative scaling and zero profile values at both endpoints;
- exact `C/12`, `9^k`, and `k9^k` invariance constants;
- finite fourth moments, independence, and distinct input probability spaces;
- the universal Lipschitz constant preceding all laws, dimensions, and tests.

The reviewer originally noted that `COVERAGE.md` was missing during its read; the
ledger has since been created. This is model semantic judgment, not kernel proof
or human approval. The external duplication audit was a separate read-only role.
The completed-proof formalization harness was not used because accepting a filled
proof would conflict with the user's explicit instruction to leave all sorries.

## Repository and reference checks

- `scripts/style_lint.py` on all seven new Lean files: **0 findings**.
- The curated reference index parses with the existing proofmatch document parser:
  **28 page-anchored blocks**, with the supplied PDF's SHA-256.
- Full raw extraction: **44 pages**, all flagged by the extractor for mathematical
  glyph/layout review. It is retained as raw evidence, not claimed as clean math.
- `scripts/dataset_hygiene.py --strict`: **0 hard failures**; it reports 229 existing
  advisory flags across 6902 existing blueprint entries.
- `git diff --check`: passed. Direct whitespace inspection also included the new
  untracked files, which ordinary `git diff --check` alone does not inspect.
- `scripts/blueprint_validate.py --strict`: **fails on 890 existing orphan `\lean`
  labels**, with 0 dangling `\uses` references and 0 dependency cycles. This task
  changes no blueprint theorem entries, dependency graph, or existing labels; the
  new chapter adds no such references. Repairing that existing project-wide index
  is outside this chapter-skeleton change.

No `\leanok`, approved proofmatch source certificate, or completed-proof claim was
created for the new theorem stubs.

## Invariance completion (2026-10-16)

All three original statements in `Invariance.lean` now have complete proofs, with
their quantifiers, assumptions, domains, and conclusions unchanged:

- `basic_invariance_principle`: the exact `(C/12) 9^k ∑ᵢ Infᵢ²` estimate.
- `invariance_small_influences`: the exact `(C/12) k 9^k ε` estimate.
- `invariance_lipschitz`: the universal estimate with the explicit witness `K = 16`.

The proof chain reuses the existing polynomial representation, evaluation, cube
derivative, variance, influence, and general-input Bonami theorem. Shared monomial
and polynomial moment identities live in `Hypercontractivity/RandomVariables/Moments.lean`.
The polynomial-to-Fourier degree bridge lives in `ThresholdFunctions/Polynomial.lean`;
the degree/variance and squared-influence bounds live in `Hypercontractivity/Cube/Basic.lean`.
The six `Invariance/` modules separate coordinate decomposition, fourth moments,
Taylor cancellation, coordinate replacement, telescoping/law transport, and smoothing.

The Lipschitz argument uses four native Mathlib interval averages in place of the
source's mollifier. The approximation error is at most `4cη`, and the fourth
derivative is at most `8c/η³`. The general expectation-comparison lemma gives
`16cB^(1/4)` from a smooth-test bound `CB`, including `B = 0` by a limit.

### Completed language-server checks

Fresh diagnostics for all 13 touched Lean files reported `partial: false`,
`timed_out: false`, `success: true`, no errors or warnings, and no failed dependencies:

- `GaussianSpace.lean`, `GaussianSpace/Inputs.lean`, and `GaussianSpace/Invariance.lean`;
- all six `GaussianSpace/Invariance/` modules;
- `Hypercontractivity/RandomVariables.lean` and `RandomVariables/Moments.lean`;
- `Hypercontractivity/Cube/Basic.lean` and `ThresholdFunctions/Polynomial.lean`.

Actual `#print axioms` commands in the active language-server file reported exactly
`propext`, `Classical.choice`, and `Quot.sound` for each of the three original
theorems, with **no `sorryAx`**. The helper declarations were also checked during
construction. Temporary axiom-print commands were removed afterward; the final
`Invariance.lean` diagnostics are empty.

No shell `lean`, `lake build`, dependency updates, or toolchain changes were used.
Checks and normal import rebuilding were handled through Lean LSP. This is completed
file/declaration validation, not a claim of a from-clean whole-project build.

### Semantic review and hygiene

Separate read-only semantic reviewers checked the source fidelity, exact constants,
existing representations, integrability, independence, separate probability spaces,
and zero-degree, zero-dimensional, zero-influence, and zero-Lipschitz cases. The
final review found no actionable issues. These reviews are model judgment, separate
from the Lean/kernel evidence and from human approval.

- `scripts/style_lint.py`: **0 findings in all 13 touched Lean files**.
- `git diff --check`: passed; direct checks also cover untracked invariance/moment files.
- Source scans: no `sorry`, `admit`, or temporary axiom-print commands in the completed
  invariance and shared moment files.
- All six helper modules are imported by the invariance facade, which is exported
  through `GaussianSpace.lean` and the existing `TCSlib.lean` import.

The six surface-area and three Bobkov source proofs remain `sorry` and are outside
this invariance task. No blueprint theorem entries, approved proofmatch source
certificates, or `\leanok` markers were changed.

## Bobkov completion (2026-10-17)

All three original statements in `Bobkov.lean` now have complete proofs, preserving
their quantifiers, assumptions, domains, and conclusions:

- `bobkov_two_point`: the full closed-interval scalar inequality, including endpoints.
- `bobkov_inequality`: the inequality in every Boolean-cube dimension, including zero.
- `bobkovFunctional_noise_monotone`: monotonicity throughout correlation interval `[0,1]`.

`Profile.lean` reuses the existing Gaussian law, CDF, density, quantile, and interior
profile. `Bobkov/TwoPoint.lean` follows the elementary calculus proof in Bobkov's
1997 paper, Proposition 1, printed pp. 212–213. `Bobkov/Cube.lean` separates the
restriction and expected-length identities. `Interpolation.lean` replaces the
source's stopped walk by a deterministic bounded-supremum maximum principle,
generalized to any continuous nonnegative profile satisfying the scalar two-point
bound and any finite vector of extra coordinates. `Noise.lean` supplies interval
preservation and coordinate identities. `Tensorization.lean` inducts uniformly in
the extra-vector dimension; the noise semigroup then compares two correlations.
All nontrivial proofs carry source references and matching mathematical sketches.

### Completed language-server checks

Fresh Lean LSP diagnostics for all nine touched Lean files reported `partial: false`,
`timed_out: false`, `success: true`, no errors or warnings, and no failed dependencies:

- `GaussianSpace.lean` and `GaussianSpace/Definitions.lean`;
- `GaussianSpace/Profile.lean` and `GaussianSpace/Bobkov.lean`;
- all five `GaussianSpace/Bobkov/` modules.

Actual `#print axioms` commands in the active language-server file reported exactly
`propext`, `Classical.choice`, and `Quot.sound` for each of the three original
theorems, with **no `sorryAx`**. This direct check resolved an inconclusive response
from the `lean_verify` wrapper. The temporary print commands were removed, and the
final file diagnostics are empty.

No shell `lean`, `lake build`, dependency updates, or toolchain changes were used.
These are completed file/declaration checks through Lean LSP, not a claim of a
from-clean whole-project build or a sorry-free project.

### Independent review and hygiene

A separate read-only reviewer checked mathematical fidelity, Gaussian endpoint
continuity, discrete derivative scaling, the symmetric-pair maximum principle,
dimension induction with carried coordinates, and the zero/positive correlation
cases. The final review found no unresolved issues. This is model semantic judgment,
separate from the Lean/kernel evidence and human approval.

- `scripts/style_lint.py`: **0 findings in all nine touched Lean files**.
- `git diff --check` and direct whitespace checks on the new files: passed.
- Source scans: no `sorry`, `admit`, new axioms, or temporary axiom-print commands in
  `Profile.lean`, `Bobkov.lean`, or its five helper modules.
- The Bobkov facade imports every helper module, and the GaussianSpace facade
  exports `Profile` and `Bobkov` through the existing `TCSlib.lean` import.

The six surface-area source proofs remain `sorry`. No blueprint theorem entries,
approved proofmatch certificates, or `\leanok` markers were changed.
