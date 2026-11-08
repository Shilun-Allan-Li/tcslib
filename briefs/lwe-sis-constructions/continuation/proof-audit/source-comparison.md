# Targeted primary-source comparison during the proof audit

The user has dispatched the construction-core proof audit. This independent
maintainer review keeps its Lean/root freeze
`690217cc1aaefe411158808a8b0797fd887a8abc` unchanged. It is not an external
verdict, complete document validation, approved proofmatch or source-policy closure.

The exact previously archived PDFs were rehashed, then nine complete relevant
pages were rendered and visually inspected. `source-page-review.json` records
their hashes, one-based PDF pages, rendering commands and image fingerprints.
The reference documents and images remain in this checkout's own source archive;
no shared reference file, registry or dataset is changed.

## Checked correspondences

PDF page numbers and printed page numbers differ. Paths below are relative to
`TCSlib/Cryptography/`.

| Source anchor | PDF / printed page | Formalization correspondence and limitation |
|---|---|---|
| Pei16, Definition 4.1.1 and Equation (4.1.1) | 20 / 18 | `SIS/Basic.IsSolution` requires a nonzero integer vector in the modular kernel. The formalization explicitly uses a natural squared-norm budget, rather than the source's real Euclidean norm radius. Boundary dimensions are allowed by the definition; hardness is a separate hypothesis. |
| Pei16, observations after Equation (4.1.1) | 20–21 / 18–19 | `Hashing/SIS/Basic` uses the binary domain, integer differences, squared norm at most the number of columns, strict cardinal compression and pigeonhole. The source supports exactly this collision-to-SIS route. |
| Pei16, same observations | 20 / 18 | `Hashing/SIS/Profiles` checks squared budget below modulus squared, excluding nonzero modulus-multiple vectors. Its exact dyadic choices are local, not source-stated hardness parameters. |
| Pei16, Definitions 4.2.1 and 4.2.3 | 24 / 22 | `LWE/Basic` has integer scalar errors, uniform public vectors and one common uniform secret for all samples. Rows transpose the source presentation. Finite-seed noise and the machine-indexed `DLWEAssumption` are explicit implementation/asymptotic adaptations. |
| Pei16, Section 5.1 | 36 / 34 | The hash discussion refers back to the SIS collision family. It does not supply a bridge from LWE to the independent SIS assumption used here. Ring-SIS/SWIFFT material is not imported. |
| Wu24, Definition 20.4 | 82 / 79 | The batched LWE equation agrees after transposition. The full batch convention is also supported by Pei16 Definition 4.2.3; a fresh secret per row is not substituted. |
| Wu24, Definition 20.5 | 83 / 80 | Direct encryption adds the bit's half-modulus codepoint to a noisy inner product. `Encryption/Symmetric/Regev` batches this under one secret. The exact decoder and strict separation condition are disclosed refinements. |
| Wu24, Lecture 21, Notation 21.1 and security discussion | 85 / 82 | The ideal translation argument supports the concrete hybrid. The single-sample displayed definition/prose does not discharge the existing API's all-polynomial message schedule, uniform message bound or machine/adaptive-game obligations. |
| Wu24, Lecture 21, Regev public-key scheme and Definition 21.3 | 86 / 83 | Future PKE uses fresh binary subset coins and accumulated error. Its correctness and leftover-hash budgets must be explicit rather than copied as asymptotic shorthand. No PKE Lean statement is introduced by this review. |
| Wu24, following PKE reformulation | 87 / 84 | The augmented-matrix form agrees with the same PKE algebra. The subsequent FHE material is outside this campaign's headline scope. |

The three earlier audit reports are unchanged. In particular, the statement
auditor's inability to rehash the complete PDFs or retrieve all SIS passages
remains part of that historical report. This maintainer check advances the
targeted source comparison; it does not retroactively change that auditor's work.

## Rounding conditions to preserve

The current decoder chooses false on ties. It proves correctness from
`2 * B < floor(q/2)`. Keep this exact premise in consumers.

The notes' PKE discussion permits `m * B <= q/4`. At `q=4`, one selected row,
error `+1`, and message true, the received residue is `2+1=3`. Its distances
to zero and two are both one, so the current decoder returns false. A future
every-coin PKE theorem therefore uses `2 * (m * B) < floor(q/2)`.

Even the informal strict real condition `|e| < q/4` needs care at odd moduli:
at `q=5`, message true has codepoint two, and error minus one gives residue one,
equally distant from zero and two. The current strict floor condition excludes
this case. The exact integer calculations are in `rounding-boundaries.json`;
they are supporting calculations, not new Lean proofs or a defect in the frozen
correctness theorem.

The pre-Definition-20.5 Gaussian/hardness discussion is not used as a support
bound: an exact infinite discrete Gaussian is not bounded on every seed. The
formal noise law remains finite, and its `Bounded` predicate is a separate
every-seed hypothesis. Search/worst-case and SIS–LWE reductions on the same
source page remain excluded.

## Remaining source work

The full validated Markdown pairs, symbol/anchor validation outside these
selected pages, approved matching and applicable registry/dataset integration
remain open. The existing registry proposal is still unapplied. A separately
dispatched document job would require its own reviewer selection and dedicated
delivery path; none was launched here. No blueprint source/proof macros are added.

Notation: `q` is the modulus; `B` bounds one error's magnitude; `m` is the number
of public-key rows. All displayed inequalities are interpreted with the stated
natural floor or exact rational quarter.
