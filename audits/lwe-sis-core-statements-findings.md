# LWE/SIS construction-core statements — round 1 findings

**Recommendation: PASS for the frozen statement gate.**

**Totals: 0 blockers, 0 majors, 0 minors, 3 continuing notes.** I found no invalid definition, false statement, missing mathematical hypothesis, or misleading completion claim in this slice. All 62 source declarations, the 31 admitted obligations and their sketches, the 23 generated readers, and the five compiler auxiliaries were reviewed. The 31 obligations remain admitted; this report does not certify their Lean proofs or later primitive-security endpoints.

## Frozen inputs and verification

| Item | Verified identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange branch | `exchange/pass-shelat-ch5-8` |
| Exact exchange commit | `90d652e19508262b3bd81234260d0585aaf8e0a0` |
| Frozen Lean/root | `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf` |
| Bundled records | `4f403f777cda259ced52d74243d7ff7f9d547f99` |
| Audited dependency | `0769cba3e44c56700349f954190fc99d9e622270`, PR #236 |
| Central integration / PR target | `cryptography/lwe-sis-constructions` |
| Bundle | `lwe-sis-core-statements-r1-bundle.md` |
| SHA-256 | `2e9e72b2211e33afbcbdf727f875d4cf27bcb0efb45b7000883391048dd1f9aa` |
| Bundle bytes / sections | 3,611,753 / 400 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the three requested READMEs in order and followed the first-section pack. All five entries in the gate's `SHA256SUMS` pass. Both `BUNDLE-FILES` indexes agree in all 400 ordered revision-qualified rows; every recovered section has its indexed size and SHA-256. The revision populations are 76 source files and 324 records files.

I also resolved every indexed path through GitHub trees at its stated revision and recomputed its Git blob identity from the recovered bytes. **All 400 match their published revision/path identities.** This independently checks the bundle against the repository, beyond checking its internal manifests. All 106 entries in the current construction-core evidence checksum file also pass.

The GitHub comparison against the audited dependency reports exactly two commits and 16 changed paths: eight new mathematical modules, five new facades, and three modified export files. I independently fetched and compared the three original export files. Their changes are precisely the disclosed imports and contents entries. Sixty of the previous 63 frozen files remain byte-identical. The two historical findings files match their recorded intake SHA-256 values; they were not altered.

No repository source or records were edited, no admissions were filled, and no workers, dispatches, pushes or merges were performed. Reviewer checks used separate scratch files. This was a static audit, with supplementary finite mathematical models; I did not run Lean.

## Declaration coverage

Paths below are relative to `TCSlib/Cryptography/`.

| Module | Definitions | Theorems | Admitted | Assessment |
|---|---:|---:|---:|---|
| `LWE/SampleSchedules` | 3 | 2 | 0 | Replacement preserves the other data and the fixed-sample assumption's meaning; sample accounting is exact. |
| `Encoding/ModularDecode` | 2 | 10 | 5 | Canonical guards, row-major indexing, rejection equations and both round-trip directions have the required hypotheses. |
| `LWE/BitEncoding` | 3 | 9 | 6 | Circular distance, separation, tie convention and bounded-error decoding agree. |
| `Encryption/Symmetric/Regev/Basic` | 3 | 3 | 2 | Direct common-secret encryption and every-seed correctness are stated faithfully. |
| `Encryption/Symmetric/Regev/Experiments` | 1 | 3 | 3 | Actual-law sampling, ideal translation and the two-advantage bound are correct. |
| `Hashing/SIS/Basic` | 2 | 8 | 6 | Integer collision differences, norm bound, kernel equation, compression and existence are correct. |
| `Hashing/SIS/Experiments` | 1 | 2 | 1 | The reduction uses the same matrix and independent finder coins; event inclusion is valid. |
| `Hashing/SIS/Profiles` | 2 | 8 | 8 | Constructor bounds, compression, exclusion of modulus multiples and exact budgets are correct. |
| **Total** | **17** | **45** | **31** | **62 declarations; no statement repair required.** |

### Sample schedules and canonical parsing

`Parameters.withSamples` retains dimension, modulus and its lower-bound proof. `Family.withSamples` retains the noise law, dimension bound, residue width and associated proof fields, replacing only the sample count and its syntactic bound. It makes no amplification assertion and changes neither `DLWEAssumption` nor its quantifier order.

I additionally read `PrivateKeyScheme.MultiMessageSecure` at the frozen source: it quantifies over `Fin (Q.eval κ + 1) → Fin κ → Bool`. Thus the new expression evaluates to exactly

\[
\kappa\bigl(Q(\kappa)+1\bigr).
\]

The proposed outer hypothesis over polynomial sample schedules and the later worst-message advice obligation are explicit. Neither follows from a single stored schedule, and neither is claimed proved here.

`decodeVector` requires exact length and checks each fixed-width numeral strictly below the modulus before casting. A successful parse therefore preserves the numeral, rather than silently reducing an out-of-range word. Decode-after-encode needs the stated coverage condition `q ≤ 2^width`. Encode-after-successful-decode needs no such global condition: each accepted chunk already fits its own width and has value below `q`.

Both vector round trips and all three matrix obligations have viable sketches. The pinned `finProdFinEquiv` sends `(i,j)` to `j + columns*i`, equal to the stated row-major index `i*columns+j`. Consequently the entry starts at `(i*columns+j)*width`. The parser does not divide by width. Modulus one, zero width, empty vectors, empty rows or columns, wrong lengths and out-of-range chunks introduce no missing premise. In particular, coverage at zero width forces modulus one; successful parsing at zero width still re-encodes exactly.

### Distance, decoding and encryption correctness

The pinned Mathlib `ValMinAbs` source supplies the cited negation, addition and half-modulus lemmas. Its convention at an even half-modulus does not affect the natural absolute value. Thus the symmetry, triangle, translation, codepoint-separation and integer-error statements are mathematically sound and have the advertised public-API routes.

For either intended bit, write its codepoint as `c` and the other as `c'`. The received residue obeys

\[
d(c+e,c)\le |e|\le B,
\]
\[
\lfloor q/2\rfloor
=d(c,c')
\le d(c,c+e)+d(c+e,c').
\]

Hence `2*B < floor(q/2)` implies

\[
d(c+e,c')\ge\lfloor q/2\rfloor-B>B\ge d(c+e,c).
\]

The intended codepoint is uniquely nearer. This proves the proposed decoding statement's mathematical content for either sign of error; the false-on-ties convention is harmless under its strict hypothesis. The condition correctly uses natural division. For example, at modulus five an error of minus one on the true codepoint produces a tie; the current hypothesis excludes that case. No informal `|e|<q/4` substitution was made.

`decrypt_encrypt` subtracts exactly the matrix-secret product added by `noisyValues`, leaving the codepoint plus its row error. Coordinatewise decoding and function extensionality give the stated result, including an empty message. `decrypt_encrypt_noise` assumes a bound on every noise seed, so it genuinely states every-seed correctness. Seed multiplicities are preserved and no Gaussian-tail argument is substituted for that bound.

### Concrete encryption security

`encryptDist` uses the exact seed product of `LWE.sample`: one public uniform matrix, one common uniform full secret, and independent scalar-noise seeds for the rows. The proposed equality with `shift` of that sample uses the same coins on both sides.

For each fixed plaintext, `shift` is a bijection on the matrix/value space: retain the matrix and subtract the same codepoint vector for its inverse. It therefore preserves the independent uniform ideal experiment and the independently sampled distinguisher coins.

Let `p₀,p₁` be the two real acceptance probabilities and `pᵤ` the common ideal acceptance probability. The claimed bound is exactly

\[
|p_0-p_1|\le |p_0-p_u|+|p_1-p_u|.
\]

Its two terms are the existing DLWE advantages with the respective plaintext translations. There is no factor-of-two convention error, secret resampling between rows, or assumption on the actual noise distribution in this argument. The statement concerns arbitrary finite-coin functions at fixed parameters. Efficient reductions, a negligible bound uniform over messages and adaptive CPA remain separate obligations.

### SIS collision relation and probability

The difference is taken over integers before reduction. For distinct Boolean vectors,

\[
z_i=\operatorname{toNat}(x_i)-\operatorname{toNat}(y_i)
\in\{-1,0,1\},\qquad z\ne0,
\]
\[
\sum_{i<m}z_i^2\le m\le\texttt{sqNormBound},
\qquad A(z\bmod q)=Ax-Ay=0.
\]

These are precisely the three existing `IsSolution` conditions. The bound on columns is present in both the algebraic reduction and the probability theorem. Integer nonzeroness is retained even at modulus two. No primality or LWE premise is needed.

The collision and solver experiments sample the same uniform matrix/finder-coin pair. Each successful collision makes the optional difference a successful SIS output, so `uprob_mono` gives the stated inequality. Typed finder outputs do not establish a raw-output machine bridge; the later owner's padding/splitting behavior is explicitly recorded.

The cardinalities are exactly `2^columns` and `q^dimension`. Strict compression rules out injectivity and yields a distinct colliding pair for every matrix. The norm condition then yields the asserted solution. At zero dimension this reasoning still applies; at zero columns the strict compression premise is impossible. Existence is not confused with an efficient finder or hardness.

### Dyadic profile and constructors

With `t=κ+1`, both constructor obligations are valid: `2 ≤ 2^t` and `2t² < 2^(2t²+1)`. The family fields give the stated exact polynomial dimensions and widths. All four constructor proof fields use public parameter readers and polynomial-evaluation equations.

Compression is `2^(t²) < 2^(2t²)` because `t≥1`. The squared-norm inequality has a valid induction:

\[
2<4,\qquad
2(t+1)^2\le8t^2=4(2t^2)<4\cdot4^t=4^{t+1}.
\]

Thus `2t² < q²`. A nonzero integer vector whose coordinates are all divisible by `q` has a coordinate of absolute value at least `q`; its total squared norm is at least `q²`, contradicting the bound. The zero vector fails nonzeroness. This establishes exactly the stated exclusion, without claiming to exclude every easy solution or attack.

The bit budgets follow directly from the existing family equations:

\[
t(2t^2)t=2t^4,\qquad
(2t^2)\bigl((2t^2+1)+1\bigr)=4t^4+4t^2.
\]

The profile asserts no hardness theorem. Requiring its own `SISAssumption` in a later security theorem is appropriately explicit.

## Readers, trust and execution evidence

The 14 closed source theorems are defining equations, guard-rejection equations and the sample-expression readout. I checked their small proofs, including the explicit public equations used in rewrites. No foreign-definition unfolding, new global simp attribute, private host or duplicated proved infrastructure was found.

The generated readers cover the selected data fields of the two schedule replacements, the three encryption product maps, and the two profile constructors. Their `simps` invocations explicitly set `isSimp := false`. Their names and axiom inventories agree with the raw final environment walk.

An independent comment-aware source census reproduces 17 definitions, 45 theorems and 31 direct admissions. Parsing the raw final probe reproduces all 62 source axiom reports and all 256 owned-module constants. Its accounting is

\[
90=62+23+5,\qquad 256=166+90.
\]

Exactly 46 new constants depend on `sorryAx`: 31 admitted statements, two profile constructors, nine profile readers and four constructor auxiliaries. The remaining schedule-constructor auxiliary has only standard axiom dependencies. All 166 earlier constants retain their recorded kinds, visibility and axiom sets, with no `sorryAx`. No owned constant is private or axiom-kind, and the reported axiom sets contain only the three standard axioms and the disclosed admissions. These are reconciled supplied probe results, not a reviewer-native environment interrogation.

I reconstructed the five facade roots' TCSlib import closure and its dependency order: exactly 68 modules. Every recorded sweep source hash matches the frozen bytes. Every final record reports exit zero and a fresh olean; its raw log has no error diagnostic. Raw warning counts reproduce 31 new and 17 inherited admissions, and durations sum to 176.591 seconds. The final probe also agrees with its supplied successful execution record. Retained development failures are historical; they were not mistaken for final failures or passing runs.

I reran the five scoped style checks and reproduced **0 FAIL, 2 WARN over 18 mathematical files**. The two warnings are the unchanged assumption-acronym heuristic cases; their complete readers remain present. All eight recorded package revisions and the Lean pin agree with the manifest. Physical package/cache isolation and actual fresh native execution remain maintainer attestations. The full `TCSlib.lean` root was not independently or reportedly built for this gate.

Supplementary independent Python models found no counterexample in 726 covered vector round trips, 14,496 parser words, 10,032 matrix cases, 246,015 distance triples, 2,010 integer-error bounds, 1,376 bounded bit decodings, 29 ties, 12,861 SIS collision pairs, 121 compressing matrices, 504 exact finite-coin hybrid checks and 256 dyadic parameter values. The hybrid models retained repeated noise-seed images. These finite checks supplement the general mathematical review; they do not fill any Lean admission.

## Source fidelity and continuing findings

I compared retrievable primary text for [Wu24, Definition 20.5 and Lecture 21](https://www.cs.utexas.edu/~dwu4/courses/sp24/static/notes.pdf) and [Pei16, Definition 4.2.3](https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf). The full uniform secret, noisy-inner-product ciphertext and common-secret DLWE convention agree. Row batching, finite-seed noise and nearest-codepoint decoding are disclosed adaptations. The SIS claims were checked directly against the integer relation and finite cardinalities; their squared-bound and binary-domain specializations are explicit. The dyadic parameters are correctly identified as local choices.

I did not independently obtain and rehash the complete primary PDFs in this audit: direct downloads failed, and retrieval of the Pei16 SIS sections was incomplete. Accordingly, this report does not assert a complete independent comparison with the frozen PDF bytes. The bundled provenance reports exact archived versions and hashes, but archival attestation, reference ingestion and approved matching remain distinguishable from the source text actually inspected. The narrow statement recommendation rests on the checked source, self-contained mathematical arguments and disclosed adaptations; N01 remains open.

| ID | Severity | Location | Finding/evidence | Required repair |
|---|---|---|---|---|
| N01 | Note, carried forward | `policy.md` §2; pack's prior-gate limits; `evidence/primary-source-provenance.json` | Primary acquisition has progressed and exact PDF hashes are recorded. Ingestion and approved matching remain open. This auditor compared the retrievable primary passages above but did not independently rehash complete PDFs or complete the Pei16 SIS-section comparison. | Preserve the earlier reports verbatim. Complete the applicable ingestion, source matching and frozen-source verification before claiming source-policy or complete frozen-source fidelity closure. No current statement correction identified. |
| N02 | Note, carried forward | Current `evidence/fresh-sweep/`, `axiom-probe-final/`, root exports | The source hashes, 68-module closure, raw logs, admission counts and constant census reconcile. This is a static audit of supplied execution evidence; physical isolation and native freshness remain attestations, and whole-root elaboration is unclaimed. | Retain these limits and perform the relevant landing/integration checks. Do not describe this review as an independent Lean rerun or a whole-library build certificate. |
| N03 | Note, carried forward | `LWE/SampleSchedules`; Regev and SIS construction modules; next-phase contracts | The slice correctly states mathematical prerequisites while leaving 31 admissions and the honest samplers, efficient representation adapters, machine reductions, required sample quantifiers and final primitive bridges open. The dyadic profile proves no hardness, and typed collisions do not implement the future raw-output game. | Carry these obligations into their proof-fill and consumer gates, including actual-law agreement, common-secret sample schedules, a uniform negligible message bound, exact output semantics and the profile's independent SIS hypothesis. No present semantic repair required. |

**Gate recommendation: PASS — 0 blockers, 0 majors, 0 minors, 3 continuing notes.** This approves the reviewed statements for the next scoped proof phase. It does not close source-policy work, prove the admitted statements, certify later constructions or authorize a merge. Integration remains through the user's PR process targeting `cryptography/lwe-sis-constructions`.

Notation glossary: `κ` is the security parameter; `Q(κ)` abbreviates `Q.eval κ`; `t=κ+1` is the dyadic profile parameter; `q` is the modulus; `m` is the SIS column count; `width` is the residue block width; `A` is a public matrix; `e` is an integer error; `B` bounds its absolute value; `c,c'` are the intended and other bit codepoints; `d` is the reviewed circular distance; `x,y` are binary hash inputs; `z` is their integer difference; `i,j` are entry indices; `p₀,p₁,pᵤ` are the two real and common ideal acceptance probabilities. Absolute-value bars denote integer or real absolute value, as appropriate.
