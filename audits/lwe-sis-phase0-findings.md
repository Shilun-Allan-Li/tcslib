# LWE/SIS phase 0, round 1: audit findings

**Recommendation: PASS the frozen statement gate.** No wrong or materially misleading statement, sketch, reader, or instance was found. This recommendation covers statements only. Source archival/ingestion remains open; the 14 representation proofs remain admitted. It does not approve a merge or certify construction security.

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 0 |
| Note | 3 |

Audit performed on 2026-11-07. No source was edited, proof admission filled, worker dispatched, GitHub output pushed, or branch merged.

## 1. Identity, integrity, and review limits

| Item | Audited identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange branch | `exchange/pass-shelat-ch5-8` |
| Exact exchange commit | `09d1456efacded71850c84497db5c8d1f65ab0a0` |
| Frozen Lean/root | `4364d0e0fe9accd649b6acb4751e8684aa93ad1e` |
| Bundled records | `06cdbc030168d9e6662b12960882d8ca6f5b1fa7` |
| Implementation baseline named by pack | `869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49` |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |
| Bundle | `lwe-sis-phase0-r1-bundle.md` |
| Bundle bytes / sections | 2,720,420 / 155 |
| Bundle SHA-256 | `9e39453ac97f8fbdc8014a302aa18c40b41f7e4692641ca5b141e0d79f25e68b` |

I read the root exchange README, campaign README, and gate README at the exact exchange commit, followed by the frozen pack in the bundle's first section. Current dispatch instructions supersede the bundled preparation-time transport descriptions.

The GitHub file-content endpoint returned empty content for the large bundle. Retrieval by its Git blob `0223d49870e14861953a95fb72fbb76abb5387f7` supplied the complete text; its independently computed byte length and SHA-256 match the requested freeze.

Integrity checks passed:

- All five entries in the exchange gate's `SHA256SUMS`.
- Exact agreement of revision-qualified `BUNDLE-FILES.txt` with `BUNDLE-FILES.json`, including order, paths, revisions, lengths, and hashes.
- All 155 extracted attachments: 63 assigned to the frozen source commit and 92 to the records commit; no repeated paths. The first attachment is `audits/lwe-sis-phase0-pack.md`.
- All 63 entries in `source-freeze.json` against the extracted bytes and their manifest revisions.
- All 82 checksums in the nested execution-evidence `SHA256SUMS`.

This was a static source audit with independent accounting and finite calculations. I reran the supplied style linter, but did not run Lean, install package caches, or independently reproduce native elaboration. Original source-commit ancestry and baseline diffs are supported by the supplied records; this review does not claim a separate checkout-based reproduction of that history. The exact exchange content and bundle integrity were independently verified.

## 2. Independent meanings of the assumptions

### Decisional LWE

At security parameter κ, take dimension n, sample count m, and modulus q from `F.parameters κ`, residue width k from `F.residueBits.eval κ`, and scalar noise χ from `F.noise κ`. The real experiment independently chooses

\[
A\leftarrow_U(\mathbb Z/q\mathbb Z)^{m\times n},\qquad
s\leftarrow_U(\mathbb Z/q\mathbb Z)^n,\qquad
(r_i)_{i<m}\leftarrow_U\chi.\mathrm{Coins}^{m},
\]

and sets

\[
e_i=\chi.\mathrm{sample}(r_i),\qquad
b_i=\sum_{j<n}A_{ij}s_j+e_i\pmod q.
\]

The same s serves every row. The comparison experiment chooses A and a uniform value vector u independently. Both challenges are encoded as the complete row-major matrix followed by the value vector, using k bits per residue.

Each `D : NUPPT` runs with the unary security parameter, its parameter-indexed advice, and independent uniform bit coins. Acceptance means its output is exactly `[true]`, through `distinguisherL`. Consequently,

\[
F.\mathrm{advantageAt}(D,\kappa)
=\left|\Pr[D\text{ accepts the encoded }(A,As+e)]
-\Pr[D\text{ accepts the encoded }(A,u)]\right|,
\]

\[
\mathrm{DLWEAssumption}(F)
\iff\forall D:\mathrm{NUPPT},\quad
\mathrm{Negligible}\bigl(\kappa\mapsto F.\mathrm{advantageAt}(D,\kappa)\bigr).
\]

The sample schedule is the single schedule stored in F. There is no quantification over all polynomial sample schedules and no claim of an efficient honest sampler, Gaussian noise, search-LWE, or a worst-case lattice reduction.

### SIS

At κ, let n be the matrix row count, m its column count, q its modulus, B its natural squared-norm bound, k the residue width, and t the output magnitude width. Choose a uniform matrix A and independent uniform machine coins. Run `D.runAt` on the canonical matrix encoding and parse its output with `decodeSolution`.

An output succeeds exactly when it has length m(t+1), decodes to an integer vector z, and satisfies

\[
z\ne0\text{ in }\mathbb Z^m,\qquad
\sum_{i<m}z_i^2\le B,\qquad
A(z\bmod q)=0.
\]

Each coordinate block has a sign bit followed by t magnitude bits; `true` means negative. Either sign of zero decodes to zero. Incorrect output lengths fail. Parsing alone does not establish validity.

\[
\mathrm{SISAssumption}(F)
\iff\forall D:\mathrm{NUPPT},\quad
\mathrm{Negligible}\bigl(\kappa\mapsto F.\mathrm{successAt}(D,\kappa)\bigr).
\]

Here `Negligible μ` means

\[
\forall c\in\mathbb N\;\exists\kappa_0\ge1\;
\forall\kappa\ge\kappa_0,\quad |\mu(\kappa)|<1/\kappa^c.
\]

The extra requirement κ₀≥1 can be obtained by increasing the threshold in the existing definition. SIS hardness is an explicit hypothesis independent of LWE; neither assumption is asserted as an axiom or theorem.

## 3. Prioritized questions

| Question | Assessment and evidence |
|---|---|
| **1. Common-secret distribution** | **Pass.** `LWE/Basic.lean:73` takes a product consisting of A, one secret, and a function assigning a noise seed to every row. Uniformity on this finite product gives independent components and independent row seeds. `sample_snd` preserves the single secret. `decisionAdvantage` compares with the identity on the full matrix/value product, giving independent uniform comparison components. Rows are independent conditional on the secret; unconditional independence of noisy rows is not required or inferred. |
| **2. Noise specialization** | **Pass.** `Noise` stores both `Fintype` and `Nonempty`, and explicitly registers their projections as instances. For any integer error value, its probability is its number of preimage seeds divided by the seed cardinality. Multiplicities therefore survive. `Bounded` quantifies over all seeds. Finite rational laws, rather than exact infinite Gaussian laws or efficient sampling, are explicitly the scope. |
| **3. Parameters and quantifiers** | **Pass.** Both parameter bundles require q≥2 and derive `NeZero q` from that field. Empty index sets have the expected unique empty functions/matrices. The security parameter is separate from all numeric parameters. Fixed sample count, arbitrary numeric schedules, and deferred computability contracts are disclosed in `LWE/Assumption.lean:37–50,58–81,128–139`. No sample-extension equivalence is smuggled in. |
| **4. Polynomial inputs** | **Pass.** Width coverage is q≤2ᵏ. The actual LWE length is m(n+1)k; the SIS matrix length is nmk. Their stored polynomial upper bounds majorize these expressions by monotonicity of natural addition and multiplication. A residue representative is strictly below q, hence below 2ᵏ. The admitted injectivity statements correctly require coverage. Empty dimensions and the general modular encoder's q=1,k=0 case do not invalidate them. Below coverage, truncation is deliberate and documented. |
| **5. SIS fidelity** | **Pass.** `SIS/Basic.lean:59–71` checks integer nonzeroness, an integer sum of coordinate squares, and the modular matrix equation. B is the squared bound, not a norm radius. For m>0 and B≥q², z=(q,0,…,0) is valid for every A; the source expressly leaves exclusion of that trivial regime to later profiles. Conversely, m=0 or B=0 permits no nonzero solution. These are allowed relations, not claimed hardness profiles. |
| **6. SIS machine output** | **Pass.** The offsets in `decodeSolution` match the encoder's sign-then-magnitude blocks. The exact-length guard ensures no coordinate accesses a missing bit. Both round-trip statements have sufficient hypotheses, including at zero width or zero columns. The norm-to-coordinate implication is valid over integers; see §4. Negative zero affects canonicality of strings, not completeness of integer outputs. |
| **7. Machine adaptation** | **Pass within stated scope.** `distinguisherL` tests exact output `[true]`; SIS uses the full output of `runAt`. The existing `NUPPT` definition supplies polynomial advice/coin budgets and a polynomial worst-case machine clock. Challenge lengths are polynomial in κ; the unary prefix, advice, coins, and pair encodings preserve that bound. No oversized-input loophole was found. Efficiency of honest samplers and representation adapters remains a later obligation, explicitly disclaimed here; no equivalence theorem to every typed efficient solver is claimed. |
| **8. Readers and sketches** | **Pass.** All 19 new definitions have complete owner-side equation, coordinate, projection, or iff readers. The 20 definitional readers and the wrong-length theorem were inspected, as were both modulus instances. All 14 admissions have compatible mathematical sketches. They need finite-list slicing, numeral round trips, arithmetic inequalities, and existing encoders; no sketch requires a new machine host. No new private infrastructure or copied proved material appears in these modules. |
| **9. Trusted boundary** | **Pass as a static evidence check.** The declaration census, source line locations, admission list, probe output, and generated-constant inventory agree. Both assumptions and both assumption readers have recorded axiom sets `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Their source bodies do not invoke the admitted representation theorems. The 17 inherited admission warnings remain inherited debt; see §5 and note N02. |

## 4. All representation statements and skeleton-time proofs

The following checks concern statement correctness and feasibility of the supplied sketches. They do not fill or certify the Lean proofs.

| Owner and statements | Count | Independent assessment |
|---|---:|---|
| `Encoding.Modular.encodeVector_length`, `encodeMatrix_length` | 2 | Each numeral has exactly the prescribed width. Summing coordinate lengths and then row lengths gives the stated products, including zero widths and empty indices. |
| `Encoding.Modular.encodeVector_injective`, `encodeMatrix_injective` | 2 | Fixed-size slices recover coordinate numerals; `Candidates.listToNat_natToList` recovers each representative under q≤2ᵏ. At k=0, coverage and `NeZero q` force q=1, whose residue type is a singleton. Empty matrix products likewise have only one matrix. |
| `LWE.encodeChallenge_length`, `encodeChallenge_injective` | 2 | The matrix segment has a known length, so concatenation preserves both lengths and injectivity of its two components. No delimiter is needed at fixed parameters. |
| `LWE.Family.encodeChallenge_length_le` | 1 | Apply the exact length and the stored dimension/sample bounds; no computability hypothesis is needed for this numeric inequality. |
| `SIS.encodeChallenge_length`, `encodeChallenge_injective` | 2 | Direct specializations of the common matrix statements with the stated width condition. |
| `SIS.encodeSolution_length` | 1 | Exactly m blocks, each consisting of one sign bit and t numeral bits; no magnitude hypothesis is needed merely for length. |
| `SIS.decodeSolution_encodeSolution` | 1 | Exact length opens the successful branch. The i-th sign is at i(t+1), and the magnitude slice starts at i(t+1)+1 with length t. The strict coordinate bound permits the numeral round trip. Sign and absolute value then recover the integer. |
| `SIS.decodeSolution_encodeSolution_of_isSolution` | 1 | The squared-bound coverage hypothesis is conservative but sufficient; the integer inequality below establishes the previous theorem's coordinate hypothesis. |
| `SIS.Family.encodeChallenge_length_le`, `encodeSolution_length_le` | 2 | Substitute the exact lengths and apply the stored row/column bounds. Output length accounting also holds for candidates whose magnitudes truncate; lossless recovery is asserted only under the separate fit conditions. |
| **Total admitted statements** | **14** | **No counterexample or missing hypothesis found.** |

For the potentially delicate squared-norm step, fix a coordinate i and put a=|zᵢ|, a natural number. If a=0 then a≤a²; otherwise a≥1 and multiplication by a gives a≤a². Every coordinate square is nonnegative, hence

\[
|z_i|\le z_i^2\le\sum_{j<m}z_j^2\le B<2^t.
\]

Thus `(z i).natAbs < 2 ^ magnitudeBits`, exactly the first round-trip theorem's hypothesis. This argument also identifies why the stored bound is sufficient without taking square roots.

The other 21 theorems comprise 20 defining readers (`rfl`/`Iff.rfl`) and `decodeSolution_of_length_ne`, which rewrites the owner's decoder equation and the failed guard. Both anonymous instances use q≥2 to establish q≠0. None requires an unstated correctness assumption.

Independent Python calculations checked 2,795 modular-vector cases, 9,280 signed round trips, and all 5,054 output words across the selected small exact-length formats. They included q=1, zero widths/coordinates, truncation below coverage, malformed lengths, and both signs of zero. A separate conditional common-secret check used q=3, two public rows equal to 1, and seed images `(0,0,1)`: equality of the two noisy values has probability 5/9, versus 1/3 in the ideal experiment. The conditional gap is 2/9, confirming that multiplicities and the common secret must both be retained. These are finite mathematical checks, not Lean evaluation or security proofs.

## 5. Census, execution attestations, and exports

Every declaration in `source-declarations.json` was reviewed against its source location. Module paths below are relative to `TCSlib/Cryptography/`.

| Module | Source declarations | Admitted theorems |
|---|---:|---:|
| `Encoding/Modular` | 8 | 4 |
| `LWE/Noise` | 3 | 0 |
| `LWE/Basic` | 7, including one instance | 0 |
| `LWE/Experiments` | 2 | 0 |
| `LWE/Encoding` | 4 | 2 |
| `LWE/Assumption` | 8 | 1 |
| `SIS/Basic` | 4, including one instance | 0 |
| `SIS/Experiments` | 2 | 0 |
| `SIS/Encoding` | 12 | 5 |
| `SIS/Assumption` | 11 | 2 |
| **Total** | **61** | **14** |

The source census is **19 definitions + 5 structures + 35 theorems + 2 instances**. The raw environment walk and `elaborated-constants.json` agree on **164 distinct public constants: 61 source declarations, 100 structure-generated constants, and 3 compiler auxiliaries**. No listed new constant has axiom kind or a private name. The probe's axiom sets are confined to `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; exactly the 14 inventoried admissions contain `sorryAx`.

I independently reconstructed the three facades' transitive TCSlib import closure: exactly 55 modules, matching both the sweep list and dependency order. Supplied logs and exit records agree on 14 new and 17 inherited admission warnings, zero reported errors, and four successful post-rename rechecks. The inherited warnings are in `TimeConstructible` (2), `Build/Loop` (5), `Build/Primitives` (3), `Build/Wrappers` (2), `Composition` (3), `Encoding` (1), and `Simulation` (1).

The check script removes the target olean before invoking Lean and fails on nonzero exit, errors, or a missing fresh olean. That supports the stated verification procedure; supplied logs are not a substitute for an independently rerun native check.

All eight selected package-source revisions agree with `lake-manifest.json`. The cache selection and archive-provenance lists agree on 2,334 archive/module pairs, with SHA-256 values recorded for every archive. The actual archives are not bundled and were not independently rehashed in this audit; isolation and extraction remain maintainer execution attestations.

I reran the three style checks and reproduced **0 FAIL, 2 WARN across 10 files**. Both warnings are name-matching false positives: `dlweAssumption_iff` and `sisAssumption_iff` exist beside their predicates and expose the exact propositions. No reader is missing, and no linter repair or rename is required for this gate.

All three new facades import their complete children, and `TCSlib.lean` imports all three. The supplied root-export diff contains exactly those additions. Neither the supplied evidence nor this audit establishes whole-library root elaboration.

## 6. Primary-source fidelity and its limits

I independently accessed the author-hosted [Peikert survey](https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf), whose cover dates it 17 February 2016. Definition 4.1.1 (printed p.18) agrees with integer nonzeroness and the modular kernel relation; the code explicitly replaces the norm radius by a natural squared bound. Definitions 4.2.1/4.2.3 (p.22) agree with the scalar error law and common-secret decision problem. The matrix convention on p.23 becomes the implementation's convention by transposition. Finite-seed noise and empty-dimensional boundaries are disclosed specializations/extensions.

I also checked [Pass–shelat, third edition, January 2010](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf), §2.1 and Definition 26.8: the advice formulation and worst-case coin convention support the existing machine interface's attribution. Parameter-indexed activation is the repository's documented adaptation. These references do not supply the new binary LWE/SIS encodings or their machine implementations.

**Definition-level correspondence was checked live. PDF byte identity, repository archival, reference ingestion, and proofmatch were not verified or completed.** The bundle contains no frozen primary PDFs or primary-PDF checksums. Successful browsing in this audit does not close the historical archival/ingestion limitation. Later construction sources, lattice reductions, and the full source equivalence of inherited machine infrastructure were outside this phase-0 review.

## 7. Findings and disposition

| ID | Severity | Location | Finding/evidence | Required repair |
|---|---|---|---|---|
| N01 | Note | Pack, “Primary sources and access limitation”; `policy.md` §2; plan, “Sources and source-access status” | Live primary-definition checks succeeded, but byte-frozen PDF provenance and the required reference archival/ingestion workflow remain open. Internal source-review claims do not discharge them. | Preserve this limitation in gate resolutions. Complete archival/ingestion and applicable source-matching work before claiming source-fidelity closure or source-policy completion. No phase-0 statement change is required. |
| N02 | Note | `evidence/summary.json`, scoped sweep, axiom probe, root-export evidence | The evidence is internally consistent but scoped: 14 new admissions and 17 inherited warning sites remain; the whole root was not checked. This auditor did not independently run Lean or validate physical cache isolation. | Retain the exact scope and admission inventory. Fill the 14 proofs only through subsequent authorized work and perform the relevant landing/integration checks. Do not relabel this report as a proof-completion or whole-library build certificate. |
| N03 | Note | `LWE/Assumption.lean:37–50,128–139`; `SIS/Assumption.lean:38–51,63–84`; plan D1–D7 | Fixed-sample hardness, finite rational noise, mathematical samplers, and unrestricted SIS numeric relations are accurately disclosed. Honest efficiency, sampling transfer, representation-machine bridges, and useful parameter profiles are future consumer obligations. | Carry those obligations into the corresponding later statement gates. In particular, check sufficient LWE sample schedules and the actual noise law; exclude trivial SIS regimes and establish needed solution/compression conditions. No current semantic repair is required. |

**Gate disposition:** the frozen phase-0 statements, sketches, readers, and instances meet the zero-blocker/zero-major threshold. Recommend recording the statement gate as passed, with N01–N03 retained verbatim. Source-fidelity archival closure, proof fills, construction gates, and user-controlled merge approval remain separate outstanding work.

## Notation glossary

- κ: security parameter; κ₀: an eventual threshold; c: natural inverse-polynomial exponent; μ: a real-valued function tested for negligibility.
- F: the relevant LWE or SIS family; D: a repository `NUPPT` adversary.
- n: LWE secret dimension or SIS matrix row count; m: LWE sample count or SIS column count; q: modulus; k: residue bit width.
- χ: scalar finite-seed noise; rᵢ: its i-th coordinate seed; e: resulting integer error vector; s: the shared secret; u: the independent uniform comparison vector.
- A: public modular matrix; b: LWE value vector; z: SIS integer candidate; B: squared-norm bound; t: magnitude bit width; a: the temporary natural absolute value of one coordinate.
- ←ᵤ: uniform sampling; ℤ/qℤ: integers modulo q; `Pr`: probability under the independent uniform seeds specified above.
