# Gate 41 — GSW statement audit

**Disposition: PR #332 CLEAR; PR #333 HOLD.** The hold is the unfulfilled Q14 source-ingestion requirement. I found no false target, missing mathematical hypothesis, or off-by-one in the 35 GSW statements. The two new #332 proofs are sound on inspection and have the standard-axiom dependencies recorded below.

| Scope | Blocker | Major | Minor | Note |
|---|---:|---:|---:|---:|
| PR #332 | 0 | 0 | 0 | 0 |
| PR #333, including its campaign records | 0 | 1 | 3 | 2 |
| Total | **0** | **1** | **3** | **2** |

This is a statement audit of #333, not a proof-completion claim: its 35 targets still contain `sorry`. I reviewed #332's two completed proofs as proofs. I authenticated and inspected the supplied build, axiom, and seal evidence; I did **not** run a new Lean elaboration. No repository files, PRs, or merge state were changed. The specified facade conflict and merged-tree rebuilds are excluded from the audit, as dispatched.

## Audited material and integrity

| Item | Pinned revision |
|---|---|
| Exchange | `c72de14a98d2ad107600323b171985017465e33a` |
| Campaign records | `86d19094aafecc1e19d208c6629b179cfdd14009` |
| [PR #332](https://github.com/Shilun-Allan-Li/tcslib/pull/332) | `94eae71b779c4ca0f76c138d699f4d737dbd6cee` |
| [PR #333](https://github.com/Shilun-Allan-Li/tcslib/pull/333) | `48d796a8a68cd50897047f01825a8132dd19e8d8` |
| Common base | `523d80d2d4dd8e4ed6799358831e5b3806c6187b` |

I read `README.md`, `pack.md`, every section of `bundle.md`, the rulings and statement-text decisions, the 118-file source closure as needed for dependencies, and the four supplied source excerpts. Independent checks passed:

- Outer `SHA256SUMS`: **15/15**; verification archive: **73/73** hashes, with exactly the listed files plus its manifest.
- Inner statement archive: **545/545** hashes; **546 files including the manifest**. All 32 furnished evidence extracts match the inner archive byte for byte. Directory entries are not counted as files.
- All **118 source files** match Git blob IDs in #333's pinned tree; all **21 bundle sections** match the Git objects named by `BUNDLE-FILES.txt`.
- The 7 verification-record copies match their disclosed pre-pin revision `aacfa40b…`; only the plan and `EVIDENCE.md` have append-only additions at the pinned records revision. The bundle supplies the pinned versions. The 8 context files match their disclosed context tip. The three filed statement-evidence objects match the pinned records.
- `48d796a8~2 = 94eae71b`; the DAGCircuit blob is identical at both heads. The supplied 84,963-byte diff matches the pinned base-to-head diff with `--abbrev=9`; SHA-256 `f577be74b52ea7607d9bdfbb87033402cc5dce6460ccf651418dee52fdf3de53`.
- Source inventory: 13 changed files, 35 target admissions, maximum line width 100, maximum file length 721.

The source comparison uses the excerpts requested in the dispatch. The cited PDF hashes are provenance claims in the pack; the PDFs are absent, so I did not independently rehash or inspect those PDFs. The committed Pei16 raw text and the supplied scoped excerpts suffice for the mathematical comparison here.

## Findings, marked by PR

Paths abbreviated as `GSW/…` below are under `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`.

| ID | Severity | PR · file · declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| **G41-01** | **major** | **#333** · source ingestion; `briefs/lattice-gsw/rulings.md`, Q14; `questions.md:147` | Q14-A expressly requires GSW13 ingestion into `blueprint/src/references/` **in the phase-5 statement PR**. The pinned diff adds no reference-ingestion files. The statement evidence and pack explicitly acknowledge that ingestion is unfinished. Excerpts make this audit possible but do not satisfy the accepted ingestion requirement or policy §2. No later waiver appears in the supplied rulings. | Complete the approved GSW13 ingestion/reference registration and provide its evidence, or obtain an explicit superseding disposition from the user. This is an unmet gate obligation, not a mathematical defect. |
| **G41-02** | **minor** | **#333** · [Eval.lean:57–63][eval] · `homAnd` | Its declaration docstring says “left-to-right product chain.” The recursion is **right-associative**, with the head on the left: `mul C₁ (mul C₂ C₃)`. Associativity/order matters for the additive noise analysis; the module docstring and recursion otherwise describe the intended operation correctly. | Say “right-associative product chain, with each head multiplied on the left.” |
| **G41-03** | **minor** | **#333** · [Eval.lean:164–184][eval] · `eval_encrypts` | The docstring says the theorem establishes the depth-indexed invariant at **every vertex**. Its exported conclusion establishes it only at the circuit output. The stronger assertion is a valid intermediate invariant in the sketch, but is not the statement being published. | State output correctness in the opening prose; describe the every-vertex invariant as an intermediate step in the proof sketch. Alternatively, publish the stronger auxiliary result deliberately. |
| **G41-04** | **minor** | **#333 / records** · `briefs/lattice-gsw/plan-section.md`, especially §G8 and §G10 | The accepted Q9 location is implemented correctly in Lean, but the proposed organization row still says `Encryption/Homomorphic/GSW/`; related facade/import prose retains the old location. The proposed organization and phase rows have not been incorporated into the main plan. The main decision log does record the correct ruling, so this is documentation drift. | Replace the obsolete paths with `AdvancedEncryption/Homomorphic/GSW/` and synchronize the pending plan tables with the actual phase-5 state. |
| **G41-N1** | **note** | **#333 / records** · Pei16 source coverage | The scoped `peikert2016-lattice-survey.md` lacks the newly cited §5.4.3/§6.1.3 passages; the committed raw extraction and gate excerpts contain them. Thus the citations can be checked here, and this is not a second source-fidelity hold. | Extend the scoped reference/anchors when integrating source matching for these declarations. |
| **G41-N2** | **note** | **#333** · PR description, Gadget summary | “The digit bounds” is an imprecise summary of the five target statements. They are digit recovery, two reconstruction identities, zero-block decomposition, and the single-block error-sum bound. The digit range itself is enforced by `digit`'s type and `Parameters.modulus_le`. | Use those five descriptions in the PR body. No signature change is needed. |

## PR #332: completed proofs and shared API

The diff adds the approved four readers, `DAGGate.getD_lt_depth`, `runWith_rel`, and their module documentation. It changes no existing definition or theorem statement. The readers are the expected `rfl` equations.

For `DAGGate.getD_lt_depth`, membership in the argument list gives

\[
\mathrm{ds.getD}(a,0)
\le \operatorname{foldr}\max\,0\,[\mathrm{ds.getD}(v,0):v\in g.\mathrm{args}]
<1+\operatorname{foldr}\max\,0\,[\mathrm{ds.getD}(v,0):v\in g.\mathrm{args}]
=g.\mathrm{depth}(\mathrm{ds}).
\]

The first inequality is exactly the list induction in the submitted proof: membership in the head uses `le_max_left`; membership in the tail uses the induction hypothesis and `le_max_right`. The strict inequality is natural-number successor arithmetic. Out-of-range reads are also covered because the formula uses `getD` throughout.

For `runWith_rel`, strong induction on the vertex is valid:

1. Below `initA.length`, both runs retain their input entries by `runWith_getD_of_lt`; `hlen` aligns the second run, and `hinit` supplies the relation.
2. Otherwise write the vertex as `initA.length + i`. Its range hypothesis implies `i < gs.length`. Both `runWith_getD_gate` equations read the prefix of exactly `i` gates; both prefixes have length `initA.length + i`.
3. Every argument is strictly earlier by `hacyc`. The induction hypothesis relates its entries in the full runs; `runWith_getD_take` transports those entries to the two prefixes. These are precisely the premises of `hgate`.

There is no requirement that the evaluators depend only on their argument entries: `hgate` already quantifies over arbitrary prefix lists with the required lengths. There is also no assumption about related out-of-range defaults; acyclicity keeps all queried arguments in range.

The relation may depend on the vertex, so it supports the depth-dependent invariant in GSW. Garbling's `runWith_sim` follows by taking `R v a b := (b = W v a)` and taking the second evaluator to be `fun g vs => fB vs.length g vs`. Its prefix-length premise turns `vs.length` into the gate's vertex number. The disclosed later deduplication is therefore viable.

The supplied axiom dump gives:

| Declaration | Dependencies |
|---|---|
| `DAGGate.getD_lt_depth` | `Quot.sound`, `propext` |
| `runWith_rel` | `Classical.choice`, `Quot.sound`, `propext` |

Neither proof reads another TCSlib definition by unfolding it. **No #332 finding.**

## PR #333: all 35 targets

Each row below is accepted as mathematically true with its displayed hypotheses. “Accepted” does not mean its Lean `sorry` has been discharged. The row numbers are the plan's target numbers.

| # | File · target | Reason |
|---:|---|---|
| 1 | Gadget · `digits_decomposeVec` | `blocksEquiv` composed with its inverse recovers the digit vector. |
| 2 | Gadget · `gadget_mulVec_decomposeVec` | Each gadget block evaluates the positional digits of the canonical residue; casting back recovers it. |
| 3 | Gadget · `gadget_mul_decompose` | Target 2 column by column; no finiteness hypothesis on the column index type is needed. |
| 4 | Gadget · `decomposeVec_block_eq_false` | A nonnegative positional sum equal to zero has every bit zero. |
| 5 | Gadget · `errorSum_decomposeVec_le` | Only one block survives; its ℓ binary-selected terms each have magnitude at most β. |
| 6 | Noise · `encrypts_gadget` | Error witness zero, message 1. |
| 7 | Noise · `encrypts_zero` | Error witness zero, message 0. |
| 8 | Noise · `Encrypts.mono` | Reuse the same error witness. |
| 9 | Noise · `Encrypts.add` | Add error witnesses; triangle inequality. |
| 10 | Noise · `Encrypts.neg` | Negate the error witness; absolute value unchanged. |
| 11 | Noise · `Encrypts.sub` | Subtract error witnesses; triangle inequality. |
| 12 | Noise · `Encrypts.sum` | Finite induction using targets 7 and 9. |
| 13 | Noise · `Encrypts.mul` | Exact witness `e₁ᵀX + x₁e₂ᵀ`, bounded by `Nβ₁ + |x₁|β₂`; see below. |
| 14 | Noise · `Encrypts.mul_bit` | A bit on the left has integer absolute value at most 1. |
| 15 | Noise · `Encrypts.mul_le` | Bit multiplication is conjunction; `Nβ + β = (N+1)β`. |
| 16 | Noise · `Encrypts.nand` | Subtract the product from noiseless G; `1 − b₁b₂` is the NAND bit. |
| 17 | Noise · `encrypts_chain` | List induction adds `Nβ` per fresh left factor; `Forall₂` supplies equal lengths. |
| 18 | Scheme · `vecMul_secretVector_augmented` | `−⟨s,aᵢ⟩ + (⟨aᵢ,s⟩ + eᵢ) = eᵢ`. |
| 19 | Scheme · `encrypts_encrypt` | Fresh error is `eᵀR`; every column is a binary subset sum of m errors. |
| 20 | Scheme · `encrypts_keygen_encrypt` | Read existing keygen/sample projections; `χ.Bounded B` bounds each realized row error. |
| 21 | Scheme · `decrypt_of_encrypts` | Regev residual is the bit codepoint plus a single-block error of magnitude at most ℓβ. |
| 22 | Scheme · `decrypt_of_encrypts_dyadic` | For `q = 2^ℓ`, the half-codepoint decomposition has one nonzero bit, so the error bound is β. |
| 23 | Scheme · `decrypt_keygen_encrypt` | Targets 20 and 21. |
| 24 | Eval · `homAnd_encrypts` | Empty/singleton bases and the right-associative product recurrence; natural subtraction is correct. |
| 25 | Eval · `homGate_encrypts` | Conjunction, negated conjunction, and De Morgan; fan-in at most two costs `(N+1)β`. |
| 26 | Eval · `eval_encrypts` | The vertex-indexed relation and strictly smaller argument depths give the depth induction below. |
| 27 | Eval · `decrypt_keygen_eval` | Fresh bound `mB`, target 26, depth monotonicity, then target 21. |
| 28 | Columns · `hashColumns_eq_mul` | Both entries are the same binary-weighted sum; the QS1 `Matrix.of` is correct. |
| 29 | Columns · `distAdv_hashColumns_uniform_le` | A hybrid replaces one independent column at a time; each neighboring gap is bounded by the existing strong single-column LHL. |
| 30 | Security · `real_uniformKey_advantage` | Reassociate the independent key, encryption, and test coins; equality with the stated DLWE advantage is exact. |
| 31 | Security · `uniformKey_uniform_advantage_le` | Augmentation is a bijection; use target 29 and the ciphertext translation by μG. |
| 32 | Security · `distAdv_encrypt_le` | Triangle inequality through both uniform-key views and a common uniform view. |
| 33 | Security · `distAdv_encrypt_le_of_width` | `Regev.two_extractionError_le` multiplied by N. |
| 34 | Symmetric · `encrypts_symEncrypt` | Reindex the augmented sample's error coordinates; each keeps bound B. |
| 35 | Symmetric · `distAdv_symEncrypt_le` | Each uniform DLWE sample maps bijectively onto the whole ciphertext batch; insert that common uniform distribution. |

### Noise calculations and boundary cases

All residue equalities below are modulo q. The error witnesses and their bounds are over the integers. Put `X = lift (decompose C₂)`, so its entries are 0 or 1 and `GX = C₂`. From the two `Encrypts` witnesses,

\[
\begin{aligned}
t^{\mathsf T}(C_1X)
&=(x_1t^{\mathsf T}G+e_1^{\mathsf T})X\\
&=x_1t^{\mathsf T}C_2+e_1^{\mathsf T}X\\
&=x_1x_2t^{\mathsf T}G+x_1e_2^{\mathsf T}+e_1^{\mathsf T}X,\\
\left|\sum_i e_{1,i}X_{ij}+x_1e_{2,j}\right|
&\le\sum_i |e_{1,i}|X_{ij}+|x_1|\,|e_{2,j}|\\
&\le N\beta_1+|x_1|\beta_2.
\end{aligned}
\]

This also covers negative integer messages. No noise independence or fresh-encryption hypothesis is needed. For a bit on the left, weaken `|x₁|` to 1. Subtraction from G negates the resulting error without increasing its bound.

For the right-associative chain of k fresh bit factors and an accumulator of bound β₀, the induction step is

\[
N\beta+\bigl(\beta_0+kN\beta\bigr)=\beta_0+(k+1)N\beta.
\]

The empty chain is exactly the accumulator and the empty Boolean product is 1. The message is consequently `(bs.all id).toNat * x`. No restriction on the integer accumulator message is missing.

For `homAnd` on k entries, the declared bound is

\[
\bigl(\max(k-1,0)N+1\bigr)\beta.
\]

At k = 0 the actual noise is zero and the displayed bound is β; at k = 1 it is β. At k ≥ 2 the recurrence is

\[
N\beta+\bigl((k-2)N+1\bigr)\beta=((k-1)N+1)\beta.
\]

Thus k ≤ 2 gives at most `(N+1)β`. Complementing a bit ciphertext as `G − C` preserves its noise bound. This proves the disjunction and negated-conjunction cases too, including arities zero and two for the library's `.not` gate. Repeated arguments are harmless. `homGate_encrypts` explicitly assumes its argument relations; mismatched list lengths need no extra hypothesis. Its default false/zero pair is consistent because zero encrypts zero noiselessly.

For a gate of depth d, each argument has depth at most d−1 and d ≥ 1. Since N+1 ≥ 1,

\[
(N+1)^{\operatorname{depthAt}(a)}\beta
\le (N+1)^{d-1}\beta,
\qquad
(N+1)\bigl((N+1)^{d-1}\beta\bigr)=(N+1)^d\beta.
\]

Inputs have depth zero. Apply `runWith_rel` with the depth-indexed `Encrypts` relation and read the in-range output. Acyclicity comes from `Cc.args_lt`; full `IsFaninTwo` is unnecessary. Counting negation gates in `depth` only makes the sufficient bound larger. Dead gates do not invalidate an output-depth bound because the invariant is proved separately at each vertex.

For decryption let `w = halfVector P` and let z be its lifted binary decomposition. Then

\[
Gz=w,\qquad t^{\mathsf T}w=\lfloor q/2\rfloor,
\]

\[
\begin{aligned}
\text{Regev residual}
&=t^{\mathsf T}Cz\\
&=b\lfloor q/2\rfloor+\sum_i e_i z_i,\\
\left|\sum_i e_i z_i\right|&\le\ell\beta.
\end{aligned}
\]

All blocks of z except the last vanish. The two codepoints have circular distance `floor(q/2)`. Under `2ℓβ < floor(q/2)`, the received residue is at distance at most ℓβ from its intended codepoint and at distance at least `floor(q/2) − ℓβ > ℓβ` from the other. This is exactly the existing `decode_codepoint_add` premise, including odd q and signed errors. There is no rounding or tie-rule gap.

For `q = 2^ℓ`, z has its sole 1 at block n, position ℓ−1 with zero-based indices. The noise bound is β and the condition becomes `2β < q/2`. `hℓ : 0 < ℓ` is redundant because `q ≥ 2` and `q = 2^ℓ` imply it; retaining it is harmless. More generally `q ≥ 2` and `q ≤ 2^ℓ` already exclude ℓ = 0. At q = 2 or 3 the general separation premise forces β = 0, and decoding is correct. B = 0, m = 0, and depth zero cause no exception.

Fresh encryption has error `eᵀR`, bounded by mB. Therefore `Cc.depth ≤ L` gives

\[
\beta_{\rm out}\le (N+1)^{\mathrm{Cc.depth}}mB
\le (N+1)^L mB,
\]

and the declared condition

\[
2\bigl(\ell((N+1)^L mB)\bigr)<\lfloor q/2\rfloor
\]

is sufficient for every key-generation seed and encryption coin matrix. No extra factor or `L+1` is required.

### Security calculations

For target 29, use hybrids whose first j ciphertext columns are independent uniform columns and whose remaining columns are independent binary hashes under the same public matrix. In each neighboring pair, the test receives the public matrix and one challenge column, samples every other column itself, and runs D. The existing **strong** LHL applies despite the shared matrix. The triangle inequality yields N times the single-column error. At N = 0 both samplers give the same public-matrix distribution and the gap is zero. This does not assert universality of the whole-matrix hash family.

With `ε = Regev.extractionError P.lwe`,

\[
\varepsilon=\tfrac12\sqrt{q^{n+1}/2^m}.
\]

Let `a_μ`, `u_μ`, and `p_unif` be D's acceptance probabilities on the real view of μ, the uniform-key view of μ, and the fully uniform key/ciphertext pair. Reassociating product seeds gives

\[
|a_\mu-u_\mu|=\operatorname{DLWEAdv}(\operatorname{reduction}_\mu D),
\qquad |u_\mu-p_{\rm unif}|\le N\varepsilon.
\]

The reduction's coins are exactly the independent binary matrix coins paired with D's coins. The augmentation bijection retains the **entire public key**; translation by μG is a ciphertext-space bijection. Hence

\[
\begin{aligned}
|a_{\mu_0}-a_{\mu_1}|
&\le |a_{\mu_0}-u_{\mu_0}|+|u_{\mu_0}-p_{\rm unif}|
  +|p_{\rm unif}-u_{\mu_1}|+|u_{\mu_1}-a_{\mu_1}|\\
&\le\operatorname{DLWEAdv}(\operatorname{reduction}_{\mu_0}D)
 +\operatorname{DLWEAdv}(\operatorname{reduction}_{\mu_1}D)+2N\varepsilon.
\end{aligned}
\]

If `q ≤ 2^w` and `m ≥ (n+1)w + 2κ`, then

\[
2N\varepsilon
=N\sqrt{q^{n+1}/2^m}
\le N\sqrt{2^{-2\kappa}}=N2^{-\kappa}.
\]

The statements are exactly the concrete, fixed-bit function-level claims approved by Q8. They do not establish the deferred efficient asymptotic primitive bridge. The statistical claims require no SIS hardness assumption.

For symmetric encryption, `m = kN` and `rowEquiv` partition all challenge rows into exactly k blocks. Augmentation, column reindexing, and translation by the chosen message vector form a bijection from a uniform challenge `(A,b)` to a uniform batch of k ciphertexts. Its inverse subtracts the message gadgets, assembles all columns through `rowEquiv`, and inverts augmentation. Thus both ideal message experiments have the same distribution, giving exactly the two displayed DLWE advantages. One common secret and all kN row errors are retained in the real experiment; no hidden independent-key assumption occurs. The empty batch also satisfies the statement.

## Fidelity, reuse, Rule 10, and roadmap

The construction is faithful to the disclosed gadget presentation. GSW13's square, flattened ciphertexts become rectangular gadget ciphertexts after the disclosed decompression/transposition and coordinate reordering. AP14 and Pei16 support the displayed left-vector invariant and multiplication algebra. The following differences are expressly disclosed: deterministic binary decomposition instead of AP14's randomized subgaussian decomposition; worst-case bounded integer errors; arbitrary sufficient gadget width; uniform secrets; the optional symmetric unit; and the Regev-based half-codepoint decryptor with its factor ℓ. The results do not claim the sources' Gaussian bounds or lattice approximation-factor theorems.

There is one source-notation point to resolve explicitly in reading the excerpts: under the standard Kronecker convention, AP14's printed `gᵀ ⊗ I_n` is **not literally** the displayed `diag(gᵀ,…,gᵀ)`. It differs by a column permutation. The code uses `I_n ⊗ gᵀ`, matching AP14's accompanying block-diagonal description and Pei16's formula exactly. I do not treat the reversed Kronecker expression as an undisclosed construction change. It is not correct to call the two Kronecker products entrywise identical without mentioning the permutation.

The operand mirroring is correct **with product order reversed under transposition**. GSW13/BV14 expand the right operand's error; AP14/the code expand the left operand's error. Accordingly, fresh ciphertexts belong on the left in the code's additive chains. The code does not assert that the two conventions produce identical ciphertexts in the same operand order.

Reuse is appropriate: the code consumes `LWE.Parameters`, noise/sample readers, binary subset-sum bounds, the existing bit decoder, Regev keygen/augmentation/decryption/extraction error, `Lossy.gadget` and its digit lemmas, `Randomized.blocksEquiv`, and the SIS single-column LHL. The `columnHashParameters` definition is the disclosed field-for-field Q11 copy; Q11 already authorizes it. The GSW security statements concern a different ciphertext space and are not duplicate public results merely because they mirror Regev's hybrid pattern. No further undisclosed duplicate was found. The generic column hybrid is placed in the shared hash layer, and the relational evaluator is placed in the circuit layer.

The Q9 namespace and file location are correct. The new facades import and list their children; the hash facade and `TCSlib.lean` export the additions. Imports are precise. The Q10 cross-topic gadget import is intentional. QS1's `Matrix.of` and QS2's qualified `GSW.mul` preserve the drafted meanings. The 23 `UNCHECKED` uses and F1–F4 resolutions are supported by the statement/API evidence; F3 and F4 are sketch-name corrections.

Every target has a sketch and the source anchors match the supplied passages: AP14 Definitions 3.2–3.3, Claim 3.4, Lemma 3.5, Corollary 3.6; GSW13 §3.3 and Lemma 1; BV14 Claims 3.4.1–3.4.2 and Lemma 3.6; Pei16 (6.1.4)–(6.1.7). The key-agnostic `Encrypts` predicate is broader than AP14's provenance-based “designed to encrypt” relation, as its documentation explains; the algebra and conditional correctness remain valid for that broader relation.

The authenticated supplied evidence records 12/12 final module checks and 278/278 root-closure checks with zero errors. Its axiom inventory has 285 declarations and 56 auxiliary constants, with `sorryAx` in exactly the 35 target rows. Its four seal variants total 48/48 successes. The sealed negative-control file fails at each of the five intended reads; the unsealed and positive controls pass. These establish the recorded behavior of the current statement surface and #332 proofs, not Rule 10 compliance of future target fills. Inspection of the new completed proofs and readers finds no forbidden read.

The phase-6/7 hooks fit the ruled BV14 roadmap. In particular, let C encrypt the selector bit b with noise β, and let `V₀,V₁` be the accumulated branch ciphertexts with noise at most β₀. The mirrored update is

\[
(G-C)\mathbin{\mathrm{mul}}V_0+C\mathbin{\mathrm{mul}}V_1.
\]

Targets 9 and 13 give its bound

\[
N\beta+(1-b)\beta_0+N\beta+b\beta_0
=\beta_0+2N\beta\qquad(b\in\{0,1\}).
\]

Thus k steps cost at most an additive `2kNβ`. The exact `|x₁|β₂` term is essential: replacing both products prematurely by `mul_bit` would unnecessarily double the accumulated bound. Worst-case analysis needs neither fresh noise independence nor BV14's probabilistic rerandomization guarantee. It incurs larger polynomial factors, which are disclosed and do not obstruct a polynomial ratio.

The decryptor's public column preprocessing leaves a modular inner product and rounding as the secret-dependent circuit, so the chosen circuit model and uniform-secret convention introduce no evident phase-6 obstruction. Barrington/PBP machinery, a decryption circuit with its depth bound, compactness/efficiency, weak circular security, and the asymptotic security bridge remain later obligations already identified by the roadmap. Phase 5 does not silently prove them or assume circular security from LWE. The accepted later small-secret-LWE assumption is unnecessary for this phase or the selected BV14 route.

## Evidence archive and notation

`gate41-gsw-statements-evidence.zip` contains this report, the independent read-only checker `verify_gate41.py`, its `gate41-integrity.json` output, and a short usage file. The checker verifies pack/Git correspondence and authenticates the furnished evidence; it does not run the audited scripts or Lean. Its 12,828 finite decryption-boundary checks for q = 2,…,127 are supplemental only; the general arguments above establish the audited bounds.

| Notation | Meaning |
|---|---|
| n, m, q, ℓ, N | LWE dimension, sample count, modulus, gadget width, and `(n+1)ℓ`. |
| G, `G⁻¹`, X, z | Gadget; deterministic binary decomposition; lifted decomposition of C₂; lifted decomposition of the half-codepoint vector. `G⁻¹` denotes a function, not an inverse matrix. |
| s, t, w | LWE secret, `secretVector = (−s,1)`, and the half-codepoint vector. In the sample-budget formula only, w is the residue-width parameter of that theorem. |
| C, Cᵢ, x, xᵢ, b, μ | Ciphertexts, integer messages, and Boolean messages interpreted as 0 or 1 where used in arithmetic. |
| e, eᵢ, β, βᵢ, β₀, B, β_out | Integer error witnesses; ciphertext/accumulator error bounds; row-error bound; output-error bound. |
| k, d, L | List/batch/program length as indicated, gate/circuit depth, and allowed depth bound. |
| R, D, χ | Binary encryption coins (or the explicitly local relation in the host proof), distinguisher, and finite-seed noise law. |
| ε, κ | Single-column extraction error and sample-budget slack. |
| a_μ, u_μ, p_unif | D's acceptance probabilities in the real, uniform-key, and fully uniform experiments. |
| V₀,V₁ | Accumulated branch ciphertexts in the roadmap calculation. |
| `ds`, g, a, v, j | Depth list, gate, argument/vertex indices, and column/hybrid index, as in the local formulas. |

[eval]: https://github.com/Shilun-Allan-Li/tcslib/blob/48d796a8a68cd50897047f01825a8132dd19e8d8/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean
