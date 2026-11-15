# Pass–shelat Gate 27 — B1 multi-message statement audit

**Verdict: CLEAR for the statement gate.** Counts: **0 blockers, 0 majors, 1 minor, 0 notes.**
The stated joint slice-security implication is mathematically sound and supplies the
security interface needed by Yao step 3. Its Lean proof remains intentionally admitted.

| Pin | Audited revision |
|---|---|
| Repository / PR | `Shilun-Allan-Li/tcslib`, draft [#311](https://github.com/Shilun-Allan-Li/tcslib/pull/311) |
| Lean head | `46b780dc1b286f59da18e2d10f188b0faaab8088` |
| Head tree | `e4056622589640b722e43251359f6901d978b984` |
| PR base | `013119f006af40d03b88b0fc2d9b453cf0a9b348` |
| Campaign records | `1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c` |
| Exchange | `2776272b61fcc7a1adf3f743c735c7e45be5045c` |
| Pack directory | `outbox/gates/27-b1-multimsg-gate/` |

## Finding

| ID | Severity | File / declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G27-01 | minor | `SecureComputation/SpecialEncryptionMulti.lean:207`, docstring of `sliceMultiMessageSecure_of_prfOut` | “Both fit exactly” is inaccurate. The inner slice uses `0+n+n=2n`, strictly below `L(n)=7n+2` for every natural `n`. The outer slice uses `2n+n+(4n+2)=7n+2`. The Lean inequalities and the probe are correct. | Replace with “Both shapes fit; the outer slice fits exactly.” |

Paths in this report are relative to `TCSlib/Cryptography/` unless otherwise stated.
This finding does not prevent statement-gate closure under the pack's severity rule.

## Integrity, scope and verification

I independently fetched the pinned Git revisions and checked:

- **Outer pack:** exact manifest path equality, **10/10 SHA-256 checks**. The bundle hash is
  `e56ff186ddb806660e05b92654c2b9465aae4801f1852e51dc985f004457db66`.
  All 11 directory files, including `SHA256SUMS`, match their Git blob identities at the exchange pin.
- **Bundle:** all **10 sections** match the Git blobs named by `BUNDLE-FILES.txt` at the specified
  Lean/records revisions. `README.md`, `pack.md` and the complete bundle were read.
- **Sources:** all **145 files** in `sources.zip` match the pinned Lean tree; its TCSlib import
  closure is complete. Both changed-file hashes, line counts and width counts match `source-head.json`.
- **Frozen scope:** the complete base/head tree comparison changes exactly two paths: the new
  325-line module and the facade's import and contents entry. The independent Git diff equals
  `pr.diff.txt` byte for byte. All other files, including `SpecialEncryptionSecurity`,
  `SpecialEncryption`, `GarblingSpecial`, `Yao` and `FromPRF*`, are unchanged.
- **Nested evidence:** `verification.zip` has exactly **27 manifest paths plus its manifest**;
  all hashes verify. Its `stmt-b1-evidence.zip` has exactly **120 manifest paths plus its
  manifest**, with all hashes verified; its manifest equals `evidence-SHA256SUMS` byte for byte.
  All **20 cited evidence extracts** are byte-identical to their originals. The evidence ZIP
  itself matches the records pin and has SHA-256
  `b3b554d67a89bad54e8fc96adaa2001bd463c47889b21c23ae0b9f5dba9c63f3`.
- **Records reconciliation:** the verification snapshot's decision log predates the records pin
  by exactly one appended “Gates 27–28 packs” row. The cited plan, ledger and provenance match
  the records pin. This is the disclosed older snapshot, not a conflicting ruling.

The supplied runs report **63/63 modules rc 0**, zero errors and one intended admission warning;
the root and audit-check modules are included. Their complete logs agree with the summary.
The supplied lint logs both contain **92 FAIL / 101 WARN**, with an empty FAIL/WARN diff.
The before/after olean manifests are identical, SHA-256
`457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`.

**Verification limit:** no Lean executable was available in this audit environment. I did not
replay compilation or the seals. These are verified supplied run records, supplemented by my
independent byte comparisons, proof-source review and mathematical statement audit. This report
does not certify a completed proof of the admitted theorem.

## Truth and quantifiers

The declaration has the required order:

\[
\forall D,q\;\exists\varepsilon\text{ negligible}\;\forall n,o,\mathrm{len},m,m',
\quad\mathrm{fit}\Longrightarrow\mathrm{distAdv}\leq\varepsilon(n).
\]

In particular, the slices can be selected after the negligible bound. This strengthening is
valid because the theorem fixes `L = ℓ.eval`, a polynomial; it does not assert the implication
for an arbitrary, potentially superpolynomial `L`.

The following verifies the proof route mathematically; constructing the oracle machines and
formalizing the distribution identities are still fill obligations.

1. For each `n`, let `A(n)` be the maximum advantage over fitting slice vectors and message
   pairs. **Set `A(n)=0` if there is no fitting slice vector.** The latter convention is needed
   when `ℓ.eval n < n`. Otherwise the maximum exists: there are `q.eval n + 1` entries, each
   offset and length is at most `ℓ.eval n`, and every message has its prescribed finite length.
2. Choose a maximizing tuple separately at each `n`. The offsets, lengths and messages have
   polynomial total encoding length: even unary offsets and lengths take
   `O((q.eval n+1)·(ℓ.eval n+1))` bits. Thus two fixed non-uniform PPT oracle machines `D₀,D₁`
   can carry the maximizing slices and the respective message vector as advice. At parameters
   with no fitting slice vector, both machines reject. Otherwise they sample
   independent `n`-bit nonces, make `q.eval n+1` queries with `ℓ.eval n`-bit answers, form the
   ciphertext tuple and run `D` with its coins. Their keyed/random advantages are negligible
   by `hG.pseudorandom`, with query-budget polynomial `q+1`.
3. Fix a tuple of pairwise distinct nonces in the random-function experiment. The corresponding
   full answers are independent uniform strings. In each answer, the intervals
   `[o_i,o_i+n)` and `[o_i+n,o_i+n+len_i)` are disjoint and contained in the output by the fit
   hypothesis. Projecting onto these bits and XORing the latter interval with the fixed
   message therefore gives a uniform `(n+len_i)`-bit body. Consequently the complete encoded
   tuple, conditional on those nonces, has exactly the same law for `m` and `m'`.
4. The good-event contributions to acceptance cancel. Each bad-event contribution lies in
   `[0, Pr[nonce collision]]`, so their difference has absolute value at most that probability,
   **with coefficient one**. The union bound gives

   \[
   \Pr[\exists i<j:r_i=r_j]
   \leq {q.eval\,n+1\choose 2}\,2^{-n}.
   \]

   Overlapping slices in different ciphertexts cause no additional loss when the nonces are
   distinct. On repeated nonces no independence is claimed.
5. The triangle inequality, applied to the maximizing tuple, gives

   \[
   0\leq A(n)\leq
   \operatorname{adv}(D_0,n)+\operatorname{adv}(D_1,n)
   +{q.eval\,n+1\choose 2}\,2^{-n}.
   \]

   Both oracle-advantage functions and the collision term are negligible; the latter is the
   existing `MultiMsg.negligible_choose_div_two_pow`. Hence `A` is negligible, and
   `ε=A` bounds every fitting tuple simultaneously.

No exceptional hypothesis is needed at `n=0`: the collision bound may be large, and negligible
functions may have arbitrary finite initial values. With `q.eval n=0` there is one ciphertext
and no collision pair. Zero-length messages are covered. With `ℓ.eval n<n`, the slice premise
is impossible. These cases do not invalidate the statement.

## Sufficiency for Yao step 3

The joint family and the evaluator hypotheses in `yaoHybrid_simulators` match the new API.
The two applications are exactly:

| Occurrence of the inactive wire key | Slice `(offset, message length)` | Fit in `L(n)=7n+2` | Bridge |
|---|---|---|---|
| Second argument of a two-input row, or only argument | `(0,n)` | `2n ≤ 7n+2` | `sliceEnc_append_left`, with message length `n` |
| First argument of a two-input row | `(2n,4n+2)` | `2n+n+(4n+2)=7n+2` | `sliceEnc_append_right` |

The outer plaintext is an inner ciphertext of length `4n+2`, by `length_spEncStr` and the
evaluator specification. The outer bridge is valid for every list; its security application
uses precisely that length. The inner bridge's condition `|m|≤n` is discharged by its
`n`-bit plaintext.

The non-adaptive interface suffices, for these reasons:

- Split a gate transition into at most two replacements, one for each inactive argument key.
  Include **every occurrence** of the selected key across all gates reading its wire. Rows
  whose plaintext does not change are included with equal left/right challenge messages.
- That inactive key is not a plaintext in the current hybrid: if its wire is a gate output,
  that earlier gate has already been made fake and emits its active key. It is absent from
  opened input keys and OT answers. `YaoCircuit.outs_sink` excludes it from output decoding pairs.
- `DAGCircuit.IsWellFormed` gives `g.args.Nodup`; hence the same wire is never both arguments
  of one row. An outer challenge plaintext is an inner ciphertext under another, sampled
  key, prepared before seeing any challenge ciphertext. An inner challenge ciphertext is
  wrapped afterward under the known other key. Thus no challenge plaintext needs a previous
  challenge ciphertext. Accidental equal values of independently sampled wire keys do not
  invalidate this simulation; the reduction knows the keys it sampled.
- The two nonce blocks of `nestedSpecial` are independent in `yaoSeed`. The challenge supplies
  the nonce of the unknown-key layer; the other block is sampled separately. All unknown-key
  occurrences fit in a fixed polynomial count (at most four rows per gate); unused challenge
  slots can be padded with equal messages and ignored.
- `encodeList` is a polynomial-size nested-pair encoding with published cons/nil readers.
  The reduction can extract challenge components and rebuild the garbling. `distinguisherL n`
  runs at common input `1^n`, matching the protocol parameter. Auxiliary randomness can be
  averaged or fixed as polynomial advice independently of the unknown key and its nonces.

The supplied `yao_step3_instance` establishes the joint-family instantiation, both bridge
equalities and the fit arithmetic. It does **not** itself formalize the row enumeration,
independence or complete hybrid reduction; those remain Yao proof obligations as described above.

## Corollary, readers, Rule 10 and reuse

`specialScheme_multiMessageSecure_of_joint` has exactly the frozen conclusion. Taking every
slice to be `(0,n)` gives fit `0+n+n≤n+n`. Its product equivalence relabels the generator's
coins as a uniform key and every encryption tape as an independent uniform nonce, preserving
their strings. The sampler identity then follows from the published generator/encryption
run equations and `sliceEnc_eq_spEncStr`; `acceptProb_comp_equiv` transports the advantage.
The supplied `frozen_from_joint` composes this corollary with the admitted target at the
intended polynomial `(.add .var .var)`. No output-length or quantifier mismatch was found.

All three new definitions have exact public readers, with formulas and without `@[simp]`:
`sliceEnc_eq`, `sliceMultiEncDist_apply`, `sliceMultiMessageSecure_iff`. All three bridges have
correct statements. The proofs read `spEncStr` via `spEncStr_eq`, and `specialScheme` via its
published projections and run lemmas. They reuse the published NUPPT coin equivalences.

I compared the three bridge proof bodies with their sealed probe copies: exact matches.
The complete corollary section, including all six private helpers, matches its probe modulo
the probe theorem's name. The supplied probe has exactly the two expected sealed-control
errors at lines 247 and 252; the unsealed controls have none. Its axiom output reports no
`sorryAx` for the corollary, readers or bridges. The composite and Yao instance inherit
`sorryAx` through the intentionally admitted target. I found no forbidden definition read
in the proved declarations on inspection, under the stated projection/coercion ruling.

The new security predicate is justified: `PrivateKeyScheme.MultiMessageSecure` fixes
`n`-bit messages and one scheme, while Yao needs varying per-ciphertext lengths and slices
under one common key. `prfScheme_multiMessageSecure` concerns a different encryption sampler
with `n`-bit output pads. This PR does not copy its security proof; it reuses the existing
scheme/security definitions and proves a genuine specialization. No new duplication finding
was identified in the requested comparison with `FromPRF*` and the frozen special-scheme result.

Placement, sole import, facade export, module sections, public formula docstrings, attribution,
deviation disclosure, proof sketches and line widths satisfy the gate's requirements, apart
from G27-01. `maxHeartbeats 0` follows the explicit repository policy.

The source comparison used [Pass–shelat, January 2010](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf),
Definition 93.1, Theorem 99.2 and §6.2.2, Algorithm 157.2. The slices and length generalization
are disclosed extensions; the source is not being cited as already stating this joint lemma.

## Required handoff to the proof jobs

These are pending implementation obligations, **not additional statement-gate findings**.

1. **`prf-long`: separate nonce and answer lengths.** Generalize the existing PRF advantage
   bridge and query-chain realization from `n`-bit answers to `ℓ.eval n`-bit answers while
   retaining `n`-bit queries, keys and nonces. Publish a query-tree evaluation identity for
   arbitrary oracles, with the coin equivalence and polynomial advice/query bounds. The
   consumer needs polynomial-time postprocessing of the full answer transcript into varying
   slices, not merely a theorem about equal-length XOR messages. A generic transcript
   postprocessor, or an equivalent sufficiently general API, is suitable. Keep the old
   `n`-output results as specializations; do not copy their implementation into secure computation.
2. **Existing general readers can be reused.** `OracleEnsemble.keyed_O`, `random_O` and
   `acceptProb_random_eq` already allow general output length. `MultiMsg.chainTree` and its
   evaluation/budget lemmas, `uprob_not_injective_le`, `pushesUniform_comp_injective` and
   `negligible_choose_div_two_pow` already provide reusable generic pieces. No missing
   reader was found that must be added to this statement PR before it can close.
3. **`sc-garble`: complete the slice proof.** Implement the finite maximizing advice with
   the empty-set convention above, compile the slice postprocessor using B3, prove the
   random-function slice law with disjoint prefix/mask bits, and close the triangle bound.
   Then fill the frozen special-scheme theorem through the proved corollary. Also retain
   the separate B2 requirement to publish the stronger garbling bound needed for `yaoSeed`.
4. **`sc-yao`: prove the embedding.** Formalize the gate/row subhybrids, all-occurrence
   enumeration and padding, the no-dependence argument, and the exact coin/view sampler
   identities; establish the polynomial-time reconstruction. The three bridges are sufficient
   at the ciphertext level, but are not substitutes for those proofs.

The pinned records specify B3's ownership and order adequately for this statement gate.
The forthcoming `prf-long` brief should spell out item 1's public API before dispatch.

## Reproduction and notation

The companion ZIP includes this Markdown, the original pack, pinned source indices, additional
comparison sources, `evidence/check.py` and its `results.json`. Running
`python3 evidence/check.py` from the extracted report directory repeats the byte/source/evidence
checks without Lean. The recorded indices can be checked against fresh fetches of the listed
Git revisions; an offline index is not a replacement for that remote provenance check.

**Glossary:** `n` is the security parameter; `q.eval n+1` is the number of ciphertexts;
`L(n)=ℓ.eval n` is the theorem's PRF output length; `o_i` and `len_i` are the slice offset and
message length; `D` is the ciphertext distinguisher; `A(n)` is its maximum fitting advantage
(zero for an empty feasible set); `D₀,D₁` are the two oracle reductions; `adv(D_b,n)` is their
keyed/random oracle advantage; `F` is a uniform random function; `r_i` are the independent
nonces; `ε` is the uniform negligible bound. The inactive key is the unopened key of the
wire selected in a Yao subhybrid.
