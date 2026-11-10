# Independent preparation while the statement audit runs

The user dispatched the Codex statement audit for PR #237. Both #236 and #237
now target `cryptography/lwe-sis-constructions`. The verified input is exchange
`90d652e19508262b3bd81234260d0585aaf8e0a0`, frozen Lean/root
`a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`, bundled records
`4f403f777cda259ced52d74243d7ff7f9d547f99`.

This continuation changes records only. The eight mathematical modules, their
31 admitted proof obligations, root/facade exports, policies and pins remain
frozen. No new branch, Lean declaration, proof fill, native check, paid model
call or external dispatch is introduced by this preparation.

## Source acquisition and ingestion readiness

The existing local Pei16/Wu24 PDF archives were rehashed. Deterministic raw
extraction now covers 90 Peikert pages and 106 Wu pages. The extraction uses
installed `pdftotext -layout` with the existing `proofmatch.extraction`
formatting/page-diagnostic functions; `pdf2txt.py` is not installed on this host.
The receipt records the actual extractor, helper hash, original PDF fingerprints,
raw output fingerprints and suspect pages. The raw texts remain in the own
`.lake/primary-sources/` archive, outside the committed review packet.

These are unvalidated extractions. No cleaned `.md`, approved proofmatch,
blueprint citation or dataset update is claimed. The phase-0 source-policy
note remains open for validation, ingestion and applicable source matching.

The generic wrappers are broader than this two-source task:

| Existing implementation | Scope relevant to a future source job |
|---|---|
| `scripts/dataset_pipeline.py:393`, `stage_references` | Processes explicitly named sources and also every pending PDF under the global references directory |
| Same file `:557`, `documents_to_match` | Considers all ingested, unmatched documents; explicit sources do not restrict the candidate-document list |
| `proofmatch/cli.py:185`, `_extract` | Handles one named PDF; `--local-only` stops before model cleanup |
| `proofmatch/document.py`, `repair_document` | Existing cleanup/validation route for one raw text, with its original PDF |

Consequently a future source job should use the per-document interfaces in its
own checkout and a dataset restricted to the owned declarations. Do not treat
`--source` or `--modules` as a guarantee that the generic wrapper will launch
only these two document jobs. No change to that shared pipeline is proposed here.

The exact prospective source-registry diff is
`source-ingestion/proposed-source-registry.patch`, with baseline/proposed hashes
and the two added entries in `source-ingestion/registry-proposal.json`.
It adds only Pei16 and Wu24; existing entries are preserved. It is **not applied**.
The target remains `blueprint/src/references/sources.json`, after the corresponding
validated reference pairs exist and the shared-file change is reviewed. Other
campaigns' tags, reference documents and datasets remain outside the delivery scope.

A future ingestion/matching job needs its own explicit Codex/Claude selection and
user dispatch. The current Codex selection authorizes the statement audit only.
The worker must preserve original PDF identity and page anchors, repair all relevant
mathematical symbols against the PDF, return diagnostics and validated document
fingerprints, and distinguish source-stated facts from the local dyadic specialization.
The maintainer checks the result before registration or source-policy closure.

## Machine adapter implementation map

These are future consumer contracts, not new Lean statements or efficiency results.
All source references below are to the current pinned checkout.

| Adapter | Required correspondence and existing owner route |
|---|---|
| Fixed-width numeric conversion | Candidate encodings are MSB-first; `BinArith` uses normalized LSB-first words. Reversal already has a proved public owner, `BinArith.polyTimeComputable_reverse` in `Complexity/ClassP/BinaryArith/Mul.lean:73`. Reuse it; add only the fixed-width/numeral correspondence and normalization accounting. |
| Dynamic block cutting | Reuse `polyTimeComputable_takePrefixByLength` / `dropPrefixByLength` in `ClassNP/PolyTimePrefix.lean:345,358`, with unary length words computed by the existing polynomial evaluator. Fixed-constant `drop` is insufficient for parameter-dependent offsets. |
| Dyadic modular arithmetic | Reuse the public `BinArith` addition, multiplication, comparison and subtraction results. Prove that retaining the low residue-width bits implements reduction modulo the dyadic modulus. For modular subtraction, add a modulus before unsigned subtraction; truncated natural subtraction alone is incorrect on negative differences. |
| Matrix traversal | Reuse `polyTimeComputable_stateFind` and `polyTimeComputable_blockMap` in `Randomized/Repetition.lean`, or the existing counted-loop host. Supply polynomial loop-state envelopes, total malformed-input behavior and exact canonical output lengths. No private replacement host is needed. |
| Uniform matrix/secret generation | Partition unbiased coins into fixed-width entries and prove the induced distribution is exactly the full uniform modular matrix/vector for a dyadic modulus. Use the existing bit/numeral equivalences; canonical encoding injectivity by itself is not a uniform-sampling proof. |
| Actual-noise implementation | A finite `Noise` need not have a fair-bit implementation. Choose an explicitly implemented bit-seed noise profile or prove a law-preserving sampler/controlled approximation. Give uniform parameter/sampler computability separately from `Family`'s size bounds. Retain the actual law in `DLWEAssumption`. |

The reversal lemma is available, so a second reversal implementation would duplicate
existing proved material. The remaining conversion correspondence is not supplied
merely by importing that lemma. None of these source-body observations establishes
the entire imported host chain's axiom closure; check that at the future machine gate.
`Candidates.ArithmeticFP` remains a conditional bundle, not a substitute for such work.

## Regev common-secret batching and advice

For polynomial message budget `Q`, the existing multi-message notion encrypts
`Q.eval κ + 1` messages of `κ` bits, requiring `κ * (Q.eval κ + 1)` rows under one
secret. Use the explicit sample substitution already stated in the audited slice;
do not silently strengthen the fixed-sample assumption or generate a new secret per row.

A whole LWE challenge encoding stores **all matrix entries followed by all values**.
It is not the concatenation of its per-message challenge encodings. The reduction
must parse/reshape the matrix and value blocks, add the message offsets, and emit
the existing `PrivateKeyScheme.encodeList` tuple. Its functional correspondence must
be proved before identifying the machine's distribution with the mathematical hybrid.

Nested-pair encoding also has length overhead. The owner equation for `pairEncode`
is `2 * first.length + second.length + 2`; a list of `count` strings each of
`itemBits` bits therefore costs `count * (2 * itemBits + 2)` bits. Use this budget
for plaintext advice and ciphertext tuples, rather than raw concatenation length.
`NUPPT.exists_withAdvice` in `Randomized/Closure.lean:360` already accounts for
pairing the adversary's original advice with the added vector. Each of the two
hybrid reductions needs its own worst-case plaintext vector; uniform computability
of that maximizing vector is not required or asserted.

## SIS collision-output adapter and owner boundaries

For the dyadic SIS profile, the matrix index and generator coins have the same
canonical bit length. The evaluator must parse the index, sum selected columns
modulo the dyadic modulus, and emit the exact declared output width. It must also
remain total and polynomial-time on malformed machine inputs.

The future CRH bridge waits for the approved owner API. Its raw collision output
must first undergo that owner's padding/truncation and split into two domain words.
Then each bit pair gives the signed integer difference directly:

| First bit | Second bit | Integer difference | Canonical sign/magnitude |
|---|---|---:|---|
| false | false | 0 | false / zero |
| false | true | −1 | true / one |
| true | false | 1 | false / one |
| true | true | 0 | false / zero |

Use the family's exact signed block width and the existing decoder-completeness
contract. This postprocessor does not need general signed subtraction, hash
evaluation or an in-machine collision test. `NUPPT.exists_compParam` preserves
the finder's advice and coins while adding parameter-aware postprocessing.

No adaptive CPA or CRH owner definition is edited here. Any future shared-owner
change needs its exact proposed diff and user coordination. Source ingestion has
an explicit proposed data diff above; it has not altered the shared registry.

## Notation glossary

`κ` is the security parameter and SKE message length. `Q` is the syntactic
polynomial message-count budget. `count` is the number of strings in a tuple;
`itemBits` is the common bit length of each string. MSB/LSB mean most/least
significant bit first. A dyadic modulus is a power of two.

**Not yet clear to merge — the statement audit is running; this records-only
preparation leaves all audited Lean files frozen.**
