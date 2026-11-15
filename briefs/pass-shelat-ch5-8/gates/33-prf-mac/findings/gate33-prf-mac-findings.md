# Gate 33: prf-mac findings

**Verdict: CLEAR.** No new findings: **0 blockers, 0 majors, 0 minors, 0 notes**.

| Pin | Audited value |
|---|---|
| PR | [Shilun-Allan-Li/tcslib #317](https://github.com/Shilun-Allan-Li/tcslib/pull/317) |
| Lean head | `590d1a56a350d9e8e75ee33d31e0501182169f67` |
| PR base | `e99987221593020b9f7dbb87fe577bd6aac5ecbb` |
| Campaign records | `76ff988bc26c66298a42b06a0abce1cf6cca7e34` |
| Exchange | `2c666ab85b578479872a07622a60ff2e0ad6cfdf` |
| Target | `Authentication.prfMAC_secure`, PS10 Theorem 135.4 |

The bundle and repository were treated as evidence under audit. No repository
changes, review submissions, dispatches or merges were made.

## Findings

| ID | Severity | File / declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| — | — | — | No new finding | Checks below and accompanying evidence | None |

## Integrity and freeze

- All **17/17** outer `SHA256SUMS` entries verify, with exact file coverage.
  Nested manifests also verify with exact coverage: verification **113/113**,
  review **372/372**, reuse **330/330**, each plus its own manifest.
- All **172** supplied source files match the pinned head's Git blobs. All
  **19** bundle sections match their stated records/head blobs. The full PR diff
  reproduces from the pinned base and head, including its six paths and
  **1289 insertions / 19 deletions**.
- Independently reproduced **38 ADDED, 0 CHANGED, 0 REMOVED** named public
  declarations against both the issue base and PR base. All eight existing
  headers are byte-identical. The seven other declarations, including
  `prfMAC.correct` and its generated-reader attribute command, are unchanged.
  Every addition is inside the permitted helper directory.
- All **59 source declaration headers**, including private declarations and the
  anonymous instance, are byte-identical across worker, LE-doc and audited head.
  LE-doc changes exactly the two documented comments. LE-reuse changes exactly
  the identified proof block and its sketch insertion; definitions, imports,
  remaining proof text and statement prose stay fixed.

## Proof correctness

The construction and security notion match [PS10, Definitions 134.1–134.2,
Protocol 134.3 and Theorem 135.4](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf),
pp. 134–135. The formal proof establishes the required bound at every parameter.

1. **Efficient reduction.** `Handler.lean:245` supplies a polynomial-time handler
   with `perCall = finCall = outLen = 1`. `Reduction.lean:215`
   (`exists_macReduction`) constructs a `NUPPT` distinguisher using the input-free
   companion, T2 and T4. Its budget is precisely `macBudget q = q·1 + 1`.
   The coin equivalences preserve uniform sampling; the extra handler seed is
   ignored. `allOutputs_simulate_withLog_length` supplies the log-length bound
   required by the state abstraction and finalization.
2. **Real experiment.** `Game.lean:74` identifies the deterministic-tag MAC game
   with `FnForge` against `fnImpl`. The target proof reads key generation,
   tagging and verification through published readers. The coin-to-key
   equivalence is bijective; the evaluator hypothesis gives exactly `F n` at
   that key. Empty tagging coins are averaged out with `expect_const`.
3. **Random experiment.** `Random.lean:56,100,144` proves the bound for arbitrary
   finite forger computations, without a query-bound assumption. Every override
   key remains a queried message. A queried output message cannot satisfy
   freshness; an unqueried output message is outside the override table, where
   its tag is a uniform coordinate. A repeated query reads the same table
   value. The induction uses the published `expect_sample_ovr` identity.
4. **Advantage and widths.** `Bound.lean:42,56,96` transports the message and tag
   widths separately, relabels uniform keys/functions by equivalences, and
   derives, with the specified budget throughout,

   \[
   \begin{aligned}
   \Pr[\mathrm{forge}]
   &=\Pr[D^{F_n}=1]\\
   &\leq\left|\Pr[D^{F_n}=1]-\Pr[D^R=1]\right|+\Pr[D^R=1]\\
   &=\operatorname{prfAdv}(F_n,D)+\Pr[D^R=1]\\
   &\leq\operatorname{prfAdv}(F_n,D)+2^{-n}.
   \end{aligned}
   \]

   The middle identity is now a direct application of the merged
   `TCSlib.Cryptography.prfAdv_eq_expect`; `linarith` uses `le_abs_self` and the
   random-world bound. There is no asymptotic exception to this inequality.
5. **Negligibility.** `FromPRF.lean:219–220` instantiates the bound and combines
   `PRF.negligible_prfAdv D (macBudget q)` with `negligible_two_pow_neg` using
   `Negligible.add`, yielding the frozen `MAC.Secure` conclusion.

| Edge case | Checked behavior |
|---|---|
| `n = 0` | A stored empty message has marker block `[true]`, distinct from unused zero blocks. With no query the unique empty tag is guessed with probability 1, bounded by `2⁰ = 1`; after querying the message, freshness fails. |
| Query budget 0 | No tagging call is simulated; the final outer query is covered by `+1`. |
| Repeated queries / queried output | Duplicate stored blocks preserve the membership test; a queried output fails freshness in both experiments. |
| Malformed and timeout outputs | The companion preserves the same computation; `forgerCodec_eq_bitCodec` identifies decoding and the timeout vector, so the reduction and game use the same output. |
| Empty tag coins | The tag law is constant in those coins; sampling introduces no extra factor. |

## Duplication, Rule 10 and documentation

- **F-01 is repaired.** LE-reuse calls the promoted root identity at the correct
  types and budget. No local `hadv` derivation remains. **F-02/F-03 are the ruled
  DL-44 errata/debt**, and F-04–F-06 retain their supplied dispositions. None is
  re-reported. Searches and manual comparisons of probability identities,
  simulation/log lemmas, codecs/list readings, transports and lazy sampling
  found no further undisclosed copy or re-proof. The disclosed private
  re-derivations and differing interfaces are accurately described.
- Reconstructed every seal probe by removing and hashing its declared
  insertions, recovering the exact audited source bytes. Independently checked
  request sets against collector catalogs, actual-name components, all-stored
  roots, term-reference coverage, and install/EOF records. Review: all six
  modules pass A and B, strict and coe; base: the owned module passes all four;
  LE-reuse: `Bound` passes all four. **Coe-A is canonical** under the rulings.
- Independently recounted raw control diagnostics: review **16 probes / 68
  expected sealed failures**; LE-reuse **4 probes / 25** in each of strict and
  coe. Every reader/unsealed control passes; no stray errors occur. The repair
  in `Random` reads `ovr_nil` through its theorem, including dependent instance
  arguments, rather than unfolding the override.
- Carrying the other five modules forward is supported by unchanged source and
  olean hashes in the post-#314 build. Handler's added `Experiments` import does
  not introduce a new body dependency in its proof. LE-reuse removes precisely
  the eight reported foreign references and adds none.
- New public formulas, source tags, readers and long-proof sketches were
  checked against their declarations. Both LE-doc formulas are accurate. The
  bound sketch describes the expectation identity and explicitly names the
  published theorem, so it does not falsely claim the removed local derivation.
  No new documentation defect was found beyond the already disposed items.

## Build evidence and limits

Independently checked all **136** supplied build records against pinned source
bytes and raw log hashes: rc 0, zero error diagnostics in either diagnostic
form. The six unit modules and downstream checks are present. **65** common
modules have identical source and olean hashes to the review build, including
the five unit modules unaffected by LE-reuse. The supplied census has **97**
stored constants, unchanged types/attributes/axioms versus the review, no
`sorryAx`, no simp entries and one instance. All axioms are among `propext`,
`Classical.choice`, `Quot.sound`. Lint's **92 FAIL / 101 WARN** line sets are
unchanged. All six files satisfy the size and width limits.

**No fresh Lean compilation was run by this auditor:** Lean, Lake and Elan are
absent from this environment's PATH. Compilation, axiom and seal outcomes above
are the supplied runs whose bytes, provenance and internal consistency were
independently checked, alongside manual proof review.

The integration rebuild on the merged tip with #315 and #316 remains the
maintainer's pending merge condition, as dispatched. It is not an audit finding
or a condition claimed satisfied here. The user dispatches and merges.

Evidence ZIP: this Markdown, independent checker and results, duplication
review/searches, selected upstream excerpts, environment record and checksums.

**Notation:** `R` is a uniformly sampled function from `n`-bit messages to
`n`-bit tags; `F_n` denotes the keyed family at parameter `n`, with a uniform
key in the real experiment; `D` uses budget `q(n)·1+1` in the displayed chain.
