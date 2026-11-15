# Pass–shelat Gate 31 — prf-long

**Verdict: CLEAR for the machinery audit.** **0 blockers, 0 majors, 1 minor, 0 notes.**

Audited draft [PR #315](https://github.com/Shilun-Allan-Li/tcslib/pull/315) at Lean head
`fbd37f447596d4207c8d08b7ef7602f57fe95198`, with campaign records
`9cc4db6204a9965da907471603993e9c24d105d2` and exchange
`37f16e2b7222d0723c17ed1e1666a290f707b0e6`. Comparisons use issue base
`7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` and PR base
`dd98360d4886ac68fab34899b8bd0d12ae9a0aef`.

This verdict covers B3's D1–D4 machinery and the supplied dispositions. It does not claim that
B1 or another admitted target has been proved. The maintainer's downstream integration rebuild
after merged #314 remains a merge condition, as requested; its pending status is not an audit finding.

## Finding

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G31-01 | minor | `review.md`, “Rule 10” and F-07; PR #315 description, “Review / Rule 10” | “Seal B fails only where the base already fails” is false. Six additional declarations fail B at the head; two are in `ReductionMachine`, whose base passes B. The pack correctly discloses this, so there is no evidence gap or Rule-10 violation. | `verification.zip:evidence/logs/seal-table.txt`; the raw base/head B logs, checked against their manifests and source instrumentation. The additional failures are the two D1 declarations, `postFun_layout`, `exists_queryChain_nuppt`, the D4 total, and `prfScheme_multiMessageSecure`. | Correct the review and PR description: A passes in every file, strict and coe; B has six additional failing declarations, all attributable to permitted `PolyExpr.eval` reductions or their cascades. |

## Verification and limits

I independently checked source bytes, hashes, statement preservation, instrumentation, raw diagnostics,
and the mathematical/API arguments. **I did not execute Lean.** Build, axiom and seal results below
are verified archived evidence, not fresh compiler runs. The supplied frozen parser was inspected
and replayed; it is identified as supplied material in the reproduction script.

| Check | Result |
|---|---|
| Outer pack | All **18/18** `SHA256SUMS` entries verify; pack files bind to the pinned exchange's Git blobs. |
| `verification.zip` | **95/95** hashes; exactly those paths plus `SHA256SUMS`: 96 files. |
| Nested review archive | **644/644** hashes; exactly the manifest paths plus its identical `SHA256SUMS`: 645 files, 710 ZIP entries including directories. |
| Source provenance | All **180** closure sources and all **18** bundle sections bind to their pinned Lean/records blobs. Git tree inventories were reconstructed and checked against the five pinned commits. |
| PR scope and patch | Exactly the six permitted changed paths. Reconstructing their diff from verified base/head blobs reproduces `pr.diff.txt` byte for byte. |
| Frozen declarations | **126** retained declarations, **38** unchanged complete definition bodies, **61** additions, **22** changed theorem proofs. No header, statement prose, declaration order, or existing top-level command changes. Five negative controls each detect exactly one violation. |
| Recorded build | **121/121** modules: rc 0, zero errors in both diagnostic forms. All 121 source hashes match the pinned head, and all 121 raw-log hashes verify. The archived whole-tree check reports 1244 modules, `RESULT OK`. |
| Elaborated census | 250 → 321 stored constants; all retained type/attribute/axiom records agree. Fifteen removals are generated auxiliaries; 86 additions include the 61 named declarations. No removed auxiliary has an explicit use in the searched head sources or #313's learning sources. Only `propext`, `Classical.choice`, `Quot.sound` occur. |

The campaign's unchanged admission count and #305-adjusted lint baseline are consistent with the
source delta and evidence. No new admission or explicit instance, abbreviation or `@[simp]` declaration is introduced.

## D1–D4 and proof-only re-derivations

The **23 drafted signatures** match, including the expanded elided binders. The disclosed
`postQueryOut`, explicit `n` arguments and additional readers are justified. `postQuery` reads
the width-dependent offset, so its generic counterpart is necessary.

- **D1:** the generic advantage identity reads `prfAdv` through `prfAdv_def` and identifies the
  same-file oracle ensembles. Its negligibility corollary transports precisely the oracle
  indistinguishability hypothesis. The two old theorems are its `.var` cases.
- **D2:** the PRF hybrid changes only answer/mask width. The random-function comparison reuses
  the uniform-restriction and coupling lemmas; the collision probability concerns the unchanged
  `n`-bit points. Uniform pads are relabelled by a Boolean-group bijection. The six-hybrid bound
  has two PRF advantages and `2 · C(q+1,2)/2^n`, as drafted.
- **D3:** history and mask lengths are both `4n + 2ℓ(n) + 6 > 0`. The constructed machine has
  coin length `(q(n)+1)n + D.coinLen n`; its explicit coin equivalence has exactly this domain.
  The encoded advice is bounded by
  `2((q(n)+1)(4n+2ℓ(n)+6)) + 2 + (q(n)+1)`.
  The proof establishes the query at every canonical history with `k < q(n)+1`, and the return
  at `k = q(n)+1`. Its remaining-budget induction therefore avoids malformed moves and timeout.
  The evaluation identity holds for **every oracle**. `exists_oneQuery_nuppt` is the specified
  zero-mask, `q = 0`, precomposition corollary; it does not build another oracle machine.
- **D4:** the maximum ranges over a nonempty finite type of mask pairs, including at zero widths.
  The two chosen mask families are fixed before applying D3. Coin equivalence identifies their
  machine advantages with the concrete adversaries. D1 at budget `q + 1` and the existing
  collision-negligibility lemma give **one negligible bound preceding all `n,w,w'`**.

The 22 old proofs genuinely specialize these results or use their same-file bridges. In particular,
the unchanged `6n+6` definitions are related to `4n+2n+6` without changing their bodies.
The definitions and statements impose no hidden positivity assumption on `n`, `ℓ(n)` or `q(n)`.

## B1 consumer map and Gate 27 hand-off

The map is correct against the merged `SpecialEncryptionMulti` and the actual `spEncStr` definition.
For a fitting slice, set

\[
w_i=0^{o_i+n}\,\Vert\,m_i\,\Vert\,0^{\ell(n)-o_i-n-\ell_i}.
\]

For each full pad `p` of length `ℓ(n)`, bitwise XOR and the fit condition give

\[
\operatorname{take}_{n+\ell_i}\operatorname{drop}_{o_i}(w_i\oplus p)
=p[o_i:o_i+n]\,\Vert\,
\bigl(m_i\oplus p[o_i+n:o_i+n+\ell_i]\bigr).
\]

Thus applying the report's slice post-processor `P` inside `encodeList` makes
`P ∘ encodeTupleOut ∘ prfEncRealOut (G n) w` equal to `sliceMultiEncDist G n q o len m`
**seed by seed**, on the same key/nonce seed type. This conclusion comes from the definitions;
the consumer probe's tautological seed-type example does not prove it.

To obtain B1's uniformity, choose a maximizing fitting slice/message pair at each parameter,
use value zero when none fits, and put the slices in polynomial-length advice of `D' = D ∘ P`.
D4 then bounds the corresponding full masks. Its factor-two collision bound is sufficient for
B1's qualitative negligible conclusion. `hG.pseudorandom` is literally D1/D4's hypothesis.

D3 supplies the required arbitrary-oracle identity and coins; the advice and query bounds remain
inside the NUPPT construction, as disclosed. The non-adaptive uniform query chain suffices here.
The one-query result similarly supplies the oracle reduction for `spDecStr_wrongKey`; the
independent-key distinguisher and random-function `2^{-n}` calculation remain consumer work.

The `sc-garble` brief must retain the sampler identity, polynomial-time slice post-processor,
fit/mask construction, maximizing advice with the empty-set convention, random-function slice
law, triangle bound, frozen corollary and B2 obligations. This audit does not discharge those
future Lean proofs.

## Duplication, seals and landing edits

I searched the pinned TCSlib sources and the pinned Mathlib list material, including probability,
expectation, relabelling, list-block and XOR identities inside the new proofs. **No undisclosed
re-proof or private copy beyond DL-46 was found.** D2/D4 reuse the published coupling and
advantage-equivalence lemmas; they do not reproduce `prfAdv_eq_expect`. The width-free block/XOR
helpers are reused. T2/T4 would replace the retained chain construction, rather than provide a
missing width generalization; the existing width-transport lemmas are unnecessary here.

DL-46's third `encodeList_eq_flatMap` copy, retained `histBlockLen`, and unused frozen items are
accurately disclosed. The public/private same-name clash explains why importing `BlockEncryptor`
is not an available frozen-preserving repair; the one-error clash transcript is consistent with
the declarations. The GGM and tableau-emitter relatives have the recorded different interfaces.
The authorized deferred cleanup remains appropriate.

All **44** base/head seal probes reconstruct the exact source by removing only their recorded
insertions. Their source/probe/log hashes and install/EOF verification counts agree. All **24**
head request sets equal the collector's eligible full-closure definitions, including matchers;
six import closures were independently reconstructed from source. All 321 stored constants'
foreign-definition references are covered by those requests or the permitted exclusions.

Canonical **A passes 6/6 head files and 5/5 base files**, in both strict and coe harnesses.
Strict and coe agree. Both sets of paired controls have their expected sealed failures and
unsealed successes; all **28 raw control logs** verify. The explicit-read scan reports zero
foreign definitions. Reading the raw B errors, including the three `OTHER` blocks, supports
the `PolyExpr.eval`/cascade attribution; it does not support the inaccurate base-only wording
identified in G31-01.

LE-doc changes only the three specified docstrings, whose formulas and argument order are correct.
LE-ws restores exactly one blank line. Neither changes a declaration or proof.

## Integration

Merged #314 changes two different paths and introduces a different name,
`TCSlib.Cryptography.prfAdv_eq_expect`. Its new upstream import does not create a dependency
cycle with D1–D4. I found no concrete name, instance or source interaction preventing integration.
The supplied clean merge-tree evidence is consistent with these disjoint changes.

At the pack's #313 head `8befc58966fd39f974a54250849736df194584b9`, learning consumes the unchanged
headers of `exists_queryChain_nuppt`, `histBlockLen`, `eval_histBlockLen`, `flatMap_range_blocks`
and `abs_uexp_sub_le_uprob`. No interface break was found. Neither combined tree is claimed built
by this report. The #314 downstream integration run belongs to the maintainer before merge.

## Reproduction

The accompanying ZIP contains this Markdown, the official pack, verified source snapshots and Git
inventories, and `evidence/verify_gate31.py` with its results. From the extracted ZIP, run:

```sh
python3 evidence/verify_gate31.py inputs rechecked
```

The script checks hashes, Git object provenance, the frozen rule and controls, the byte-identical
patch, build-log binding, seal instrumentation/coverage, the census and control logs. Its exact
small models check 1,275 history/mask cases and 8,403 slice cases; these supplement source proof
inspection and are not presented as formal proofs.

**Notation:** `ℓ(n)` and `q(n)` mean polynomial evaluation; `ℓ_i` is a slice's message length;
`w_i` is its full-width mask; `p` is a full-width pad; `P` is the slice post-processor;
`D'` is the composed distinguisher; `⊕` is bitwise XOR; `‖` is concatenation;
`p[a:b]` is the half-open slice from bit `a` to bit `b`.
