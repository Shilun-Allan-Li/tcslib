# Pass–shelat Gate 22 — ext-nosrc

**Verdict: CLEAR at the audited head.**

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |

No new finding. The gate meets the pack's zero-blocker, zero-major closure criterion.
This conclusion includes source review and independent evidence verification; Lean was **not** rerun locally.

| Pin | Audited value |
|---|---|
| Repository / draft PR | [Shilun-Allan-Li/tcslib #303](https://github.com/Shilun-Allan-Li/tcslib/pull/303) |
| Lean head | `e99a6055ff6b24cdf4b25993e83d045bd569028f` |
| Lean tree | `962374efbcb153c8f696b96f74aae0cab4a2baff` |
| Comparison base | `ba0adb6b1a69787805340d06cb5ce9216b6277a0` |
| Campaign records | `1d109ff037d12cc6520ba0fb7826e320da348d73` |
| Exchange | `7e84141907941e0d684942f370f9830eaeb555e5` |

The live PR head matched the requested pin when inspected. Scope: the proof of
`Randomness.not_isExtractor_effSources` [PS10, Theorem 183.6], its two helpers, the approved
facade imports, and the pack's stated evidence and documentation obligations.

## Integrity and frozen surface

Read the pinned `README.md`, `pack.md` and all 11 sections of `bundle.md`. Independently checked:

| Material | Result |
|---|---|
| Gate `SHA256SUMS` | 15/15 hashes match; exact file coverage apart from the manifest itself |
| `verification.zip` manifest | 42/42 hashes match; archive contains precisely those entries plus its manifest |
| Nested review / LE-doc archives | 352/352 and 53/53 hashes match; exact archive/manifest coverage |
| Original worker delivery at `a5da5cc3…` | Payload 846/846; evidence 837/837; exact manifest coverage |
| Bundle / source closure | All 11 sections agree with their pinned repository sources; all 203 source files agree with the head |
| Patch replay | All three worker patches apply; all four resulting files equal the delivered `src/` bytes |

The independent Git diff reproduces the packaged diff: four paths, 949 insertions and six
deletions. The five-commit range contains no other change. The issue-base-to-comparison-base
delta contains records only.

All eight pre-existing declaration headers in `Extraction.lean`, including the target, are
byte-identical. No frozen statement, global simp attribute or unrelated provider changed.
LE-width changes whitespace only. Between `653d6c1b…` and the head, removing docstrings makes
the sources byte-identical; all 81 written declaration headers agree, and exactly 44
docstrings change. The target's docstring is untouched by LE-doc.

## Proof against the frozen theorem

The delivered proof establishes the stated contradiction for every natural-number width.
Its use of a sampler chosen **after fixing the width** agrees with the frozen definition of
`effSources`: the source condition is required at that width. The constructed machine has
empty advice at every activation parameter and a constant coin polynomial; both properties
are supplied by the published `NUPPT.ofPolyTimeUniform` interface.

Here is the checked argument. Fix `n` and suppose the asserted extractor property holds. Set

\[
D(x)=(\operatorname{Ext}(\operatorname{List.ofFn}x)).\operatorname{headD}(\mathrm{false}),
\qquad q=\Pr[D(U_n)=\mathrm{true}],\qquad S=\{x:D(x)=\mathrm{true}\}.
\]

1. `uniform_mem_effSources` supplies the uniform source. The extractor bound and
   `uniform_one_probTrue` give
   \[
   |q-\tfrac12|\le\tfrac14\quad\Longrightarrow\quad q\ge\tfrac14>0.
   \]

2. Write \(L_t=\operatorname{Rejection.law}D\,t\). The selector returns the first accepted
   point among `t` trials, or an independent fallback. Its point recurrence is
   \[
   L_0(x)=2^{-n},\qquad
   L_{t+1}(x)=\mathbf1_{D(x)=\mathrm{true}}2^{-n}+(1-q)L_t(x).
   \]
   Induction gives the proved mixture identity
   \[
   L_t=(1-q)^tU_n+\bigl(1-(1-q)^t\bigr)\operatorname{flat}(S).
   \]
   The accepted flat component satisfies, at every point,
   \[
   \operatorname{flat}(S)(x)\le\frac{2^{-n}}q
   \le4\,2^{-n}=2^{-(n-2)}.
   \]
   The uniform component has the same upper bound. `mixture_isSource` therefore supplies
   the required source property for `L_10`.

3. `chooseWord_poly` constructs the bounded string selector from published prefix, drop,
   head-bit and conditional combinators. `coinEquiv`, `FunFamily.blocks`,
   `chooseWord_blocks` and `samplerLaw_rejection` identify the machine's uniform `11n`
   coins with eleven independent uniform blocks and identify its output law with `L_10`.
   Thus `rejection_mem_effSources` supplies the efficient source used in the contradiction.

4. The acceptance recurrence and its solution are
   \[
   \Pr[D(L_{t+1})=\mathrm{true}]
   =q+(1-q)\Pr[D(L_t)=\mathrm{true}],\qquad
   \Pr[D(L_t)=\mathrm{true}]=1-(1-q)^{t+1}.
   \]
   Consequently,
   \[
   \Pr[D(L_{10})=\mathrm{true}]
   \ge1-(\tfrac34)^{11}
   =\frac{4017157}{4194304}
   >\frac{3145728}{4194304}=\tfrac34.
   \]
   The extractor bound on this source instead implies
   \(\Pr[D(L_{10})=\mathrm{true}]\le\tfrac34\). The Lean proof uses exactly this contradiction.

The generic rejection-law proof includes zero trials and acceptance probabilities zero and
one. Its flat-law identity requires positive acceptance and divides only by that probability,
never by its complement. The bit-block equivalence also covers `n = 0`. For `n = 0,1,2`,
the entropy subtraction is in the reals and the displayed point bound remains valid.
`extBit_zero` explicitly handles empty extractor outputs by reading `false`. The target sketch
describes the delivered construction and bound accurately.

## Rule 10, facade and documentation

Reconstructed every submitted conservative request set from the collector catalogues and
independently checked its source import closure. Checked 28 base/head/LE-width seal records:
probe hashes, removal of instrumentation to recover source bytes, native-name metadata,
installation records, EOF coverage, raw error counts and source bindings.

The final canonical request counts and outcomes are:

| Owner | Base A / B | Head A / B | Canonical result |
|---|---:|---:|---|
| Extraction | 607 / 608 | 1045 / 1046 | All pass |
| Rejection | New file | 17 / 17 | Both pass |
| Sampler | New file | 1033 / 1034 | Both pass after LE-width |
| Randomness facade | 3364 / 3365 | 3381 / 3382 | All pass |

The coe variant removes exactly `FinDist.instCoeFunForallReal` from the corresponding strict
request sets. Other definition instances remain covered. The strict Rejection runs each
contain 18 source errors in the same 16 declarations; the raw diagnostics concern conversion
between `p a`, `CoeFun.coe p a` and `p.prob a`. The published-reader controls exhibit the
same obstruction. This is covered by the supplied projection-coercion ruling. No additional
forbidden read was identified.

All 12 canonical control probes reconcile with their raw logs: each intended sealed negative
fails exactly once, positives and unsealed controls pass, and there are no stray errors.
The 215-item explicit scan contains no foreign-definition item. I also inspected the
unresolved/local entries; they do not expose another forbidden definition read.

The facade patch is exactly the two approved imports. An independent graph check over 1,236
archived Lean modules finds no cycle; the touched modules' exact source closure contains 203
files. The other facade import lines are preserved.

All 44 LE-doc formulas accurately describe their declarations, with the declarations'
parameters and hypotheses understood. No new documentation finding. Searches and proof
inspection identified no undisclosed copied private lemma or additional duplicate beyond
the recorded dispositions. The worker's detailed `promotion-requests.md`,
`rejection-review.md` and `sampler-review.md` cover the generic helpers, including
`map_apply_expect`, `branch_apply`, the uniform-machine family and `take_poly`; DL-39's
shorter enumeration is not the whole promotion list.

## Validation and limits

The submitted census has 108 stored constants, all using subsets of `propext`,
`Classical.choice` and `Quot.sound`; the target no longer uses `sorryAx`. The issued-module
admission count is 21 → 20, with only the target removed. No new instance, global simp
declaration or handwritten abbreviation was introduced.

Independently matched all 1,201 full-order execution rows to their source hashes at
`653d6c1b…`, with zero recorded errors. The evidence also records 31 PFR modules. The five
final-head rebuilds—Rejection, Sampler, Extraction, the facade and root `TCSlib`—have matching
head-source and raw-log hashes, return code zero, and no admissions. The proved docstring-only
bridge accounts for the earlier seals and census. I independently reran the campaign lint:
the 318 FAIL/WARN lines are byte-identical at base and head (216 FAIL / 102 WARN).

The approved imports, projection coercion, DL-39 debt, disclosed linter warnings,
unreproducible worker commit metadata and frozen review-prose slip remain the pack's known
dispositions; they are not reissued as findings.

**Execution limit:** no local Lean elaboration or independent `.olean` reconstruction was
performed. Compiler, axiom and seal outcomes above use the hash-verified submitted execution
evidence, checked against the audited source and raw logs. Independent work comprised source
proof review, byte checks, patch replay, request-set reconstruction, log reconciliation,
exact rational diagnostics and lint. No source-repository write, dispatch or merge was performed.

**Glossary:** `n` is the input width; `Ext` is the candidate string extractor; `U_n` is the
uniform law on `n`-bit words; `D` reads the extractor's first bit, defaulting to false; `q` is
its uniform acceptance probability; `S` is its accepted set; `t` is the trial count; `L_t` is
the rejection law with `t` trials and one fallback; `flat(S)` is uniform on `S`; `Pr` denotes
probability; the bold indicator is one when its subscripted condition holds and zero otherwise.
