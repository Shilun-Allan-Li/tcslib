# Gate 03b, round 2: external findings

**DO NOT CLOSE: 0 blockers, 1 major, 2 minors.** The canonical-decoding repair resolves round 1's major. A different, newly added docstring claim about `ofString` is false for the implemented padding operation (R2-1).

Audited the supplied round 2 bundle at `e79397eaf68b156b9db091f464741f6eb75b9c28`, following `03b-pack-r2.md` and the applicable common statement-audit brief. Date: 2026-11-05. Lean line numbers below refer to the supplied files; paths beginning `Asymptotic/` or `Candidates/` are under `TCSlib/Cryptography/`.

The attached [PS10] PDF was available and checked directly; book page = PDF page − 12. This was a statement, semantics, docstring and resolution audit, not a tactic-proof audit or independent Lean replay. Section B of the repair diff supplies context for the candidate and public-key repairs. Prong B's repaired OT code, the full candidate files, `OneWayYao.lean`, `QUEUE.md`, the gate-06 plan and the underlying combined replay are not included; their reported external status is distinguished from independently checked content below.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | **major** | `Asymptotic/OneWay.lean:198–206` · `FunFamily.ofString` docstring, added in section A | The new example claims that, for a length-preserving one-way `g`, defining `f(0^k ‖ w) = w` for `length w = k` and `f = g` elsewhere yields typed inversion probability at most inversion probability against `g` plus `2^{-n/2}`. This overlooks the false-padding performed by `ofString`. | Take a length-preserving strong OWF `h` and define, at length `n`, `g(x) = h(x.take ⌈n/2⌉) ‖ 0^{⌊n/2⌋}`. This `g` is length-preserving and one-way. Set `p = .var` and use the displayed definition of `f`. At every even length `2k`, every output of `ofString f .var` is `v ‖ 0^k`, and the efficient, correctly sized answer `0^k ‖ v` is a preimage. Success is **1**, while every efficient inverter of `g` has negligible success. The derivation below shows the collision explicitly. | Remove the unsupported example/bound, or identify it explicitly as a claim about a different, raw-output typed experiment. To retain an example for the actual implementation, specify `p = .var` and additionally choose `g` whose nonempty outputs end in `1`; this prevents shortened special outputs, padded with zeros, from colliding with ordinary outputs. No change to `ofString` itself is necessary. |
| R2-2 | minor | `Asymptotic/OneWay.lean:180–182` · `WorstCaseOneWayLit` docstring | After correctly restricting `toParam` to nonconstant output length, the revised paragraph still concludes that the two forms coincide “for every family of the text.” This is overbroad. | [PS10, Def. 26.1, book pp. 26–27 / PDF pp. 38–39] imposes no nonconstant-output restriction. For `f(x) = []`, `inLen = .var`, `outLen = .const 0`, the parameter-aware machine outputs `0^n`, so `WorstCaseOneWay` is false. A literal machine sees the same empty argument at parameter 0 at every input length and cannot always return both a length-0 and a length-1 preimage; `WorstCaseOneWayLit` is true. This is also the preceding paragraph's own example. | Replace the final universal phrase with “for families with nonconstant `outLen`,” or delete it. Keep the correct constant-length warning and the unchanged bridge statements. |
| R2-3 | minor | `resolutions-03b-r1.md:52` · M6 | The resolution says the current duplication ledger calls the `GGMRed` copy private. The supplied ledger already calls it public. | `duplication-ledger.md:42`, DL-15, explicitly lists a private copy in `Collections.lean`, a **public** `GGMRed.decodeFin_eq_some_iff`, the new forward lemma, and the namespace-clash constraint. The deferral is valid; this description of its current record is stale. | Delete or update that sentence in M6. Retain the approved DL-15 schedule; no immediate deduplication is requested. |

R2-1 is major because the trusted prose asserts an invalid hardness-preservation bound, not merely an imprecise name or a finite-parameter exception. It is not a blocker: no supplied theorem statement uses this example or bound.

## R2-1: counterexample calculation

This is conditional on the same existence assumption as the docstring: let `h` be a length-preserving strong one-way function. For a string `x` of length `n`, put

\[
g(x)=h\bigl(x.\mathrm{take}\lceil n/2\rceil\bigr)
      \mathbin\Vert 0^{\lfloor n/2\rfloor}.
\]

Then `g` is polynomial-time and length-preserving. It is one-way: at lengths `n = 2k` and `n = 2k−1`, its challenge distribution is respectively `h(U_k) ‖ 0^k` and `h(U_k) ‖ 0^{k−1}`. Given a challenge for `h`, either distribution can be generated efficiently; the first `k` bits of any valid inverse for `g` invert that challenge. These are two polynomial-time reductions, with advice and coins at `n = O(k)`. Their negligible bounds imply a negligible bound for every inverter of `g`.

Define `f` exactly as in the disputed docstring. Write `\widehat f_n` for the string-valued output of `ofString f .var` at length `n`. For `n = 2k`, `k ≥ 1`, and `a,b ∈ {0,1}^k`, the implementation at line 210 gives

\[
f(a\Vert b)=
\begin{cases}
b,&a=0^k,\\
h(a)\Vert0^k,&a\ne0^k,
\end{cases}
\qquad
\widehat f_{2k}(a\Vert b)=
\begin{cases}
b\Vert0^k,&a=0^k,\\
h(a)\Vert0^k,&a\ne0^k.
\end{cases}
\]

Thus every challenge is `v ‖ 0^k`. Define the inverter, at even parameter `2k`, by

\[
A(1^{2k},v\Vert0^k)=0^k\Vert v.
\]

Its answer has exactly `2k` bits, so the typed decoder accepts it, and

\[
\widehat f_{2k}\bigl(A(1^{2k},v\Vert0^k)\bigr)
=\widehat f_{2k}(0^k\Vert v)
=v\Vert0^k.
\]

Consequently the implemented inversion probability is `1` at every positive even length. Against `g` itself, the same inverter succeeds precisely when `h(U_k) = h(0^k)`. That probability is negligible: it is the success probability of the efficient inverter of `h` that always returns `0^k`. In particular, for all sufficiently large `k`,

\[
1>\Pr[h(U_k)=h(0^k)]+2^{-k},
\]

contradicting the asserted bound. Interpreting the bound as involving some other efficient reduction does not help, since `g` is one-way.

The proposed normalization is available under the same assumption: define `g(x ‖ b) = h(x) ‖ 1` on nonempty inputs. This remains length-preserving and one-way. At even positive input lengths, the special branch of `f` pads to a string ending in `0`, whereas the ordinary branch ends in `1`. Successful inversions of ordinary-branch challenges must therefore use ordinary-branch preimages. The exceptional input fraction is exactly `2^{-n/2}`, yielding the intended bound; at odd lengths the special branch is absent. This is a mathematical repair suggestion, not a newly formalized lemma.

## Round 1 resolution dispositions

Each label below is a row of `resolutions-03b-r1.md`. “Recorded” does not certify execution of absent external code.

- **1: fixed** — `encD_decD` rules out alias strings at every index; the derived evaluator, sampler and inverter equalities close the original interface gap. Section B also supplies the predicate-evaluator bridge. Removal of prong B's redundant `hcanon`/`hspec` remains scheduled for gate 06, as declared.
- **2: fixed** — the requested `LengthRegular` provisos are present in D5, the module docstring and `FunFamily`. The separate, later addition to `ofString` from #201 introduces R2-1; the original three provisos are not missing.
- **3: fixed** — `OneWayPermutation` now cites §2.10 / Def. 55.1 and identifies the single-function form; the collection hard-core consumer lists agree and omit Thm. 126.4. Direct PDF checks support these corrections.
- **4: fixed** — the collection sketch now describes `padStr` and `collInvRaw` without a length check. The amplification sketch uses the actual `exists_yaoReduction` call, the reduced advice layout and the total `yaoB` interface. Its internal sub-machine implementation remains pack 03h's scope.
- **5: fixed** — `PermCollection` explicitly records the stronger all-index obligation and the singleton-domain treatment of junk indices.
- **6: fixed** — both the docstring and DESIGN give the general index-in-trapdoor encoding argument, not only the candidate examples.
- **7: scheduled** — the enhanced-hard-core obligation is assigned to gate 06B. The reported prong-B repair commit is identified, but its source is absent here. Canonical decoding alone does not remove the known-coins attack.
- **8: fixed** — DESIGN §5.23 records the parameter-`n` reading, the changed repetition count and threshold, and the statistical margin. The optional bridge to a single string OWF remains explicitly unformalized/deferred.
- **9: not resolved** — the revised constant-output warning and parity example are correct, but the same paragraph retains the false universal conclusion in R2-2.
- **10: fixed** — all three `Permutations.lean` occurrences now restrict the upper bound to `n ≥ 1`; no sampler statement changed.
- **11: recorded** — `ArithmeticFP` remains the same nine-operation hypothesis bundle, not a new axiom or a proved machine instance. No repair was required.
- **12a: recorded** — the resolution records G3-6's approval; the files contain exactly the same 15 `@[simp]` attributes, with none added by the repair. The underlying `QUEUE.md` ruling is not bundled.
- **12b: fixed** — the machine and string helpers moved to `CollectionsHelpers.lean`, with names preserved and an import from `Collections.lean`.
- **12c: scheduled** — the copies remain, as permitted by G3-5, and are covered by DL-10/DL-15 and the named gate-03 cleanup. The new forward decoder lemma is included in DL-15.
- **12d: fixed** — the split is present; `Collections.lean` is 982 lines and `CollectionsHelpers.lean` is 198 lines.
- **13: fixed** — all three requested identity exclusions, the common success-probability lemma and `eval_inv` are present and included in the supplied standard-axiom prints.
- **14: recorded** — the maintainer's review records the canonical default-pair check; section B shows the new field supplied through `encodeDistinctPrimes_of_decode`. The full sampler/default implementation is not reproduced, so its detailed recheck belongs to 03f2.
- **M1: scheduled** — same gate-06B obligation as row 7; the external implementation claim is recorded, not independently verified in this bundle.
- **M2: fixed** — section B derives `PredEvaluator` from `HardCore`, adds the evaluator-free existence corollary, and states the remaining `henc` restriction and its candidate cost. It no longer claims the unrestricted TDP-to-PKE implication from the collection interface alone.
- **M3: recorded** — the problematic lenient-decoder alternative was not adopted; the canonical field is the chosen repair.
- **M4: recorded** — the corrected source location is Def. 41.1(2) and Def. 56.1(6). Def. 41.1(3) specifies evaluation on domain elements and was not itself the missing representation guarantee.
- **M5: recorded** — the `fUniversal` use is an unchanged, explicitly identified check for 03h. Its complete reduction is absent here; this report does not certify it or generalize it to arbitrary `ofString` inputs.
- **M6: not resolved** — the DL-15 deferral is adequate, but its description of the current ledger needs the small correction in R2-3.
- **M7: fixed** — the final split preserves the helper names/import path and accommodates the field without crossing 1000 lines.
- **M8: fixed** — direct PDF checks confirm the printed repetition count/threshold, §2.10–§2.12 attribution, and that `(33.2)` is an equation rather than a numbered “Remark 33.2.”

## Every new public declaration

These are restatements of the formal signatures, with the docstring comparison. All 15 declarations listed by the round 2 pack are covered.

| Declaration | Mathematical meaning and docstring verdict |
|---|---|
| `Collection.encD_decD` (`Collections.lean:147`) | If a word decodes to a domain element, encoding that element recovers the original word. Together with `decD_encD`, the decoder accepts exactly the image of the encoder. **Matches.** This is a field, not an independently assumed theorem about every decoder. |
| `Collection.decD_eq_some_iff` (:258) | Decoding a word to `x` is equivalent to that word being `encD i x`. **Matches**, at every index. |
| `Collection.apply_of_decD` (:265) | Any function on encoded index/word pairs agreeing with a specified value on encodings has that value on every word decoding to the same element. **Matches**; the codomain is arbitrary and no efficiency assumption is needed for this equality. |
| `Collection.eval_of_decD` (:273) | A successfully decoded word is evaluated as the corresponding abstract domain element. **Matches.** |
| `Collection.sample_eq_encD` (:280) | At every generated index and for every sampler coin tape, the sample is an encoding of some domain element. **Matches**; it asserts membership, not uniformity. |
| `Collection.HardCore.evaluator` (:289) | A hard-core predicate has one polynomial-time evaluator correct on every decodable word, uniformly across indices. **Matches**; existence follows from its existing efficiency clause and canonicity. |
| `TrapdoorCollection.inv_eq_encD` (:362) | For every generated index/trapdoor, domain target and inverter tape, inversion returns exactly the encoding of the inverse permutation value. **Matches**; no one-wayness assumption is needed. |
| `TrapdoorCollection.eval_inv` (:373) | Evaluating the inverter's returned word recovers exactly the target's encoding. **Matches** and supplies the missing string-level sanity statement. |
| `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean:189`) | Successful exact-width bit-vector decoding means the original word is exactly `List.ofFn` of the decoded vector. **Matches**, including width zero. |
| `natToList_length_listToNat` (`Arithmetic.lean:157`) | Reading a binary word as a natural and rewriting it at its original width returns the same word, including leading zeros. **Matches.** |
| `natToList_val_natCast` (:165) | A width-`k` word whose value is below `M` is unchanged by casting that value into `ZMod M`, taking its representative and rewriting at width `k`. **Matches**; the strict bound excludes modulus zero. |
| `FunFamily.invProbAt_ofString_id_eq_one` (`OneWay.lean:836`) | Any machine returning its argument on every activation inverts the typed identity with probability one at every parameter. **Matches**, including parameter zero and arbitrary advice/coins satisfying the hypothesis. |
| `not_weakOneWay_id` (:870) | The typed identity fails weak one-wayness. **Matches**: success one exceeds `1 − 1/q(n)` for every positive `q(n)`. |
| `not_worstCaseOneWay_id` (:887) | The typed identity fails the parameter-aware worst-case notion. **Matches**: one efficient machine inverts every input on every tape. |
| `FunFamily.not_toCollection_oneWay_id` (`Collections.lean:545`) | For every polynomial-time evaluator correctly implementing the identity family, its `toCollection` instance fails collection one-wayness. **Matches**: project the challenge's second component. The evaluator assumptions are inhabited, for example by `pairSndD`. |

## Remaining changed surface and regressions

The section-A hunks match the supplied final files. Existing declarations retain their statements, apart from the added `Collection` field; the negative strong-identity witness retains its statement and now uses the shared probability lemma. The helper relocation preserves namespaces and signatures.

| Surface | Check |
|---|---|
| Moved `NUPPT.withIndexParam`, `coins_withIndexParam`, `withIndexParam_runAt` | The wrapper prepends `1^n` as the argument's index and preserves advice and coins; the activation and coin equations say precisely this. No semantic change. |
| Moved `NUPPT.length_runAt_le`, `runLenPoly`, `eval_runLenPoly`, `length_runAt_le_runLenPoly` | The output bound is `Ct·(8n + 14 + 4·length y + 2·adv(n) + coins(n) + 1)^ct`; substituting a polynomial bound for `length y` gives the stated polynomial. No semantic change. |
| Moved `splitCoins` and its three `ofFn_splitCoins_*` lemmas | The bijection splits an `a+b`-bit tape into its first `a` and last `b` bits, and its inverse concatenates. Statements/docstrings agree, also when either block is empty. |
| Moved `Collection.ofFn_padFin_of_le`, `padFin_append_true_injective` | Short-word padding appends zeros; appending a `true` marker before padding is injective under both strict length bounds. Statements/docstrings agree. This lossless construction is distinct from the problematic unmarked padding in R2-1. |
| `Collection`, `HardCore`, `toCollection`, `TrapdoorCollection`, `inv_preimage` docstrings | The canonical-word consequences and the remaining generated-index restrictions are accurately stated. `sample_spec`'s evaluator conjunct is now redundant but consistent. The old decode-level sanity result is preserved. |
| `owfFamily_strongOneWay` sketch | `padStr`, the drop-only reduction, the successful-answer implication and the sampled-to-ideal statistical loss agree with the included definitions/contracts. An unsuccessful wrong-length answer requires no extra machine-side check. |
| `weak_to_strong` sketch | The top-level reduction call and probability comparison match the included statements, including `T+1` rounds and subtraction of `(T+1)·2^{-n}` for positive parameters. The source's differing constants are declared. The old, incompatible advice layout has been removed. |
| `not_strongOneWay_id` sketch; module result lists | The refactor uses the new shared success-one lemma; the listed new declarations exist. No strengthened or weakened theorem statement was introduced. |
| `OneWay` representation prose | The length-regularity provisos are correct. Exceptions are the new false-padding example (R2-1) and the residual universal literal/parameter equivalence claim (R2-2). |
| `Permutations` and `Arithmetic` prose | The three positive-parameter qualifications and both numeral-canonicality descriptions agree with the formal statements. No arithmetic-efficiency field changed. |

Section B records a canonical-decoder obligation for every listed ch. 2–4 constructor: `toCollection`, `glPad`, exponentiation, factoring, RSA, Rabin and Blum. Its new candidate lemmas assert the right encoder-after-decoder equalities; their complete instance audits remain 03f1/03f2/03i. The public-key additions derive an evaluator and retain `henc`. The `henc` restriction is acknowledged, not claimed discharged for the candidates.

## Adversarial instantiations

1. **Alias strings, round 1's attack.** Let the encoding be `false :: encD₀ x` and let both prefixes decode to `x`. At `true :: encD₀ x`, the new field would require `false :: encD₀ x = true :: encD₀ x`, impossible by head-bit inequality. The sampler and trapdoor-inverter variants of that attack cannot instantiate the repaired structure. **Repair passes.**

2. **An inverter returning a wrong or noncanonical word.** `inv_spec` first forces its output to decode to the inverse permutation value; `encD_decD` then forces the exact encoding. Applying `eval_spec` and the permutation equation gives `eval(Inv(y)) = encD(y)`. Applying the same canonical-word equality to the hard-core evaluator gives its correct predicate bit. Neither a malformed word nor an alias can pass the fields. **Repair passes.**

3. **Empty tapes, singleton domains and numeral boundaries.** `Fin 0 → Bool` has one element, not none, so the identity's success is still one at `n=0`. A singleton collection with encoding `[]`, decoder accepting exactly `[]`, constant sampler and identity permutation satisfies the canonical interface and is easily invertible; the interface is not made inconsistent. The numeral round trip sends `[]` to `[]` and `[false,false,true]` back to that same three-bit word. `natToList_val_natCast` at `M=0` has an impossible strict-bound premise, while at `M=1` it correctly preserves any all-zero word of the specified width. **No vacuity or boundary defect found.**

4. **False-padding collisions.** The construction and exact equations in R2-1 give success one at every even length despite the stipulated hardness of the base family. The algebraic attack identity was also enumerated for every map on one- and two-bit halves (4,112 cases); that finite check corroborates the identity, not the cryptographic hardness assumption. **New defect found.**

5. **Constant-output literal inversion.** The empty-output family separates the two worst-case predicates exactly as shown in R2-2. **The warning is repaired, but its final universal conclusion is not.**

6. **Known sampler coins.** Replacing a sampler by its permutation image preserves canonicality and ideal-distribution one-wayness/hard-core hypotheses. Its coins still reveal the preimage used to produce that image. The new field therefore does not establish enhanced hard-core security. **The separate gate-06B obligation is necessary and remains separately scheduled.**

## Source and inventory checks

The inventory file itself is not attached; the following covers its labels reproduced in pack 03b and round 1's findings. Statements outside the changed surface are assessed here only for the repair's effect.

| Source item | Round 2 assessment |
|---|---|
| Def. 26.1, pp. 26–27 | The two declared parameter/literal variants and their conditional bridges remain unchanged. The overbroad docstring conclusion is R2-2. |
| Def. 27.3, pp. 27–28 | The declared same-length-preimage restriction remains. Exact correspondence for length-regular, nonconstant output length is correct; the new nonregular example is R2-1. |
| Def. 28.4, p. 28 | The existential positive polynomial and subsequent universal adversary quantifier are unchanged; the new identity exclusion tests them correctly. |
| Thms. 35.1 and 35.2, p. 35 | No statement change; the family/parameter reading is recorded in §5.23. The revised amplification sketch addresses the reported mismatch. |
| Claim-38.2 / §2.4.3, pp. 38–39 | The PDF has `m = 2nq(n)`, `2nm²p(n)` repetitions and threshold `1/(2m²p(n))`. The different formal parameters and sampling margin are explicitly registered. |
| Rem-33.2, p. 33 | The primality statement is unnumbered prose; `(33.2)` labels an equation. `ArithmeticFP` correctly cites the page/section rather than inventing a numbered remark. |
| Def. 41.1, p. 41 | The repair supplies actual encoded domain elements for clause (2), preserving clause (3). Approximate rather than exact domain sampling remains the declared D10 deviation. |
| Thm. 42.2, p. 42 | Both formal directions retain their statements in the campaign's function-family setting. Canonicality preserves the earlier sample/evaluation guarantee; no new single-string bridge is claimed proved. |
| Def. 55.1, p. 55 | Correct §2.10 attribution. The all-index permutation condition is explicitly stronger than the source's valid-index condition. |
| Def. 56.1, p. 56 | The new equalities supply the string-level correctness required by clause (6). Packing the index into the trapdoor addresses the declared trapdoor-layout difference. |
| Def. 78.3 collection form; Lem. 84.1; Alg. 104.3 / Thm. 104.4 | Canonical decoding makes the existing efficient hard-core evaluator usable on honest produced words. The corrected consumer list is appropriate; the additional `henc` cost is stated. |
| Thms. 79.4 and 126.4 | The source uses the single-permutation form; the corrected `OneWayPermutation` attribution and removal of 126.4 from collection-hard-core consumers agree. |

## Evidence checks

- Bundle: **19 sections**, SHA-256 `1db137f935655cb9a172f6564f750614c59a979f4738ed0c622319d0b9f970c0`. The extracted round 1 findings match the stated SHA-256 `0d3a1f038c63a13cfc0f7484832049d5559790e84f6d19935a2241716b01bbb6`.
- Source PDF: SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Text extraction and visual checks of the relevant formula/definition pages agree.
- Every section-A diff hunk matches the corresponding supplied final file. The new helper file and the four existing files have respectively 198, 982 (`Collections`), 923 (`OneWay`), 512 (`Permutations`) and 361 (`Arithmetic`) lines.
- `replay.log` lists **66** distinct module checks, all `rc=0`, `errors=0`; its warning counts sum to **17**, all outside the five audited files. These are supplied execution records, not checks rerun by this auditor.
- The five files contain **111 public theorem/lemma declarations**; the supplied axiom log has **111 corresponding entries**, all restricted to `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. The new public lemmas are included. A comment-stripped scan found no `sorry`, `admit` or axiom declaration in these five files.
- The supplied lint result is **0 findings in 5 files**. The 15 approved `@[simp]` attributes are preserved. These mechanical results do not validate docstring mathematics, so they do not resolve R2-1 or R2-2.

**Closing condition:** repair R2-1's prose claim and recheck that replacement. R2-2 and R2-3 are nonblocking corrections. The canonical collection field and its derived API need no further change on the evidence reviewed here.

## Notation

`h`: hypothetical length-preserving strong OWF used in the counterexample; `g`: the constructed length-preserving base function; `f`: the docstring's special-branch function; `\widehat f_n`: the padded string output of `ofString f .var` at parameter `n`; `A`: the explicit inverter; `U_k`: a uniform `k`-bit string; `k`: half an even input length; `a,b,v`: `k`-bit strings (the final repair suggestion also uses `b` for a final bit); `0^k`, `1^n`: repeated zero/one bits; `‖`: string concatenation; `[]`: the empty string. Other names and parameters are those of the supplied declarations.
