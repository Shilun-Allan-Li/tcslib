## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03b-pack-r3.md =====

# Gate 03b ([PS10] ch. 2–4, one-wayness and collections), round 3: delta audit pack

**What is audited:** the repair of round 2, on `cryptography/pass-shelat-ch2-4` at
`4769fe88d6894a62c87a19bc524088c5a2c99e0b` (the merge of
[Shilun-Allan-Li/tcslib#204](https://github.com/Shilun-Allan-Li/tcslib/pull/204); its Lean files are
#204's head `08fa1185`).
- **Round 2** audited `e79397ea` and found **0 blockers, 1 major, 2 minors**
  (`gate03b-r2-findings.md`, in the bundle, verbatim). Round 1's major (canonical decoding) was
  confirmed fixed there; every other round 1 row was fixed, recorded or scheduled, except #9 and M6,
  which round 2's R2-2 and R2-3 carry.
- **The repair:** #204 changes two docstrings in `TCSlib/Cryptography/Asymptotic/OneWay.lean`; no
  statement changes. R2-3 is a records correction. The diff is `evidence-repairs/03b-r2/repair.diff.txt`;
  the resolutions are `resolutions-03b-r2.md` (both in the bundle).
- **The deliverable:** **`gate03b-r3-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12). Book pp. 26–28 (Defs 26.1, 27.3) are the relevant pages.

## Brief for the auditor

1. **Verify the three round 2 resolutions:** say for each whether it is fixed, or not resolved and
   why.
   - **R2-1 (major).** `FunFamily.ofString`'s docstring now gives the informal example with
     `p = var` and `g(x ‖ b) := h(x) ‖ 1`, and claims a typed-inversion success at most the
     inverter's success against `g` plus `O(2^{-n/2})`. Check that claim against `ofString`'s
     implementation, which pads or truncates `f`'s output to `p(n)` bits with `false`. Check that
     the special outputs cannot collide with ordinary ones, that the text's experiment is still
     inverted with probability one by `y ↦ 0^{|y|} ‖ y`, and that the stated bound holds,
     including at odd lengths and at `k = 0`. Attempt at least one counterexample.
   - **R2-2 (minor).** `WorstCaseOneWayLit`'s docstring: the two forms coincide for families with
     non-constant `outLen`; with constant `outLen` they can differ.
   - **R2-3 (minor).** `resolutions-03b-r1.md`, row M6 (records): the ledger's DL-15 already
     calls the `GGMRed` copy public.
2. **Check that nothing else changed** in `OneWay.lean`: no statement and no other docstring.
   The diff is the whole change.

Pack 03a's severity guide applies. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 2 findings, resolutions, the diff | `findings/gate03b-r2-findings.md`, `resolutions-03b-r2.md`, `evidence-repairs/03b-r2/repair.diff.txt` |
| Under audit | `TCSlib/Cryptography/Asymptotic/OneWay.lean` (the two docstrings), at the pin |
| Context | `resolutions-03b-r1.md` (row M6), `03b-pack-r2.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03b-r2/`)

- **Elaboration** (`replay.log`): `OneWay.lean` and its 42 downstream modules (facades excluded),
  then `audits/pass-shelat/Checks`, each checked alone into a copy of the tree at #203's merge:
  **44 of 44 pass, 0 errors**. The `sorry` warnings are unchanged (61 before, 61 after).
- **Lint** (`lint.log`): `scripts/style_lint.py` on `OneWay.lean`: 0 findings.
- **Axioms:** no statement changed. The round 2 print of `OneWay.lean`'s public theorems stands:
  all standard, none `sorryAx` (`evidence/b2/axioms.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 2 finding: `R2-<n>: fixed / not resolved — <reason>`.

The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03b-r2-findings.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03b-r2.md =====

# Gate 03b (one-wayness and collections): round 2 resolutions

- **Round 2:** findings `findings/gate03b-r2-findings.md`, verbatim, SHA-256
  `924a93b01d6ee976c86f602701dbd67f2e77d908b6a1eed264cd46b3a77fbf2a`; pin
  `e79397eaf68b156b9db091f464741f6eb75b9c28`; bundle SHA-256 `1db137f9…` (19 sections). Verdict
  **DO NOT CLOSE: 0 blockers, 1 major, 2 minors.** Round 1's major (#1, canonical decoding) is
  **fixed**. Round 1's rows are fixed, recorded or scheduled, apart from #9 and M6, which
  R2-2 and R2-3 resolve.
- **Repair:** a docstring-only change to `TCSlib/Cryptography/Asymptotic/OneWay.lean` (PR below),
  checked by the maintainer (the 43 modules downstream of `OneWay.lean` plus `Checks`), and one
  record correction.

| Finding | Severity | Resolution |
|---|---|---|
| R2-1 | major | **Fixed** (maintainer, true: with `p = var` the zero-padded special outputs `w ‖ 0^k` collide with outputs of `g` ending in `0^k`, so the auditor's inverter succeeds with probability one). `FunFamily.ofString`'s docstring example now follows the auditor's repair. It fixes `p = var` and takes `g(x ‖ b) := h(x) ‖ 1`, so every ordinary output ends in `1` and no zero-padded special output can collide with one. The bound is stated as "at most its success against `g` plus `O(2^{-n/2})`", and the example is marked informal and not formalized. The docstring also says why the final `1` matters. No statement changes; `ofString` itself is unchanged. |
| R2-2 | minor | **Fixed.** `WorstCaseOneWayLit`'s docstring now says the two forms coincide "for families with non-constant `outLen`" and that with constant `outLen` they can differ, as its own examples show. This resolves round 1's #9 in full. |
| R2-3 | minor | **Fixed** (records). `resolutions-03b-r1.md` M6 no longer says the ledger calls the `GGMRed` copy private; DL-15 was corrected on 2026-11-05. |

**Round 3** is a delta audit of the two rewritten docstrings (and the record line).

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03b-r2/repair.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic/OneWay.lean b/TCSlib/Cryptography/Asymptotic/OneWay.lean
index d4b35d6f..b2445e44 100644
--- a/TCSlib/Cryptography/Asymptotic/OneWay.lean
+++ b/TCSlib/Cryptography/Asymptotic/OneWay.lean
@@ -178,8 +178,9 @@ typed inverse (the literal adversary cannot know `n`): e.g. the constant family
 `inLen = var`, `outLen = 0` (the adversary cannot know the required output length `inLen n`),
 or `f n b = b ⊕ [n odd]` on one bit (it cannot know the parity of `n`; gate 03b, finding 9).
 The `1^n` form is the headline; `toParam` applies whenever `outLen` is non-constant (for
-`PolyExpr` lengths, injective ⇔ non-constant), so for every family of the text the two forms
-coincide (`toLit`, `toParam`). -/
+`PolyExpr` lengths, injective ⇔ non-constant), so for families with non-constant `outLen` the two
+forms coincide (`toLit`, `toParam`); with constant `outLen` they can differ, as above (gate 03b,
+round 2, R2-2). -/
 structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where
   /-- Easy to compute. -/
   easy : 𝓕.Easy
@@ -199,11 +200,16 @@ Inversion is typed (D5, `NUPPT.inverter`): an inverter of `ofString f p` at para
 return a preimage of length `n`, while [PS10, Definition 27.3] accepts a preimage of any
 length. The two experiments agree when `f` is length-regular with non-constant `p` (then
 `|f(x)|` determines `|x|`); with constant `p` neither notion is satisfiable. Otherwise the typed
-notion can be strictly weaker: for a length-preserving one-way `g`, the function
-`f(0^k ‖ w) := w` (`|w| = k`), `f(x) := g(x)` elsewhere is inverted with probability one by
-`y ↦ 0^{|y|} ‖ y` in the text's experiment, while in the typed one every inverter succeeds
-with probability at most its inversion probability against `g` plus `2^{-n/2}` (gate 03a,
-note 15). -/
+notion can be strictly weaker. An informal example (not formalized; gate 03a, note 15): let `h` be
+a length-preserving one-way function and `g(x ‖ b) := h(x) ‖ 1` on non-empty inputs (again
+length-preserving and one-way, with every output ending in `1`); put `f(0^k ‖ w) := w` for
+`|w| = k ≥ 1` and `f(x) := g(x)` elsewhere, and take `p = var`. In the text's experiment
+`y ↦ 0^{|y|} ‖ y` inverts `f` with probability one. In the typed experiment on `ofString f .var`
+the special outputs are padded with zeros, so they end in `0` and cannot equal an ordinary output;
+an inverter succeeds on an ordinary challenge only by inverting `g`, so its success is at most
+its success against `g` plus `O(2^{-n/2})`. The final `1` matters: without it the zero padding can
+make special outputs collide with ordinary ones, and the typed experiment is then not harder
+(gate 03b, round 2, R2-1). -/
 def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily where
   inLen := .var
   outLen := p

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03b-r2/replay.log =====

# maintainer re-check at 08fa1185903968af42937cfb2532c45c33721d25: OneWay.lean and its 42 downstream modules (downstream2.py, facades excluded), then audits/pass-shelat/Checks, on a copy of the tree at #203's merge (Lean = f29be161)
TCSlib/Cryptography/Asymptotic/OneWay rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 7s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 33s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 19s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Factoring rc=0 3s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 8s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 6s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 3s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 4s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 4s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 3s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 102s errors=0 sorry=0
# done 2026-11-05T23:49:52Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03b-r2/lint.log =====


0 findings in 1 files


## ===== TCSlib/Cryptography/Asymptotic/OneWay.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.OneWayYao
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-way functions, asymptotic layer

The one-way function definitions of [PS10, §2.2] and the hardness amplification theorems of
[PS10, §2.4], stated over the machine layer `Complexity.NUPPT` and the typed concrete
experiments of `TCSlib.Cryptography.Foundations.Experiments` (foundation decisions D2, D3,
D5 of `PassShelatChapter2-4Plan.md`).

A *function family* `FunFamily` is `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with syntactic
polynomial lengths (the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p`, parameter =
input length; exact for length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding to
`p(n)` bits is lossy); `FunFamily.invProbAt 𝓕 A n` is the experiment
`Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y]` for the machine `A`, its output decoded as an
`inLen n`-bit string. The three one-wayness notions of [PS10, Definitions 26.1, 27.3, 28.4]
follow — Definition 26.1 in its `1^n` form `FunFamily.WorstCaseOneWay` (headline) and its
literal form `FunFamily.WorstCaseOneWayLit` (`A(f(x))` only), related by
`WorstCaseOneWay.toLit` and `WorstCaseOneWayLit.toParam` (D5, run-3 audit P3-2) —
then the direct product `FunFamily.prod` with the parameters `yaoBlocks`/`yaoRounds`
(`m = 2nq(n)`, `T = 2nm(n)n^c`) of [PS10, §2.4.3], the theorems `weak_to_strong`
[PS10, Theorem 35.1], `strong_prod_two` [PS10, Theorem 35.2], `claim_38_2` (the parameter
instantiation of the concrete `OneWay.yao_amplification_exp` [Gar26, Theorem 2.1]), the sanity
results `FunFamily.StrongOneWay.weak` and `not_strongOneWay_id`, `not_weakOneWay_id`,
`not_worstCaseOneWay_id` (the adversary classes are not vacuous), and
`PermFamily`/`OneWayPermutation` (the single-function form of [PS10, Definition 55.1], as used
in Theorems 79.4 and 126.4). Every
asymptotic theorem is proved by (i) instantiating the concrete reduction at every `n`,
(ii) exhibiting the reduction as a `Complexity.NUPPT` by the closure calculus of
`TCSlib/Complexity/Randomized/`, (iii) negligible-function arithmetic (`not_negligible_iff`).

**Deviation:** domains are typed at each parameter (D5): the direct product `𝓕.prod q` is the
family at parameter `n` with input length `q(n)·inLen(n)` and its adversaries receive `1^n`
where the text's adversary of `f'` receives `1^{n·m(n)}`; the two are interderivable
(`1^{n·m(n)}` is computed from `1^n` by `polyTimeComputable_unaryPoly`, and `n` is recovered
from `n·m(n)` by a polynomial search, `m` being monotone), so the classes coincide. The
deviations of `Easy`, `invProbAt` and `WeakOneWay` are recorded on the declarations.

## Main definitions

* `TCSlib.Cryptography.FunFamily` (`Easy`, `invProbAt`, `ofString`, `LengthRegular`, `blocks`,
  `prod`); `FunFamily.StrongOneWay`, `FunFamily.WeakOneWay`, `FunFamily.WorstCaseOneWay`
  (`1^n` form, headline) and `FunFamily.WorstCaseOneWayLit` (literal form)
  [PS10, Definitions 27.3, 28.4, 26.1].
* `TCSlib.Cryptography.yaoBlocks`, `yaoRounds` — `m = 2nq(n)`, `T = 2nm(n)n^c` [PS10, §2.4.3].
* `TCSlib.Cryptography.PermFamily`, `TCSlib.Cryptography.OneWayPermutation`.

## Main results

* `TCSlib.Cryptography.weak_to_strong` [PS10, Theorem 35.1], `strong_prod_two`
  [PS10, Theorem 35.2], `claim_38_2` (parameter instantiation, [PS10, §2.4.3]),
  `OneWay.invProb_prodFun_le_yaoTry` (concrete one-call planting, lemma C2 of the inventory).
* `TCSlib.Cryptography.FunFamily.StrongOneWay.weak`, `TCSlib.Cryptography.not_strongOneWay_id`,
  `not_weakOneWay_id`, `not_worstCaseOneWay_id`,
  `TCSlib.Cryptography.FunFamily.invProbAt_ofString_id_eq_one` — sanity and non-vacuity.
* `TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit`,
  `TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam` — the two forms of
  [PS10, Definition 26.1] (always / for injective `outLen`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Function families -/

/-- A family `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with explicit polynomial lengths: the
typed reading (D5) of the textbook `f : {0,1}* → {0,1}*` at security parameter `n`
[PS10, §2.2]. A string function `f` gives the family `ofString f p`, exact for length-regular
`f` (`ofFn_ofString_f`); otherwise the `false`-padding to `p(n)` bits is lossy. -/
structure FunFamily where
  /-- The input length at parameter `n`. -/
  inLen : PolyExpr
  /-- The output length at parameter `n`. -/
  outLen : PolyExpr
  /-- The function at parameter `n`. -/
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily

/-- `𝓕` is *easy to compute*: a polynomial-time string function computes `f n x` from
`⟨1^n, x⟩` [PS10, Definitions 26.1 (1) and 27.3 (1)].

**Deviation:** `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead
of a PPT computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`). -/
def Easy (𝓕 : FunFamily) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)

/-- The inversion probability of the machine `A` against `𝓕` at parameter `n`:
`Pr[x ← {0,1}^{inLen n}; y ← f(x); r : f(A(1^n, y; r)) = y]` with the output of `A` decoded as
an `inLen n`-bit string [PS10, Definitions 27.3 and 28.4, the displayed experiment].

**Deviation:** `inverter`: wrong-length output = failure (D5). -/
noncomputable def invProbAt (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))

/-- `𝓕` is a *strong one-way function*: easy to compute, and every non-uniform PPT inverts it
with negligible probability [PS10, Definition 27.3]. -/
structure StrongOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: negligible inversion probability for every `A`. -/
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n

/-- `𝓕` is a *weak one-way function*: easy to compute, and there is a polynomial `q` such
that every non-uniform PPT inverts it with probability at most `1 - 1/q(n)` for all
sufficiently large `n` [PS10, Definition 28.4].

**Deviation:** `WeakOneWay`: `0 < q n` made explicit (`1 - 1/0 = 1` would make the clause
vacuous). -/
structure WeakOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert with probability `1 - 1/q(n)`. -/
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)

/-- `𝓕` is a *worst-case one-way function*: easy to compute, and no non-uniform PPT inverts
it on every input with probability one [PS10, Definition 26.1], in the `1^n` form: the
adversary receives `1^n` and `f(x)` (`inverter`, D5) and must return an `inLen n`-bit
preimage. This is the headline form of the definition; the literal form (the adversary
receives `f(x)` only) is `WorstCaseOneWayLit`, and the two are related by
`WorstCaseOneWay.toLit` (always) and `WorstCaseOneWayLit.toParam` (injective `outLen`), as
`Ensemble.Indist`/`Ensemble.IndistLit` for [PS10, Definition 69.4].

Repair (run-3 audit P3-2): the frozen headline was the literal form (now `WorstCaseOneWayLit`),
which can be vacuously satisfied by families whose output length does not determine `n` (e.g.
the constant family `x ↦ ε`, trivially invertible in the text); the `1^n`
form is now the headline, mirroring D5's treatment of Definition 69.4.

**Deviation:** the adversary receives `1^n` where the text writes `A(f(x))` (D5; the literal
reading is `WorstCaseOneWayLit`); inverses are sought in the domain at the current parameter
(`inverter`, wrong-length output = failure). -/
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(1^n, f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- `𝓕` is a *worst-case one-way function in the literal form* of [PS10, Definition 26.1]:
easy to compute, and no non-uniform PPT inverts it on every input with probability one, the
adversary receiving `f(x)` only (activation at the output length, `inverterLit`, D5) and
returning an `inLen n`-bit preimage.

Repair (run-3 audit P3-2): renamed from `WorstCaseOneWay`; the `1^n` form `WorstCaseOneWay` is
the headline, and `WorstCaseOneWay.toLit`/`WorstCaseOneWayLit.toParam` relate the two.

**Deviation:** when `outLen` is constant, so that `|f(x)|` does not determine `n`, the literal
form can hold for families that are trivially invertible given `1^n`, an artefact of D5's
typed inverse (the literal adversary cannot know `n`): e.g. the constant family `x ↦ ε` with
`inLen = var`, `outLen = 0` (the adversary cannot know the required output length `inLen n`),
or `f n b = b ⊕ [n odd]` on one bit (it cannot know the parity of `n`; gate 03b, finding 9).
The `1^n` form is the headline; `toParam` applies whenever `outLen` is non-constant (for
`PolyExpr` lengths, injective ⇔ non-constant), so for families with non-constant `outLen` the two
forms coincide (`toLit`, `toParam`); with constant `outLen` they can differ, as above (gate 03b,
round 2, R2-2). -/
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- The output length of a string function on inputs of length `n`, read off at `0^n`. -/
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length

/-- The textbook `f : {0,1}* → {0,1}*` with the output length `p`: parameter = input length,
the output padded or truncated to `p(n)` bits (exact when `f` is `LengthRegular f p`).

Inversion is typed (D5, `NUPPT.inverter`): an inverter of `ofString f p` at parameter `n` must
return a preimage of length `n`, while [PS10, Definition 27.3] accepts a preimage of any
length. The two experiments agree when `f` is length-regular with non-constant `p` (then
`|f(x)|` determines `|x|`); with constant `p` neither notion is satisfiable. Otherwise the typed
notion can be strictly weaker. An informal example (not formalized; gate 03a, note 15): let `h` be
a length-preserving one-way function and `g(x ‖ b) := h(x) ‖ 1` on non-empty inputs (again
length-preserving and one-way, with every output ending in `1`); put `f(0^k ‖ w) := w` for
`|w| = k ≥ 1` and `f(x) := g(x)` elsewhere, and take `p = var`. In the text's experiment
`y ↦ 0^{|y|} ‖ y` inverts `f` with probability one. In the typed experiment on `ofString f .var`
the special outputs are padded with zeros, so they end in `0` and cannot equal an ordinary output;
an inverter succeeds on an ordinary challenge only by inverting `g`, so its success is at most
its success against `g` plus `O(2^{-n/2})`. The final `1` matters: without it the zero padding can
make special outputs collide with ordinary ones, and the typed experiment is then not harder
(gate 03b, round 2, R2-1). -/
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily where
  inLen := .var
  outLen := p
  f _ x i := (f (List.ofFn x)).getD i false

/-- `f` is *length-regular* with output length `p`: `|f x| = p(|x|)` for every `x`. -/
def LengthRegular (f : List Bool → List Bool) (p : PolyExpr) : Prop :=
  ∀ x, (f x).length = p.eval x.length

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation. -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The direct product `f'_n = (f_n)^{q n}` of [PS10, Theorem 35.1]:
`f'(x₁, …, x_{q(n)}) = (f(x₁), …, f(x_{q(n)}))` on blocks, encoded as concatenations;
`OneWay.prodFun` [Gar26, Theorem 2.1] blockwise. -/
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily where
  inLen := .mul q 𝓕.inLen
  outLen := .mul q 𝓕.outLen
  f n x := (blocks (q.eval n) (𝓕.outLen.eval n)).symm
    (TCSlib.Cryptography.OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x))

/-! ### Unfolding lemmas -/

/-- The inversion probability is nonnegative. -/
theorem invProbAt_nonneg (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 0 ≤ 𝓕.invProbAt A n :=
  invProbOpt_nonneg _ _

/-- The inversion probability is at most one. -/
theorem invProbAt_le_one (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 𝓕.invProbAt A n ≤ 1 :=
  invProbOpt_le_one _ _

/-- The inversion probability unfolded: the probability over `x` and the coins `r` that the
activation `A(1^n, f(x); r)` is the encoding of some `x'` with `f(x') = f(x)`. -/
theorem invProbAt_eq_uprob (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) :
    𝓕.invProbAt A n = uprob fun z : (Fin (𝓕.inLen.eval n) → Bool) × A.Coins n =>
      ∃ x', A.runAt n (List.ofFn (𝓕.f n z.1)) z.2 = List.ofFn x' ∧ 𝓕.f n x' = 𝓕.f n z.1 := by
  unfold invProbAt invProbOpt
  congr 1
  funext z
  simp only [NUPPT.inverter_eq_some_iff]

/-! ### The two forms of Definition 26.1 -/

/-- **The `1^n` form implies the literal form** of [PS10, Definition 26.1] (repair of the
run-3 audit, P3-2; the analogue of `Ensemble.Indist.toLit`): a literal inverter `A`, activated at
the output length `|f(x)| = outLen n`, is the `1^n`-inverter `NUPPT.exists_reparam A outLen`,
so if no `1^n`-inverter succeeds on every input, no literal inverter does.

**Proof sketch.** `NUPPT.exists_reparam A 𝓕.outLen` gives `B` with
`B.runAtL n y r = A.runAtL (outLen n) y r` and `B.coins = A.coins.subst outLen`, so
`B.Coins n ≃ A.Coins (outLen n)` (`PolyExpr.eval_subst`, `finCongr`); `uprob_comp_equiv`
transports the success event, and `NUPPT.inverter`/`NUPPT.inverterLit` unfold to the same
`decodeFin` of the same activation (`List.ofFn_congr`). -/
theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit := by
  refine ⟨h.easy, ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨B, hBc, -, hB⟩ := A.exists_reparam 𝓕.outLen
  refine h.hard ⟨B, fun n x => ?_⟩
  have hlen : B.coinLen n = A.coinLen (𝓕.outLen.eval n) := by
    simp only [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
  let e : A.Coins (𝓕.outLen.eval n) ≃ B.Coins n :=
    Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)
  rw [← uprob_comp_equiv e]
  refine (OneWay.uprob_congr fun r => ?_).trans (hA n x)
  have hofn : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen.symm r).symm
  simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]

/-- **The literal form implies the `1^n` form when the output length determines the
parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
and `B.advice n` at the output length and leaves its extra coins unread.

**Proof sketch.** An injective monotone `outLen.eval` (`PolyExpr.eval_mono`) is strictly
monotone (`Monotone.strictMono_of_injective`), so `n ≤ outLen n` (`StrictMono.id_le`) and
`φ m := the n with outLen n = m` (`0` if none) is majorised by `var`.
`NUPPT.exists_reparam_advice B φ var` gives `A` with
`A.runAtL m y r = B.runAtL (φ m) y (r.take (B.coinLen (φ m)))`; at `m = outLen n` we have
`φ m = n` and `A.Coins m ≃ B.Coins n × (Fin (B.coinLen m − B.coinLen n) → Bool)`
(`Fin.appendEquiv`, `finCongr`, `PolyExpr.eval_mono`); `List.ofFn_fin_append` and
`List.take_left'` identify the literal event with the `1^n` event on the first factor
(`uprob_comp_equiv`, `uprob_fst`). -/
theorem WorstCaseOneWayLit.toParam {𝓕 : FunFamily} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay := by
  classical
  refine ⟨h.easy, ?_⟩
  rintro ⟨B, hB⟩
  have hsm : StrictMono 𝓕.outLen.eval := 𝓕.outLen.eval_mono.strictMono_of_injective hinj
  have hle : ∀ n, n ≤ 𝓕.outLen.eval n := fun n => hsm.id_le n
  let φ : ℕ → ℕ := fun m => if hm : ∃ n, 𝓕.outLen.eval n = m then hm.choose else 0
  have hφ : ∀ m, φ m ≤ PolyExpr.var.eval m := by
    intro m
    simp only [φ, PolyExpr.eval_var]
    split_ifs with hm
    · exact (hle _).trans_eq hm.choose_spec
    · exact Nat.zero_le _
  have hφn : ∀ n, φ (𝓕.outLen.eval n) = n := by
    intro n
    have hm : ∃ n', 𝓕.outLen.eval n' = 𝓕.outLen.eval n := ⟨n, rfl⟩
    simp only [φ, dif_pos hm]
    exact hinj hm.choose_spec
  obtain ⟨A, hAc, hA⟩ := B.exists_reparam_advice φ .var hφ
  refine h.hard ⟨A, fun n x => ?_⟩
  have hAlen : A.coinLen (𝓕.outLen.eval n) =
      B.coinLen n + (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) := by
    have h1 : A.coinLen (𝓕.outLen.eval n) = B.coinLen (𝓕.outLen.eval n) := by
      simp only [NUPPT.coinLen, hAc, PolyExpr.eval_subst, PolyExpr.eval_var]
    have h2 : B.coinLen n ≤ B.coinLen (𝓕.outLen.eval n) := B.coins.eval_mono (hle n)
    omega
  let e : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool) ≃
      A.Coins (𝓕.outLen.eval n) :=
    (Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hAlen.symm) (Equiv.refl Bool))
  rw [← uprob_comp_equiv e]
  have key : ∀ z : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool),
      (∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) (e z) = some x' ∧
        𝓕.f n x' = 𝓕.f n x) ↔
      ∃ x', B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) z.1 = some x' ∧
        𝓕.f n x' = 𝓕.f n x := by
    intro z
    have hofn : List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
      rw [← List.ofFn_fin_append]
      exact (List.ofFn_congr hAlen.symm (Fin.append z.1 z.2)).symm
    simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hA, hφn, hofn,
      List.take_left', List.length_ofFn]
  rw [OneWay.uprob_congr key]
  exact (uprob_fst fun r : B.Coins n => ∃ x',
    B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
      𝓕.f n x' = 𝓕.f n x).trans (hB n x)

/-- On a length-regular `f`, the family `ofString f p` is exactly `f` on encoded strings. -/
theorem ofFn_ofString_f {f : List Bool → List Bool} {p : PolyExpr} (hf : LengthRegular f p)
    (n : ℕ) (x : Fin n → Bool) : List.ofFn ((ofString f p).f n x) = f (List.ofFn x) := by
  have hlen : (f (List.ofFn x)).length = p.eval n := by rw [hf, List.length_ofFn]
  refine List.ext_get (by simp [ofString, hlen]) fun i h₁ h₂ => ?_
  simp [ofString, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- The identity family is the identity at every parameter. -/
theorem ofString_id_f (n : ℕ) (x : Fin n → Bool) : (ofString id .var).f n x = x := by
  have h := ofFn_ofString_f (f := id) (p := .var) (fun x => by simp) n x
  exact List.ofFn_injective (by simpa using h)

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (blocks q ℓ).symm t k = t k.divNat k.modNat := rfl

/-- The encoding of a tuple of blocks is the concatenation of the encodings of the blocks. -/
theorem ofFn_blocks_symm (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) :
    List.ofFn ((blocks q ℓ).symm t) = (List.ofFn fun i => List.ofFn (t i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  rw [blocks_symm_apply]
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
  congr 1
  · refine Fin.ext ?_
    simp only [Fin.coe_divNat]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt j.2, zero_add]
  · refine Fin.ext ?_
    simp only [Fin.coe_modNat]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-- The input length of the direct product is `q · inLen`. -/
@[simp] theorem prod_inLen (𝓕 : FunFamily) (q : PolyExpr) : (𝓕.prod q).inLen = .mul q 𝓕.inLen :=
  rfl

/-- The output length of the direct product is `q · outLen`. -/
@[simp] theorem prod_outLen (𝓕 : FunFamily) (q : PolyExpr) :
    (𝓕.prod q).outLen = .mul q 𝓕.outLen := rfl

/-- The direct product unfolded: `prodFun` between the block bijections. -/
theorem prod_f (𝓕 : FunFamily) (q : PolyExpr) (n : ℕ) (x : Fin (q.eval n * 𝓕.inLen.eval n) → Bool) :
    (𝓕.prod q).f n x = (blocks (q.eval n) (𝓕.outLen.eval n)).symm
      (OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x)) := rfl

/-- The inversion probability of the direct product is the concrete `invProbOpt` of
`OneWay.prodFun (f n) (q n)` against the inverter that encodes its challenge tuple by
`blocks` and decodes its answer: the bridge from `𝓕.prod q` to [Gar26, Theorem 2.1].

**Proof sketch.** Reindex the uniform input `x : {0,1}^{q·ℓ}` by the bijection `blocks`
(`uprob_comp_equiv` on the first coordinate); `f'` is `blocks⁻¹ ∘ prodFun ∘ blocks` by
`prod_f`, and `blocks⁻¹` is injective, so the success events coincide pointwise. -/
theorem invProbAt_prod_eq (𝓕 : FunFamily) (q : PolyExpr) (A : NUPPT) (n : ℕ) :
    (𝓕.prod q).invProbAt A n =
      invProbOpt (OneWay.prodFun (𝓕.f n) (q.eval n)) fun ys r =>
        (A.inverter n (q.eval n * 𝓕.inLen.eval n) (q.eval n * 𝓕.outLen.eval n)
          ((blocks (q.eval n) (𝓕.outLen.eval n)).symm ys) r).map (blocks (q.eval n) (𝓕.inLen.eval n)) := by
  unfold invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (blocks (q.eval n) (𝓕.inLen.eval n)) (Equiv.refl _))]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq, prod_f,
    Option.map_eq_some_iff]
  apply propext
  constructor
  · rintro ⟨x', hx', hf⟩
    refine ⟨blocks _ _ x', ⟨x', hx', rfl⟩, ?_⟩
    have := congrArg (blocks (q.eval n) (𝓕.outLen.eval n)) hf
    simpa using this
  · rintro ⟨t, ⟨x', hx', rfl⟩, hf⟩
    exact ⟨x', hx', by simp [hf]⟩

/-- **The direct product is easy to compute.** If `𝓕` is easy then so is `𝓕.prod q`
[PS10, Theorem 35.1, "`f'` is easy to compute"].

**Proof sketch.** Let `F` be the evaluator of `𝓕`. The evaluator of `𝓕.prod q` is the
blockwise evaluator `OneWay.exists_prodEval F inLen q` (an instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := q` on the state word `⟨⟨1^n, cnt⟩, rest⟩`:
while the unary counter `cnt` is shorter than `1^{q(n)}` a round emits `F ⟨1^n, rest.take (inLen n)⟩`
and drops `inLen n` bits, afterwards it emits `[]`; `q` is evaluated at the state-word length
`≥ n`, so exactly `q(n)` rounds emit). Its specification gives the concatenation over `i < q(n)`
of `F ⟨1^n, block i⟩`, which is the concatenation of `List.ofFn (f n (blocks x i))`
(`ofFn_blocks_symm`, the hypothesis on `F`). -/
theorem Easy.prod {𝓕 : FunFamily} (h : 𝓕.Easy) (q : PolyExpr) : (𝓕.prod q).Easy := by
  obtain ⟨F, hF, hFx⟩ := h
  obtain ⟨F', hF', hspec⟩ := OneWay.exists_prodEval hF 𝓕.inLen q
  refine ⟨F', hF', fun n x => ?_⟩
  rw [NUPPT.advInput, hspec, prod_f, ofFn_blocks_symm]
  congr 2
  funext i
  exact hFx n (blocks (q.eval n) (𝓕.inLen.eval n) x i)

end FunFamily

/-! ## Yao's parameters and the concrete one-call reduction -/

/-- The number of blocks `m = 2 n q(n)` of [PS10, §2.4.3] ("we pick `m = 2nq(n)`"), as a
syntactic polynomial. -/
def yaoBlocks (q : PolyExpr) : PolyExpr := .mul (.const 2) (.mul .var q)

/-- The number of repetitions `T = 2 n m(n) n^c` of the one-call inverter [PS10, §2.4.3, the
definition of `A`]: the text's `2nm²p(n)` with `p(n) = n^c` and one factor `m` saved by the
threshold `θ = μ₀/(2m)` of `OneWay.yao_amplification_exp`. -/
def yaoRounds (q : PolyExpr) (c : ℕ) : PolyExpr :=
  .mul (.const 2) (.mul .var (.mul (yaoBlocks q) (.pow .var c)))

/-- `m(n) = 2 n q(n)`. -/
@[simp] theorem eval_yaoBlocks (q : PolyExpr) (n : ℕ) : (yaoBlocks q).eval n = 2 * (n * q.eval n) :=
  rfl

/-- `T(n) = 2 n m(n) n^c`. -/
@[simp] theorem eval_yaoRounds (q : PolyExpr) (c : ℕ) (n : ℕ) :
    (yaoRounds q c).eval n = 2 * (n * ((yaoBlocks q).eval n * n ^ c)) := rfl

/-- `m(n)` is positive for `n ≥ 1` and positive `q`. -/
theorem yaoBlocks_pos (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) {n : ℕ} (hn : 0 < n) :
    0 < (yaoBlocks q).eval n := by
  simp only [eval_yaoBlocks]
  exact Nat.mul_pos (by norm_num) (Nat.mul_pos hn (hq n))

namespace OneWay

/-- **One-call planting reduction** (lemma C2 of the Chapter 2 inventory, the concrete
content of [PS10, Theorem 35.2]): for every fixed position `i`, the inverter that samples
fresh inputs `xs`, plants the challenge `y` at position `i` of `(f(x₁), …, f(x_q))`, calls `B`
and returns the `i`-th component of the answer (`yaoTry` at the fixed position `i`) inverts
`f` with at least the probability with which `B` inverts `prodFun f q`. [PS10, Theorem 35.2,
proof]; the text's test "`f(a) = u`" is unnecessary for the inequality.

**Proof sketch.** In the planted experiment `(x, xs, r)` the tuple `update xs i x` is uniform
(`OneWay.uprob_update`), so the planted experiment is the direct-product experiment with the
answer projected to position `i`; an inverse of the whole tuple inverts every coordinate
(`uprob_mono`). -/
theorem invProb_prodFun_le_yaoTry {α β ρ : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    [Fintype ρ] {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (i : Fin q) :
    invProb (prodFun f q) B ≤ invProb f fun y c => yaoTry f B y (i, c) := by
  unfold invProb
  have h := uprob_update (α := α) (ρ := ρ) i fun xs r => f (B (prodFun f q xs) r i) = f (xs i)
  simp only [prodFun_update, Function.update_self] at h
  simp only [yaoTry]
  rw [h]
  apply uprob_mono
  rintro ⟨xs, r⟩ hxs
  exact congrFun hxs i

end OneWay

/-- Polynomial times `2^{-n}` is eventually below one. -/
private theorem eventually_poly_mul_two_pow_lt_one (p : PolyExpr) :
    ∃ n₀, ∀ n ≥ n₀, (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n < 1 := by
  obtain ⟨C, e, hCe⟩ := p.eval_le
  have hneg : Negligible fun n => ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow e).const_mul _
  have hμ : Negligible fun n => (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    refine hneg.mono ⟨1, fun n hn => ?_⟩
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have h1 : (p.eval n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ e := by exact_mod_cast hCe n
    have h2 : ((n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ)) ^ e := by
      apply pow_le_pow_left₀ (by positivity)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ (C : ℝ) * (2 * (n : ℝ)) ^ e * (2 : ℝ)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
            (by positivity)
      _ = ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) := by push_cast; ring
  obtain ⟨n₀, h⟩ := hμ 0
  refine ⟨n₀, fun n hn => lt_of_le_of_lt (le_abs_self _) ?_⟩
  simpa using h n hn

/-- `e^{-n} ≤ 2^{-n}`. -/
private theorem exp_neg_le_two_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (2 : ℝ)⁻¹ ^ n := by
  have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h1]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have := Real.add_one_le_exp (1 : ℝ)
  exact inv_anti₀ (by norm_num) (by linarith)

/-- **Parameter instantiation** [PS10, §2.4.3, Claim 38.2 of the inventory]: with
`m(n) = 2nq(n)` blocks (`yaoBlocks q`) and `T(n) + 1 = 2nm(n)n^c + 1` repetitions
(`yaoRounds q c`), for all large `n` and every `f`, `B` such that `B` inverts `prodFun f (m n)`
with probability at least `1/n^c`, `yaoInverter f B (T n + 1)` inverts `f` with probability
exceeding `1 - 1/q(n) + (T(n) + 1)·2^{-n}` (the margin is the statistical term of the
rejection-sampled positions that `weak_to_strong` subtracts). The concrete inequality is
`OneWay.yao_amplification_exp` [Gar26, Theorem 2.1].

**Deviation:** the text takes `T = 2nm²p(n)` and the threshold `1/(2m²p(n))`; with the
threshold `μ₀/(2m)` of `yao_amplification_exp` one factor `m` is saved. The statistical margin
is absent from the text (exact sampling of `i ← [m]`).

**Proof sketch.** Apply `OneWay.yao_amplification_exp` with `α' := 1/q(n) ≤ 1`, `q := m(n)`
(so `α' m(n) = 2n`), `μ₀ := 1/n^c`, `T' := T(n) + 1` (so `μ₀ T' ≥ 2n m(n)`); it needs
`2e^{-n} < 1/n^c` and yields `invProb f (yaoInverter …) ≥ 1 - 1/(2q(n)) - e^{-n}`. Both this
and the tail bound `e^{-n} + (T(n) + 1) 2^{-n} < 1/(2q(n))` follow from `e^{-n} ≤ 2^{-n}` and
`eventually_poly_mul_two_pow_lt_one` (polynomial times `2^{-n}` is negligible,
`negligible_two_pow_neg`, `Negligible.mul_pow`). `NeZero (m n)` is `yaoBlocks_pos`. -/
theorem claim_38_2 (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) (c : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ {α β ρ : Type} [Fintype α] [Inhabited α] [DecidableEq β] [Fintype ρ]
      [Nonempty ρ] (f : α → β) (B : (Fin ((yaoBlocks q).eval n) → β) → ρ → (Fin ((yaoBlocks q).eval n) → α)),
      1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun f ((yaoBlocks q).eval n)) B →
      1 - 1 / (q.eval n : ℝ) + ((yaoRounds q c).eval n + 1) * (2 : ℝ)⁻¹ ^ n <
        invProb f (OneWay.yaoInverter f B ((yaoRounds q c).eval n + 1)) := by
  obtain ⟨n₁, h₁⟩ := eventually_poly_mul_two_pow_lt_one (.mul (.const 2) (.pow .var c))
  obtain ⟨n₂, h₂⟩ := eventually_poly_mul_two_pow_lt_one
    (.mul (.add (yaoRounds q c) (.const 2)) (.mul (.const 2) q))
  refine ⟨max 1 (max n₁ n₂), fun n hn => ?_⟩
  set m : ℕ := (yaoBlocks q).eval n with hm
  set T : ℕ := (yaoRounds q c).eval n with hT
  intro α β ρ _ _ _ _ _ f B hμ
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqR : (1 : ℝ) ≤ q.eval n := by exact_mod_cast hq n
  have hexp := exp_neg_le_two_pow n
  have hb := h₁ n (le_of_max_le_left (le_of_max_le_right hn))
  have hc := h₂ n (le_of_max_le_right (le_of_max_le_right hn))
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow, PolyExpr.eval_var,
    PolyExpr.eval_add] at hb hc
  push_cast at hb hc
  have hμ₀ : 2 * Real.exp (-(n : ℝ)) < 1 / (n : ℝ) ^ c := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < 2⁻¹ by norm_num) n, pow_pos (show (0:ℝ) < n by linarith) c]
  haveI : NeZero m := ⟨(yaoBlocks_pos q hq hn1).ne'⟩
  have hmR : (m : ℝ) = 2 * (n * q.eval n) := by rw [hm, eval_yaoBlocks]; push_cast; ring
  have hTR : (T : ℝ) = 2 * (n * (m * (n : ℝ) ^ c)) := by rw [hT, eval_yaoRounds]; push_cast; ring
  have hα₁ : 1 / (q.eval n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hqR
  have hq' : 2 * (n : ℝ) ≤ 1 / (q.eval n : ℝ) * (m : ℝ) := by
    have : 1 / (q.eval n : ℝ) * (2 * (n * q.eval n)) = 2 * n := by field_simp
    rw [hmR, this]
  have hT' : 2 * (n : ℝ) * (m : ℝ) ≤ 1 / (n : ℝ) ^ c * ((T + 1 : ℕ) : ℝ) := by
    push_cast
    rw [hTR]
    have hpos : (0 : ℝ) < (n : ℝ) ^ c := by positivity
    have : 1 / (n : ℝ) ^ c * (2 * (n * (m * (n : ℝ) ^ c)) + 1) = 2 * n * m + 1 / (n : ℝ) ^ c := by
      field_simp
    rw [this]
    linarith [show 0 < 1 / (n : ℝ) ^ c by positivity]
  have hmain := OneWay.yao_amplification_exp f B (n := n) (α' := 1 / (q.eval n : ℝ))
    (μ₀ := 1 / (n : ℝ) ^ c) (T + 1) hα₁ hq' hT' hμ₀ hμ
  have htail : Real.exp (-(n : ℝ)) + ((T : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n < 1 / (q.eval n : ℝ) / 2 := by
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    rw [lt_div_iff₀ (by norm_num), lt_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ## Hardness amplification -/

/-- The block bijection of this file is the one of `OneWayLemmas`/`OneWayYao`. -/
private theorem blocks_eq_blocksE (q ℓ : ℕ) : FunFamily.blocks q ℓ = OneWay.blocksE q ℓ := rfl

/-- **Yao's hardness amplification** [PS10, Theorem 35.1]: for every weak one-way function
`𝓕` there is a polynomial `m` (the proof takes `m(n) = 2nq(n)`, `q` the polynomial of weak
one-wayness) such that the direct product `𝓕.prod m`, `f'(x₁, …, x_{m(n)}) = (f(x₁), …,
f(x_{m(n)}))`, is strongly one-way.

**Deviation:** `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's
`m = 2nq(n)` and a rejection-sampled position (statistical term absorbed). The direct product
is a family at parameter `n` whose adversaries receive `1^n` (module docstring); the text's
`T = 2nm²p(n)` repetitions become `T(n) + 1`, `T(n) = 2nm(n)n^c` (`yaoRounds`).

**Proof sketch.** Let `q_w` be the polynomial of `h.hard` and `m := yaoBlocks q_w`
(`m(n) = 2nq_w(n)`). *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT` and suppose
`fun n => (𝓕.prod m).invProbAt A' n` is not negligible; `not_negligible_iff` gives `c` with
`1/n^c ≤ (𝓕.prod m).invProbAt A' n` for infinitely many `n` (the function is nonnegative,
`invProbAt_nonneg`). Put `T := yaoRounds q_w c`.

*The reduction `A`* (Algorithm 38.5 repeated) is the machine of `OneWay.exists_yaoReduction`
(`TCSlib.Cryptography.Asymptotic.OneWayYao`, sub-machines in `OneWayLemmas`), applied to the
evaluator `F` of `h.easy` and to `A'`. It is `NUPPT.ofPolyTime` of the loop
`YaoMachine.yaoRaw'` (`Complexity.polyTimeComputable_iterateFind`) with coins
`(T + 1)·ρ`, `ρ(n) = n·m(n) + m(n)·inLen(n) + A'.coins(n)` the coins of one round, and advice
`⟨A'.advice n, 1^{kk}⟩`, `kk = kkOf (m n) = ⌊log₂ m(n)⌋ + 1` (so `m(n) < 2^{kk} ≤ 2m(n)`).
Round `t` consumes the `t`-th block of `ρ(n)` coins: it reads `n·kk` of its `n·m(n)` position
bits and samples the
position `i ← [m(n)]` by rejection (`n` trials of `kk` bits, D10), evaluates `f` on the `m(n)`
fresh inputs, plants `y` at block `i`, calls `A'` on the planted tuple, takes block `i` of the
answer padded with `true` to `inLen(n)` bits (the total inverter `OneWay.yaoB`), and tests
`f(z_i) = y`; the machine returns the first success and `1^{inLen n}` on exhaustion.

*Functional identity.* On `⟨⟨⟨1^n, y⟩, ⟨A'.advice n, 1^{kk}⟩⟩, r⟩` the machine returns
`OneWay.yaoInverter (𝓕.f n) (yaoB … A' n) (T n + 1) y (sampleAll r)` (`YaoMachine.yaoRaw'_layout`),
where `sampleAll r` reads the typed coins of the `T(n) + 1` rounds (position, inputs, coins of
`A'`) off `r`.

*Probability.* Each round's position is within `(1 − m/2^{kk})^n ≤ 2^{-n}` of uniform
(`statClose_rejectionSample`); `YaoMachine.statClose_sampleAll` and
`StatClose.abs_uprob_sub_le_prod` give, for `n ≥ 1`,
`𝓕.invProbAt A n ≥ invProb (𝓕.f n) (yaoInverter (𝓕.f n) (yaoB … A' n) (T n + 1)) − (T n + 1)·2^{-n}`
(`exists_yaoReduction`).

*Conclusion.* `yaoB` inverts the direct product at least as often as `A'` (when `A'`'s answer
decodes, `yaoB` returns its blocks: `invProbAt_prod_eq`, `NUPPT.inverter_eq_some_iff`,
`OneWay.padTrue_drop_ofFn`), so at the infinitely many `n` with
`1/n^c ≤ (𝓕.prod m).invProbAt A' n`, also `1/n^c ≤ invProb (prodFun (𝓕.f n) (m n)) (yaoB … A' n)`.
There `claim_38_2` (which packages `OneWay.yao_amplification_exp` with `α' = 1/q_w(n)`,
`μ₀ = 1/n^c`, `T' = T n + 1`) gives
`invProb (𝓕.f n) (yaoInverter …) > 1 − 1/q_w(n) + (T n + 1)·2^{-n}`, hence
`𝓕.invProbAt A n > 1 − 1/q_w(n)` for infinitely many `n`, contradicting `h.hard` for `A`
(`∃ n₀, ∀ n ≥ n₀, … ≤ 1 − 1/q_w(n)`). -/
theorem weak_to_strong {𝓕 : FunFamily} (h : FunFamily.WeakOneWay 𝓕) :
    ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q) := by
  obtain ⟨qw, hqw, hhard⟩ := h.hard
  refine ⟨yaoBlocks qw, h.easy.prod _, fun A' => ?_⟩
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.1 hneg
  obtain ⟨F, hF, hFx⟩ := h.easy
  have hFe_spec : ∀ n (a : Fin (𝓕.inLen.eval n) → Bool),
      F (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (𝓕.f n a) :=
    fun n a => hFx n a
  have hm : ∀ n, 1 ≤ n → 0 < (yaoBlocks qw).eval n := fun n hn => yaoBlocks_pos qw hqw hn
  -- the reduction machine of Algorithm 38.5
  obtain ⟨A, hA⟩ := OneWay.exists_yaoReduction 𝓕.inLen 𝓕.outLen (yaoBlocks qw) (yaoRounds qw c)
    𝓕.f hF hFe_spec A' hm
  obtain ⟨n₀, hn₀⟩ := hhard A
  obtain ⟨n₁, hn₁⟩ := claim_38_2 qw hqw c
  obtain ⟨n, hn, hlow⟩ := hc (max 1 (max n₀ n₁))
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnn₀ : n₀ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnn₁ : n₁ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hlow
  -- the total inverter `yaoB` inverts the direct product at least as often as `A'`
  have hB : 1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n))
      (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) := by
    refine hlow.trans ?_
    rw [FunFamily.invProbAt_prod_eq]
    unfold invProbOpt invProb
    apply uprob_mono
    rintro ⟨xs, r⟩ ⟨xs', hxs', hf⟩
    rw [Option.map_eq_some_iff] at hxs'
    obtain ⟨x'', hx'', rfl⟩ := hxs'
    rw [NUPPT.inverter_eq_some_iff, blocks_eq_blocksE] at hx''
    have hyB : OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n
        (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n) xs) r =
        FunFamily.blocks ((yaoBlocks qw).eval n) (𝓕.inLen.eval n) x'' := by
      funext j
      simp only [OneWay.yaoB]
      rw [hx'', OneWay.padTrue_drop_ofFn]
      rfl
    rw [hyB]
    exact hf
  -- the parameter instantiation and the reduction's bound
  have hclaim := @hn₁ n hnn₁ (Fin (𝓕.inLen.eval n) → Bool) (Fin (𝓕.outLen.eval n) → Bool)
    (A'.Coins n) _ ⟨fun _ => true⟩ _ _ _ (𝓕.f n)
    (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) hB
  have hred := hA n hn1
  have hup := hn₀ n hnn₀
  unfold FunFamily.invProbAt at hup
  rw [one_div] at hred
  linarith

/-- `blocks q ℓ x i j` reads position `ℓ·i + j` of `x`. -/
private theorem blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl

/-- Two blocks: the encoding of `blocks⁻¹ t` is `ofFn (t 0) ++ ofFn (t 1)`. -/
private theorem ofFn_blocks_two_symm (ℓ : ℕ) (t : Fin 2 → Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks 2 ℓ).symm t) = List.ofFn (t 0) ++ List.ofFn (t 1) := by
  rw [FunFamily.ofFn_blocks_symm, OneWay.flatten_ofFn_two]

/-- **The simple security reduction** [PS10, Theorem 35.2]: if `𝓕` is a strong one-way
function then `g(x, y) = (f(x), f(y))`, the direct product with two blocks (input length
`2·inLen(n)`), is a strong one-way function.

**Deviation:** `g` is `𝓕.prod (const 2)` (two blocks of the typed domain), a family at
parameter `n` whose adversaries receive `1^n` rather than `1^{2n}` (module docstring).

**Proof sketch.** *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT`. The reduction `A`
of the text ("choose a random `y`, compute `v ← f(y)`, submit `(u, v)` to `A'`, output `a`")
is `NUPPT.ofPolyTime` of an FP function of the raw input `⟨⟨⟨1^n, u⟩, A'.advice n⟩, r⟩` with
coins `add (mul (const 2) inLen) A'.coins` and advice `A'.advice`: cut the first `2·inLen n`
coins as a fresh pair of blocks whose second block is `y` (`polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly` on `⟨1^n, r⟩`; the first block is the overwritten coordinate of
the planting lemma), evaluate `v := F ⟨1^n, y⟩` with the evaluator of `h.easy`, call `A'.output`
on the layout `⟨⟨⟨1^n, u ++ v⟩, A'.advice n⟩, r'⟩` (`PolyTimeComputable.append`,
`polyTimeComputable_layout`, `A'.polyTimeComputable_output`) and return the first `inLen n`
bits of the answer (`polyTimeComputable_pairTakePoly inLen`; no length test is needed for an
upper bound). Functional identity: `A.runAt n u (xs, r') = (A'.runAt n (u ++ f (xs 1)) r').take (inLen n)`
after reindexing `A.Coins n ≃ (Fin 2 → Fin (inLen n) → Bool) × A'.Coins n` (`blocks`,
`Fin.appendEquiv`, `uprob_comp_equiv`, `ofFn_blocks_symm`). Probability: `invProbAt_prod_eq`
writes `(𝓕.prod 2).invProbAt A' n` as `invProbOpt (prodFun (f n) 2) B'`, the planting lemma
`OneWay.invProbOpt_prodFun_le_yaoTryOpt` at position `0` bounds it by the planted experiment, and
`uprob_mono` (a `2·inLen n`-bit answer of `A'` decodes to the first block of `A`'s answer,
`ofFn_block_eq_take_drop`) gives `(𝓕.prod 2).invProbAt A' n ≤ 𝓕.invProbAt A n`; conclude by
`h.hard A` and `Negligible.mono` (`invProbAt_nonneg`). -/
theorem strong_prod_two {𝓕 : FunFamily} (h : FunFamily.StrongOneWay 𝓕) :
    FunFamily.StrongOneWay (𝓕.prod (.const 2)) := by
  classical
  obtain ⟨F, hF, hFx⟩ := h.easy
  refine ⟨h.easy.prod _, fun A' => ?_⟩
  -- the reduction: cut two fresh blocks, evaluate `f` on the second, plant, call `A'`, return
  -- the first block of the answer
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hxs := (polyTimeComputable_pairTakePoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hr' := (polyTimeComputable_pairDropPoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hy2 := (polyTimeComputable_pairDropPoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hxs)
  have hv := hF.comp (NUPPT.polyTimeComputable_inParam.pairEncode hy2)
  have hout := A'.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (NUPPT.polyTimeComputable_inArg.append hv) NUPPT.polyTimeComputable_inAdvice hr')
  have hG := (polyTimeComputable_pairTakePoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hout)
  let A : NUPPT := NUPPT.ofPolyTime hG (.add (.mul (.const 2) 𝓕.inLen) A'.coins) A'.adv A'.advice
    A'.advice_length
  refine (h.hard A).mono ⟨0, fun n _ => ?_⟩
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  set ℓ := 𝓕.inLen.eval n with hℓ
  set f := 𝓕.f n with hf
  -- the coin bijection `(xs, r') ↦ ⟨xs⟩ ++ r'`
  have hlen : 2 * ℓ + A'.coinLen n = A.coinLen n := rfl
  let e : (Fin 2 → Fin ℓ → Bool) × A'.Coins n ≃ A.Coins n :=
    (Equiv.prodCongr (FunFamily.blocks 2 ℓ).symm (Equiv.refl _)).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)))
  have hofn : ∀ (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      List.ofFn (e (xs, r')) = (List.ofFn (xs 0) ++ List.ofFn (xs 1)) ++ List.ofFn r' := by
    intro xs r'
    rw [← ofFn_blocks_two_symm, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen (Fin.append ((FunFamily.blocks 2 ℓ).symm xs) r')).symm
  -- the functional identity of the reduction
  have hrun : ∀ (y : Fin (𝓕.outLen.eval n) → Bool) (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      A.runAt n (List.ofFn y) (e (xs, r')) =
        (A'.runAt n (List.ofFn y ++ List.ofFn (f (xs 1))) r').take ℓ := by
    intro y xs r'
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTime hG _ _ _ _).runAtL n _ _ = _
    rw [NUPPT.runAtL_ofPolyTime]
    simp only [Function.comp, NUPPT.advInput, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
      NUPPT.inCoins, NUPPT.layout, pairFstD_pairEncode, pairSndD_pairEncode, hofn,
      PolyExpr.eval_mul, PolyExpr.eval_const, List.length_replicate]
    have h2 : (List.ofFn (xs 0) ++ List.ofFn (xs 1)).length = 2 * ℓ := by simp; ring
    rw [List.take_left' h2, List.drop_left' h2,
      List.drop_left' (by simp only [List.length_ofFn]; try exact hℓ)]
    have := hFx n (xs 1)
    simp only [NUPPT.advInput] at this
    rw [this]
    rfl
  -- the planting bound
  let B' : (Fin 2 → Fin (𝓕.outLen.eval n) → Bool) → A'.Coins n → Option (Fin 2 → Fin ℓ → Bool) :=
    fun ys r => (A'.inverter n (2 * ℓ) (2 * 𝓕.outLen.eval n)
      ((FunFamily.blocks 2 (𝓕.outLen.eval n)).symm ys) r).map (FunFamily.blocks 2 ℓ)
  have h1 : (𝓕.prod (.const 2)).invProbAt A' n = invProbOpt (OneWay.prodFun f 2) B' :=
    FunFamily.invProbAt_prod_eq 𝓕 (.const 2) A' n
  have h2 := OneWay.invProbOpt_prodFun_le_yaoTryOpt f B' 0
  refine h1.trans_le (h2.trans ?_)
  unfold FunFamily.invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl _) e)]
  apply uprob_mono
  rintro ⟨x, xs, r'⟩ ⟨x', hx', hfx⟩
  refine ⟨x', ?_, hfx⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  rw [Option.map_eq_some_iff] at hx'
  obtain ⟨xs', hxs', rfl⟩ := hx'
  simp only [B', Option.map_eq_some_iff] at hxs'
  obtain ⟨x'', hx'', rfl⟩ := hxs'
  rw [NUPPT.inverter_eq_some_iff, ofFn_blocks_two_symm, Function.update_self,
    Function.update_of_ne (by decide), OneWay.prodFun] at hx''
  rw [NUPPT.inverter_eq_some_iff, hrun, hx'']
  have hblk := OneWay.ofFn_block_eq_take_drop x'' 0
  simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero] at hblk
  rw [← hblk]
  rfl

/-- **Strong implies weak** (sanity, [PS10, §2.2, the remark after Definition 28.4]): a strong
one-way function is a weak one-way function with `q = 2`.

**Proof sketch.** Negligibility with `c = 1` gives `invProbAt A n < 1/n ≤ 1/2 = 1 - 1/2` for
all `n ≥ max n₀ 2`. -/
theorem FunFamily.StrongOneWay.weak {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay := by
  refine ⟨h.easy, .const 2, fun _ => by simp, fun A => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.hard A 1
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / (n : ℝ) ^ 1 ≤ 1 / 2 := by
    rw [pow_one]; exact one_div_le_one_div_of_le (by norm_num) hn2
  simp only [PolyExpr.eval_const, Nat.cast_ofNat]
  linarith [le_abs_self (𝓕.invProbAt A n)]

/-- A machine that returns its argument exists: `A(1^n, y; r) = y` (`ofPolyTimeUniform` of the
argument projection, no coins). -/
private theorem exists_runAt_eq_arg : ∃ A : NUPPT, ∀ n y (r : A.Coins n), A.runAt n y r = y :=
  ⟨NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inArg (.const 0), fun n y r => by
    rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
    exact NUPPT.inArg_layout _ _ _ _⟩

/-- **A machine that returns its argument inverts the identity with probability one**: if
`A(1^n, y; r) = y` for all `n`, `y`, `r`, then `(ofString id var).invProbAt A n = 1` at every
parameter `n` (the common step of the non-vacuity results below and of
`FunFamily.not_toCollection_oneWay_id`).

**Proof sketch.** By `invProbAt_eq_uprob` the event is that `A(1^n, x)` is the encoding of a
preimage of `x`; it holds for every `(x, r)` with the preimage `x` itself (`ofString_id_f`), so
the probability is `uprob True = 1`. -/
theorem FunFamily.invProbAt_ofString_id_eq_one {A : NUPPT}
    (hA : ∀ n y (r : A.Coins n), A.runAt n y r = y) (n : ℕ) :
    (FunFamily.ofString id .var).invProbAt A n = 1 := by
  rw [FunFamily.invProbAt_eq_uprob]
  have hp : (fun z : (Fin ((FunFamily.ofString id .var).inLen.eval n) → Bool) × A.Coins n =>
      ∃ x', A.runAt n (List.ofFn ((FunFamily.ofString id .var).f n z.1)) z.2 = List.ofFn x' ∧
        (FunFamily.ofString id .var).f n x' = (FunFamily.ofString id .var).f n z.1) =
      fun _ => True := by
    funext z
    refine propext ⟨fun _ => trivial, fun _ => ⟨z.1, ?_, rfl⟩⟩
    rw [hA, FunFamily.ofString_id_f]
  rw [hp, uprob_true]

/-- **The identity is not one-way** (non-vacuity of the adversary class, [PS10, §2.2]): the
machine that returns its argument inverts `FunFamily.ofString id var` with probability one at
every parameter, and the constant `1` is not negligible.

**Proof sketch.** `A := NUPPT.ofPolyTimeUniform polyTimeComputable_inArg (const 0)` returns
`y` on `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (`runAtL_ofPolyTimeUniform`, `inArg_layout`), so
`invProbAt … A n = 1` (`FunFamily.invProbAt_ofString_id_eq_one`); `Negligible (fun _ => 1)`
fails at `c = 0`. -/
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var) := by
  intro h
  obtain ⟨A, hA⟩ := exists_runAt_eq_arg
  obtain ⟨n₀, hn₀⟩ := h.hard A 0
  have := hn₀ n₀ le_rfl
  simp [FunFamily.invProbAt_ofString_id_eq_one hA] at this

/-- **The identity is not weakly one-way** (non-vacuity of [PS10, Definition 28.4]; gate 03b,
finding 13): the machine that returns its argument inverts `FunFamily.ofString id var` with
probability `1 > 1 − 1/q(n)` at every parameter, for every positive polynomial `q`.

**Proof sketch.** As `not_strongOneWay_id`: `invProbAt … A n = 1`
(`FunFamily.invProbAt_ofString_id_eq_one`), and `1 ≤ 1 − 1/q(n₀)` contradicts `q(n₀) > 0`. -/
theorem not_weakOneWay_id : ¬ FunFamily.WeakOneWay (FunFamily.ofString id .var) := by
  intro h
  obtain ⟨q, hq, hhard⟩ := h.hard
  obtain ⟨A, hA⟩ := exists_runAt_eq_arg
  obtain ⟨n₀, hn₀⟩ := hhard A
  have h1 := hn₀ n₀ le_rfl
  rw [FunFamily.invProbAt_ofString_id_eq_one hA] at h1
  have h2 : (0 : ℝ) < 1 / (q.eval n₀ : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr (hq n₀))
  linarith

/-- **The identity is not worst-case one-way** (non-vacuity of [PS10, Definition 26.1], `1^n`
form; gate 03b, finding 13): the machine that returns its argument inverts
`FunFamily.ofString id var` on every input with probability one.

**Proof sketch.** On `⟨1^n, x⟩` the machine returns `x`, which the inverter decodes to `x`
(`NUPPT.inverter_eq_some_iff`), a preimage of `x` (`ofString_id_f`); so the event holds for
every coin string and its probability is `uprob True = 1`. -/
theorem not_worstCaseOneWay_id : ¬ FunFamily.WorstCaseOneWay (FunFamily.ofString id .var) := by
  intro h
  obtain ⟨A, hA⟩ := exists_runAt_eq_arg
  refine h.hard ⟨A, fun n x => ?_⟩
  have hp : (fun r : A.Coins n => ∃ x', A.inverter n ((FunFamily.ofString id .var).inLen.eval n)
      ((FunFamily.ofString id .var).outLen.eval n) ((FunFamily.ofString id .var).f n x) r =
        some x' ∧ (FunFamily.ofString id .var).f n x' = (FunFamily.ofString id .var).f n x) =
      fun _ => True := by
    funext r
    refine propext ⟨fun _ => trivial, fun _ => ⟨x, ?_, rfl⟩⟩
    rw [NUPPT.inverter_eq_some_iff, hA, FunFamily.ofString_id_f]
  rw [hp, uprob_true]

/-! ## One-way permutations -/

/-- A family of permutations of `{0,1}^n` (the single one-way permutation of
[PS10, Theorems 79.4 and 126.4]; the *collection* of permutations of [PS10, Definition 55.1] is
`PermCollection` in `Asymptotic/Collections.lean`). -/
structure PermFamily where
  /-- The permutation at parameter `n`. -/
  f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)

/-- The function family underlying a permutation family: `inLen = outLen = var`. -/
def PermFamily.toFunFamily (P : PermFamily) : FunFamily where
  inLen := .var
  outLen := .var
  f n := P.f n

/-- `P` is a *one-way permutation* when its underlying family is strongly one-way
[PS10, §2.10, Definition 55.1, single-function form, as used in Theorems 79.4 and 126.4]. -/
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay

/-- The function of a permutation family is the permutation. -/
@[simp] theorem PermFamily.toFunFamily_f (P : PermFamily) (n : ℕ) (x : Fin n → Bool) :
    P.toFunFamily.f n x = P.f n x := rfl

end TCSlib.Cryptography

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03b-r1.md =====

# Gate 03b (one-wayness and collections): round 1 resolutions

- **Round 1:** findings `findings/gate03b-findings.md`, verbatim, SHA-256
  `0d3a1f038c63a13cfc0f7484832049d5559790e84f6d19935a2241716b01bbb6`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 1 major (#1), 3 minors,
  10 notes.**
- **Review:** `review/gate03b-review.md`: 12 true, 1 partly true (#1), 1 true and resolved by the
  review (#14), none false. #1 stays a major, not a blocker (the formal Algorithm 104.3 takes a
  `PredEvaluator`). One severity change: #12 is split, and (c) (unledgered copies) goes from note to
  **minor**; (a), (b), (d) stay notes. #7 is a note here but, in the review, a blocker for gate 06B.
  New tally **0 blockers, 1 major, 4 minors, the rest notes**. Eight items missed by the auditor
  (M1–M8 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`; decision log rows "Gate 03 rulings G3-1 to
  G3-4" and "G3-5 to G3-8"**):** G3-1 (A), canonical decoding `Collection.encD_decD` (#1); G3-5
  (A), ledger and clean up the duplicates (#12c, M6: DL-10, DL-15); G3-6 (A), approve the listed
  `@[simp]` (#12a); G3-8 (A), an enhanced hard-core hypothesis for Prop 161.5 in prong B (#7, M1).
  G3-7 (c) (03c #3, the cost of `henc`) was applied in the same commit and closes M2's overclaim.
- **Repair:** PR #198, head `c10ed6ace0b991146c0be769313fbbe52d36e25a` (one commit on
  `a3c5fa8b…`), merged into `cryptography/pass-shelat-ch2-4` by
  `cdff8890ee4af8eec7d6682963c02041390f52f2`. Maintainer re-check recorded in the decision log
  (#198 row: 62 downstream modules plus `Checks`, no `sorry` change, lint 0); the prints below are
  in the `Checks` axiom print at #201's head (`evidence-repairs/03ac/checks-axioms.log`). Line
  numbers are at #201's head (`0c348ff94cacf24d96d99078c9dd9e328530c8d2`, which contains #198);
  Lean paths are under `TCSlib/Cryptography/`.
- **Prong B** (outside ch. 2–4): G3-8 is commit `587843c76f95f10056c9ddc9174da9dc8fba8b54` on
  `cryptography/pass-shelat-ch5-8-prong-b`.

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major (not blocker) | **Fixed** (G3-1). The field `encD_decD` (`Asymptotic/Collections.lean:141–147`) is proved for every instance (`Collections.lean:420`; `Asymptotic/HardCoreCollection.lean:103–107`; `Candidates/DiscreteLog.lean:571`, `Factoring.lean:585`, `RSA.lean:648`, `Rabin.lean:476, 855`), with the derived `decD_eq_some_iff` … `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv` (`Collections.lean:258–289, 362, 373`), `HardCore.nonempty_predEvaluator` and the evaluator-free `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure` (`Asymptotic/PublicKey.lean:549, 973`), DESIGN §2.10 and §5 item 24 (`briefs/pass-shelat/DESIGN.md:587, 630–640, 1064–1067`); prints standard (`checks-axioms.log:424–433`). **Scheduled:** prong B still carries `hcanon : SamplerCanonical T` and `hspec`; dropping them is in gate 06's integration to-do (`gates/06-ch5-8-statements/PLAN.md:58–59`). |
| 2 | minor | **Fixed** (docstrings). The `LengthRegular` proviso is in DESIGN D5 (`DESIGN.md:87–88`), `OneWay.lean`'s module docstring (:29–31) and `FunFamily` (:92–93). `ofString` keeps its padding (marker padding not recommended: it would change `fUniversal`). |
| 3 | minor | **Fixed.** `OneWayPermutation` cites [PS10, §2.10, Definition 55.1, single-function form, as used in Theorems 79.4 and 126.4] (`Asymptotic/OneWay.lean:916`); Thm 126.4 is dropped from `Collection.HardCore`'s consumers and the two lists agree (`Collections.lean:25–26, 221`). |
| 4 | minor | **Fixed.** `owfFamily_strongOneWay`'s sketch (`Collections.lean:926–953`) describes `padStr` and the reduction without a length check (and why none is needed); `weak_to_strong`'s (`OneWay.lean:603–641`) describes `OneWay.exists_yaoReduction` with advice `⟨A'.advice n, 1^{kk}⟩`, the "Implementation" paragraph folded in. |
| 5 | note | **Fixed** (optional docstring): `PermCollection` (`Collections.lean:300–303`) says junk indices may have a one-element domain. |
| 6 | note | **Fixed.** `TrapdoorCollection`'s P3-5 deviation (`Collections.lean:326–334`) and DESIGN §5 item 17 (`DESIGN.md:1031–1035`) give the general argument (`t' := ⟨i, t⟩`; the classes coincide). |
| 7 | note (blocker for 06B, review) | **No change** in ch. 2–4. G3-8 is applied in prong B (`587843c7…`): `EnhancedHardCore` (`SecureComputation/ObliviousTransfer.lean:149` there), taken by `otProtocol_simulators` and `otProtocol_hbcSecure` (:420, :452); gate 06B audits it. |
| 8 | note | **Fixed.** DESIGN §5 item 23 (`DESIGN.md:1058–1063`): parameter-`n` adversaries for Thms 35.1, 35.2, and Claim 38.2's `T` and threshold. The optional bridge lemma is deferred (review) and not added. |
| 9 | note | **Fixed.** `WorstCaseOneWayLit`'s deviation (`OneWay.lean:175–182`) and DESIGN §5 item 16 (`DESIGN.md:1025–1030`), with the review's correction ("can hold" for constant `outLen`; `f n b = b ⊕ [n odd]`). |
| 10 | note | **Fixed.** "for `n ≥ 1`" at the three places (`Asymptotic/Permutations.lean:28, 78, 426`). |
| 11 | note | **No change** (true; the review proposes none). |
| 12a | note | **Recorded** (G3-6, `QUEUE.md:125`): the 15 attributes are approved and unchanged: `prod_inLen`, `prod_outLen`, `eval_yaoBlocks`, `eval_yaoRounds`, `PermFamily.toFunFamily_f` (`OneWay.lean`), `NUPPT.coins_withIndexParam` (now `Asymptotic/CollectionsHelpers.lean:68`), `liftSucc_zero`, `liftSucc_succ` (`Permutations.lean`), `length_natToList`, `mulStr_`, `addStr_`, `subStr_`, `leStr_`, `modExpStr_pairEncode`, `length_sizeStr` (`Candidates/Arithmetic.lean`). No repair added an attribute. |
| 12b | note | **Fixed** (the review's option): `NUPPT.withIndexParam`, `length_runAt_le`, `runLenPoly` and their lemmas moved, names unchanged, to `Asymptotic/CollectionsHelpers.lean:58–115`, which `Collections.lean` imports. The file is still in the crypto layer, as the review allowed. |
| 12c | minor (was note) | **Scheduled** (G3-5, clean-up part 2). `ptc_comp` (`Collections.lean:644`, private) is DL-10; `decodeFin_eq_some_iff` (`Collections.lean:472`, private; `Asymptotic/GGMReductionEval.lean:163`, public) is DL-15, together with #198's new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean:189`). G3-5 supersedes the review's "inline `ptc_comp` now". |
| 12d | note | **Fixed.** `Collections.lean` was split upstream first and is 982 lines with the new field. |
| 13 | note | **Fixed.** `not_weakOneWay_id`, `not_worstCaseOneWay_id` (`OneWay.lean:870, 887`) and `FunFamily.not_toCollection_oneWay_id` (`Collections.lean:545`), through `FunFamily.invProbAt_ofString_id_eq_one` (`OneWay.lean:836`); printed with `TrapdoorCollection.eval_inv` in `audits/pass-shelat/Checks.lean:404–416`, all standard (`checks-axioms.log:424–436`). |
| 14 | note | **No change:** resolved by the review (`samplePairOut_eq_encode`; the default pair is the canonical encoding). Under G3-1 `factoringCollection` discharges `encD_decD` (`Candidates/Factoring.lean:585`). |
| M1 | (review) Prop 161.5 unprovable as stated | **Fixed** outside ch. 2–4 (G3-8, prong B `587843c7…`); see #7. |
| M2 | (review) `PredEvaluator`; GL docstring overclaims | **Fixed.** Under canonical decoding the evaluator is derivable (`PublicKey.lean:549`) and Thm 104.4's text reading is evaluator-free (:973); "from trapdoor permutations alone" is replaced (`Asymptotic/HardCoreCollection.lean:344–347`, `PublicKey.lean:809–812`; G3-7 (c)). |
| M3 | (review) the lenient fix breaks GL for collections | **No change:** the lenient alternative was not adopted. |
| M4 | (review) the infidelity is in Def 41.1 (2), 56.1 (6) | **Recorded** here and in the field docstring (`Collections.lean:141–146`) and DESIGN §5 item 24: the auditor's inventory row Def-41.1 should read "(2) and Def 56.1 (6) were decode-level only; repaired by `encD_decD`", and (3) was faithful. |
| M5 | (review) `fUniversal` is the in-repo instance of #2 | **No change:** the lossy padding is harmless there; a pointer for 03h. |
| M6 | (review) third copy of `decodeFin_eq_some_iff` | **Scheduled:** DL-15 (part 2). The `GGMRed` copy is public (`GGMReductionEval.lean:163`), which is what makes the namespace collision; the ledger row now says so (corrected 2026-11-05; gate 03b round 2, R2-3). |
| M7 | (review) split `Collections.lean` first | **Fixed:** the split precedes the field (#12b, #12d). |
| M8 | (review) the † items | **No change:** resolved by the review against the extract (#3, #8, #11). |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03b-pack-r2.md =====

# Gate 03b ([PS10] ch. 2–4, one-wayness and collections), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e79397eaf68b156b9db091f464741f6eb75b9c28` (the branch after #201 merged; its Lean files are #201's head `0c348ff9`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 1 major (#1), 3 minors and 10 notes**; after the review, 1 major and 4 minors (#12 (c) raised) (`gate03b-findings.md`, in the bundle,
  verbatim).
- **The repair:** PR #198 (G3-1: the field `Collection.encD_decD`, every instance proved, derived lemmas; G3-7 (c): `glPad`'s `henc` cost; 03b's minors), merged; later changes to this pack's files come from #201 (03a's docstring repairs to `OneWay.lean`). The full delta is `evidence-r2/03b/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03b-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03b-review.md` (in the bundle).
- **The deliverable:** **`gate03b-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03b-r1.md` (the
   findings and the review's missed items `M1`, …) say whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR or gate, and
     the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03b/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** `Collection` gains the field `encD_decD`, so every instance (the candidates, `glPad`, OT's collections) now proves it; no theorem statement of this pack changes otherwise.
- **New public declarations:**
- `Collection.encD_decD` (a new **field** of `Collection`: decoding is canonical) and the derived
  `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`, `sample_eq_encD`,
  `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `TrapdoorCollection.eval_inv`;
- `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, new file: the split of
  `Collections.lean`);
- `natToList_length_listToNat`, `natToList_val_natCast` (`Arithmetic.lean`: numerals are
  canonical);
- the non-vacuity witnesses `not_weakOneWay_id`, `not_worstCaseOneWay_id`,
  `FunFamily.invProbAt_ofString_id_eq_one` (`OneWay.lean`), `FunFamily.not_toCollection_oneWay_id`
  (`Collections.lean`).
- The instances' proofs are in packs 03f1, 03f2 (candidates) and 03i (`HardCoreCollection.lean`); they are context here (section B of the diff).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03b-findings.md`, `review/gate03b-review.md`, `resolutions-03b-r1.md`, `evidence-r2/03b/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Cryptography/Asymptotic/{OneWay, Collections, CollectionsHelpers, Permutations}.lean`, `Candidates/Arithmetic.lean` |
| Context | `03b-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; the scheduled clean-up (G3-5, DL-9 onward) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/b2/` in the bundle)

### Attestation results at `e79397eaf68b156b9db091f464741f6eb75b9c28` (evidence under `evidence/b2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 66 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 111 prints of every public theorem and lemma in this pack's files:
   111 use only the standard axioms, and 0 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes (`evidence-repairs/03ac/replay.log`); each line of `replay.log` is the
newest check of its module, and the Lean files at the pin equal #201's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.
