# Gate 07, round 2: equation-lemma PR #210 — external audit

**Verdict: HOLD — 0 blockers, 1 major, 2 minors.** Round-one F01 and F03 are fixed. F02 is not resolved: the promised sealed consumer of the padded **permutation collection** interface is still absent from the supplied evidence. I found no counterexample to the new equations, no mathematical change in the reviewed restatements, and no additional concrete rule-10 violation in a touched declaration. This is not a blanket approval of the library or its deferred proofs.

## Pins, integrity, and verification boundary

- Exchange checkout: `be9567b7fca668e73e9865abb150c4d074cf598c`, branch `exchange/pass-shelat-ch5-8`.
- Audited Lean head: `3436321ba28042549bead976dc654aab3d661f10`; base: `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`; round-one head: `fff0430c7c9db136e60ed14b069e972c2ea56fc8`.
- Records: `c10170bb631dbab90dfa4ee7b2f573c3efd813fb`, principally `briefs/pass-shelat-ch5-8/gates/07-eqlemmas/`.
- Bundle SHA-256 verified: `1c57a78a17db9fc7225c233fd72a61ef911892ead049c6f94f1d1b61e29e3766`. All 53 sections match their pinned record files, allowing only terminal-newline differences introduced by section extraction.
- Source PDF SHA-256 verified: `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Book pages are PDF pages minus 12.

I read the exchange protocol, round-two brief, round-one findings and resolutions, the pinned Lean diff and relevant surrounding definitions, and the sweep/probe evidence and fill-interface requests. I independently checked the 70-file diff (`+3317 -561`), regenerated the touched-declaration list and the classification from the supplied raw summaries/scan, checked declaration-table headers against source, and attributed the negative-control errors to their examples.

**No Lean replay was performed in this audit.** This host had no Lean/lake toolchain or compiled dependency tree. Compiler results below are explicitly reviews of the archived logs, not new executions. In particular, regenerating a classification independently checks its bookkeeping, not the underlying elaboration run. The final all-70-file proof-seal archive supplies its summary and tools; it does not supply the complete final per-file sealed/unsealed copies and compiler outputs. The earlier runs and the 18-file control have substantially fuller artifacts.

Paths below are relative to the repository; evidence paths without a prefix are relative to the gate's records directory. Source line numbers refer to the audited Lean head.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-01 | **major** | `resolutions-r1.md`, F02; `Asymptotic/HardCoreCollection.lean:394,401,407`, `PermCollection.glPad_domEquiv`, `_apply`, `glPad_perm` | The claimed repair of round-one F02 is not evidenced. | The resolution specifically promises a pass probe with both `PermCollection.glPad` and `Collection.glPad` sealed, plus a paired control. Neither name is in the seal of the round-five/six/six-b final probes, and none of those probes consumes `PermCollection.glPad_perm` or even mentions `PermCollection`. Their `PermFamily` examples concern a different interface. Full-module copies containing the defining declarations do not supply the missing foreign consumer. | Add and archive an actual consumer of this domain/permutation group under the promised seal, a corresponding old-reading control that passes unsealed and fails sealed, and the source-to-log mapping. Run these against the audited head or its explicit successor. Correct F02's disposition only after that evidence exists. |
| R2-02 | **minor** | `Foundations/Experiments.lean:86–100`; `Asymptotic/Adversary.lean:180`; `Asymptotic/HardCoreLemmas.lean:982` | Six new equation docstrings do not state the formula, as required by brief item 3. | `invProb_def`, `predProb_def`, `acceptProb_def`, `distAdv_def`, `invProbOpt_def`, and `glPadInvFun_eq` say only “The defining equation of …”. Their statements are correct; the short docstrings omit the mathematical content requested by the brief. | Put the event/formula, or an exact verbal description of it, into each docstring. No statement or proof change is needed. |
| R2-03 | **minor** | `pack-r2.md`, replay attestation; `evidence-r5/sorry-compare.txt`; `evidence-r2/decls-vs-base.tsv`, `GGMRed.queryOf_eq` row | Two evidence-presentation claims need correction. | “Sorry counts … equal the base's” is false for the named PR base: Factoring has 8 executable `sorry` tokens there and 10 at head; RSA has 9 and 10. These are exactly the authorized S1–S3 additions. The supplied comparison instead has 10→10 in both files. Separately, the `queryOf_eq` table entry stops at `match pairDecode w with`, omitting both branches of the actual statement at `GGMReduction.lean:97`. | Name the later comparison baseline and state that the PR adds precisely the three authorized shared sorries. Include both match branches in the declaration table and ensure the header extractor does not stop before an expression-level match. |

F01: **fixed** — the named `FunFamily.glPad` length reads in `HardCorePermutation` and `HardCoreClaims` now use published length/domain/range interfaces. The broader sweep and follow-up repairs address statements, definition bodies, and touched proofs rather than the former hand-picked collection list.

F02: **not resolved** — the resolution claims completion, but the promised padded permutation-collection pass/control pair is absent (R2-01). This is an evidence finding, not a claim that `glPad_perm` is false.

F03: **fixed** — `polyTimeComputable_samplePrimeL` now restricts the numeral `0^(n-2)10` to `n ≥ 2` and explicitly gives `[]` at zero and `[false]` at one.

## R2-01: exact evidence distinction

The full evidence, not merely the bundle, was searched. In particular:

```text
evidence-r5/probes/Final5Pass.lean
evidence-r5/probes/Final5Control.lean
evidence-r5/probes/Final5OpenControl.lean
evidence-r2/r6/probes/Final6Pass.lean
evidence-r2/r6/probes/Final6Control.lean
evidence-r2/r6/probes/Final6OpenControl.lean
evidence-r2/r6b/probes/Final6Pass.lean
evidence-r2/r6b/probes/Final6Control.lean
evidence-r2/r6b/probes/Final6OpenControl.lean
```

Searching the `.lean` files in these three probe directories for `PermCollection` or `glPad_perm` returns no match. `Final6Pass` group P2 exercises `FunFamily`/`PermFamily` padding, and R5 exercises the `PermFamily` append lemmas. Neither is a `PermCollection` test. The older `evidence/probes/SealRestatedPass.lean.txt` does seal `PermCollection.glPad`, but its examples consume the full-DL and **trapdoor** interfaces; this is the same unused seal that did not discharge round-one F02.

Occurrences of `glPad_perm` in axiom inventories and copied `HardCoreCollection` source likewise do not demonstrate consumer usability with those definitions sealed. The own-file declaration is allowed to read its own definitions. This matters because the round-one finding and accepted resolution specifically require an external use of the domain/permutation group.

The positive test should assert the published conjugated permutation equation on `(P.glPad m henc).D i` using `P.glPad_domEquiv`, and explicitly account for the domain/application part of the group. Its paired negative test should attempt the direct product-domain/permutation reading under the same seal. An imported theorem name appearing only in `#print axioms` is insufficient. I have not represented a proposed probe as an executed test.

## Statement and value review

The supplied manifests contain 367 additions, 58 changes and two removals against the PR base, and 184 additions, 55 changes and two removals against round one. I checked all listed old/new headers directly against the pinned sources: 484 of 485 header comparisons against the base match; the sole exception is the truncated added `queryOf_eq` row in R2-03. All 296 header comparisons against round one match. The source diff, including proof-only and definition-body changes, was reviewed separately; these text comparisons are not a Lean elaboration certificate.

| Change family | Mathematical check and disposition |
|---|---|
| `PermFamily.HardCore`, its nine headline consumers, and permutation-form accessors | `hardCore_iff` expands to `HardCore P.toFunFamily (fun n x => h n (P.toFunFamily_domEquiv n x))`. The domain equivalence is `Equiv.refl`, so this is the previous predicate at every input. It changes neither the efficiency clause nor the adversary quantifiers. The commitment, PRG, and NP wrappers preserve their previous assumptions. |
| `glHalf_f_even/odd`, `glHalfBit_even/odd`, prediction/inversion identities, `thm_87_3_1/2/3/9` | The new input and output equivalences have the correct directions: `.symm` takes a concrete concatenated input into the padded domain; the forward output equivalence returns the padded output to concrete bits. The lengths are proved equal to `m + m`. `ofFn` is unchanged by the casts, and uniform probabilities are unchanged by the bijections. Inverter outputs use the inverse domain transport. The odd case still retains/drops the same last bit. |
| Full-DL hard-core predicate and padded public-key statements | The new predicates compose with the published identity domain equivalences. The encoded inputs, sampled distributions, and hard-core predicates are unchanged. No hardness assumption is added or removed. |
| `expGen_runAt`, the candidate `_index` interfaces, and NUPPT coin interfaces | The new casts expose the coin lengths through proved equations. Their `ofFn` equations preserve every tape bit, including at small parameters. The output encodings and fallback cases are unchanged. |
| `ofFn_fUniversal_f`, `PadQuad.ofFn_family_f`, `quadraticCode_of_linear` | The input binders now use the family's input length. Its published length equation identifies this with the former parameter. The list input, output, and running-time bound remain the same. |
| `gniTapes_apply` | Passing from function equality to equality of `List.ofFn` loses no information: for the equal finite lengths in question, `List.ofFn` is injective. The cast lemma supplies equality of the represented lists. |
| GI/ZK `viewV_encode`, closeness statements, `PerfectZKAbort`, and `sim_ofFn_eq` | `withV_P` preserves the prover; `withV_vCoinsEquiv_ofFn` preserves the verifier's tape; `blockTapeEquiv_ofFn` preserves the block tape. Thus the view encodings, simulator attempts, and statistical errors are unchanged. The retyped `ExecCoins` refers to the prover of the same modified protocol. |
| `NUPPT.uniform_iff`, `NUPPT.Uniform.advice_eq` | The two removed declarations reappear in `Complexity/Randomized/PPT.lean` with the same names and statements. The move makes the interface available in the required import closure. |
| `glNeed` | `def` becomes `abbrev` with the same body. This falls within the explicit accepted notation ruling; it is not counted as an unauthorized exclusion. |

For the body-only changes, I checked the following separately:

- `prodInverter` replaces the reducible product lengths by `fmultBlocks.eval n * (2 * n)`. The published product-length equalities identify both inputs and outputs with the old ones. The block bijection, `Option.getD`, and all-false fallback are unchanged.
- `vTapeSplit`, `giBitEquiv`, `giCoinEquiv`, `gniTapes`, `giRepCoins`, `predCoins`, and `oddCoins` insert casts along proved coin-length equalities. These preserve the represented bit lists, so their pointwise values and induced uniform distributions agree with the old definitions.
- `sampleAll` and `owfFamily` insert the corresponding tape equivalences before the same samplers. `Collection.glPad`, `TrapdoorCollection.glPad`, and the correctness fields of `bitwise` and `prgScheme` retain the same operational data; the changes expose transports or replace proof terms.
- The added `noncomputable` modifiers concern these proof-facing tape equivalences and their dependencies. I found no current executable consumer that requires their former computability. This does not assert that an arbitrary future `#eval` client would be unaffected.

The added equations I inspected agree with their definitions, preserve the exceptional/default branches, and do not introduce hidden mathematical hypotheses. The new equations are public and no new simplifier registration was found; the `@[simp]` lines appearing as additions for several coin lemmas replace already-`@[simp]` declarations. Public wrappers of existing private proofs are deliberate interface exposure, not new independent proofs. The additions concerning the concrete candidates expose project encodings, samplers, and domain fields rather than re-proving elementary number theory from the Mathlib-overlap inventory. R2-02 records the formula-docstring exceptions.

## Rule-10 evidence and controls

| Layer | What was checked | Result and limit |
|---|---|---|
| Statement/definition-body sweep | Collector and minimization method, all-file inventory, round-five remaining reads, and round-six 17-file resweep | The remaining listed reads are in the separately identified #195 scope after the `prodInverter` repair. I found no extra residual in the round-two scope. This does not independently certify #195's separate fix. |
| Touched classification | Re-ran the full-evidence `r6c/touched2.py` against the actual base and head | Exactly 547 entries, matching supplied `touched.tsv`. This is the corrected declaration-content comparison, not the older `touched_code.py` included in the bundle. |
| All-70-file proof seal and explicit scan | Re-ran `r6c/classify.py` with the pinned source, supplied proof-seal summary, and scan output | Exactly `(a) = 0`, `(b) = 764`, matching `classified.tsv`; 468 distinct deferred declarations. The scan records 446 lemma-list hits and 53 generated-equation references. This reproduces attribution of the supplied observations, not fresh seal executions. |
| Round-six-c control | Reviewed the 18-file previous-head control and its classifications | 26 touched hits at the previous head, absent from the supplied head classification. All unsealed control-file runs report success. |
| Hand-written controls | Counted examples and mapped each error location to its source example; compared sealed/unsealed example bodies | Round five: 39 positive examples, 27 negative examples and 27 errors. Rounds six/six-b: 47 positive examples, 30 negative examples and 30 errors. Every negative example has exactly one error; the unsealed versions have the same example bodies and no errors. Positive logs have no errors or sorry warnings. This coverage does not include F02's missing group. |

The three reported classification repairs are borne out by the scripts and source: trailing namespace/variable commands are excluded from declaration code; namespace-qualified names distinguish `PermCollection.OneWay.glPad` from `OneWay.glPad`; and proof-seal error attribution accounts for preceding docstrings. I checked the specifically disputed untouched declarations against the base. The two recorded DL proof failures remain in the deferred category, not silently treated as passes. Approved `PolyExpr.eval` and `glNeed` notation exceptions are respected.

The open negative-control file contains one deliberate `sorry` in the old `glHalf_f_even` example. Its role is to test elaboration of the old **signature**, so its unsealed pass is not being used as proof of the old equation. The equation is independently present in the original source. This does not invalidate that signature control.

## Shared statements, source fidelity, and fill interfaces

S1–S3 remain explicitly authorized, unproved shared statements. I found no mathematical counterexample:

- **S1:** coin lists are truncated or padded to the finite sampler's tape; emptiness distinguishes failure for positive lengths. The zero- and one-length fallback branches now have the correct numerals.
- **S2:** the two equal tape halves are independent. Each sampler contributes at most `(1/2)^n`, and excluding equal primes contributes at most `1 / card (Primes n) ≤ 2n / 2^n`. The stated sum follows; `n ≥ 2` supplies a nonempty distinct-prime domain.
- **S3:** `N ≠ 0` permits the unit domain, including `N = 1`. With `k = Nat.size N`, the acceptance probability is `Nat.totient N / 2^k ≥ 1/(2*k) ≥ 1/(4*n+8)`. There are `(4*n+8)*n` trials, giving the stated `exp(-n)` failure bound. At `n = 0` the bound is one; at `N = 1` the fallback is the unique residue zero. These observations are a mathematical review of the statement/sketch, not a filled Lean proof.

I compared the affected claims with the supplied book at pages 27, 41–42, 50–54, 78–81, 87–90, 92, 104, and 124–127. The transports preserve the intended one-way, hard-core, encryption, commitment, and ZK claims. In particular, the padded hard-core predicate is attached to the padded function, consistent with the proof of Theorem 87.3 despite the book's wording slip in its final clause. This PR does not turn the book's expected-time prime-sampling discussion into a claimed exact bounded-time uniform sampler: the shared statements expose their finite-tape errors. Previously documented encoding/parameter conventions remain in place.

| Required fill interface | Audited declaration | Fit |
|---|---|---|
| 3-colouring message lookup | `ThreeColoring/Protocol.lean:106`, `msgAt_eq` | Explicit arguments `(w, i)`; exactly `pairFstD (pairSndD^[i] w)`, as requested by col-b's frontier. |
| Arbitrary edge challenge | `ThreeColoring/Language.lean:347`, `edgeIdxOfMsg_eq` | Explicit `(m, w)`; exactly `w.length % m`, including arbitrary replies. |
| Factoring/Yao reduction | `Asymptotic/OneWayYao.lean:553`, `OneWay.yaoB_apply` | Same padded output block, offset, input layout and coin argument as the requested helper. |
| Uniform advice | `Complexity/Randomized/PPT.lean:289`, `NUPPT.Uniform.advice_eq` | Gives `A.advice n = []` from `A.Uniform`, in the needed closure. |
| Product inverter | `Candidates/Factoring.lean:392`, `prodInverter_eq` | Explicit numerical product lengths and unchanged defaulting behavior, removing the frozen-body obstruction. |
| #195 expansion output | `Asymptotic/HardCore.lean:498`, `PRG.expand_G_stretch` | The index is typed by the actual expanded generator's stretch, matching the required consumer. |

The DL generator/domain transports also expose the requested candidate interfaces. This checks interface compatibility; it does not claim that the delivered fill patches, with all their landing edits, were integrated or replayed here.

## Replay and axiom record

The archived round-six, six-b and six-c replay logs contain respectively 70, 65 and 82 module rows **including Checks**, all `rc=0`, `errors=0`; the last corresponds to 81 downstream modules plus Checks. The recorded round-five replay and later missing-module completion were also reviewed. The round-six-c axiom log has 47 prints, no errors and no `sorryAx`; the earlier logs disclose the inherited dependencies and authorized S1–S3. The added source sorries are precisely those three shared statements. The inaccurate baseline wording is R2-03, not an unauthorized-axiom finding.

Closure requires discharging R2-01 with the promised consumer evidence. The two minors are local documentation/record corrections. The 764 deferred rows and the separately audited #195 work are not certified as fixed by this report.

**Notation:** `(a)` means a read attributed to an added or code-changed declaration; `(b)` means a read attributed to an unchanged declaration. `k` in the S3 discussion is `Nat.size N`; other identifiers are the existing Lean/book notation.
